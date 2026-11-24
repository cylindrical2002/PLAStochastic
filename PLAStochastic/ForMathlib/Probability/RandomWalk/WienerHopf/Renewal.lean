import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Markov

/-!
# Coefficient identities behind the Wiener–Hopf factorization

For a measurable set `A` with first entrance time `τ = firstEntry A` and a complex `z`:

* `integral_cexp_partialSum`: `E[e^{z S_n}] = φ(z)^n`.
* `stepTransform_pow_eq_survival_add`: decomposition at the first entrance,
  `φ(z)^n = E[e^{z S_n}; n < τ] + ∑_{k ≤ n} E[e^{z S_k}; τ = k] φ(z)^{n-k}`.
* `ladderTimeCoeff_eq`: for a half-line type set (`A + A ⊆ A` and `x ∈ A, y ∉ A → x - y ∈ A`),
  the `A`-ladder times renew at the first entrance:
  `d_n = [n = 0] + ∑_{k ≤ n} E[e^{z S_k}; τ = k] d_{n-k}`.
* `survivalCoeff_compl_eq_ladderTimeCoeff`: time reversal,
  `E[e^{z S_n}; n < τ_{Aᶜ}] = E[e^{z S_n}; S_n - S_j ∈ A ∀ j < n]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : Set ℝ}

/-! ### Prefix-determined events -/

theorem DependsOnPrefix.indicator {E : Type*} [Zero E] {k : ℕ} {s : Set (ℕ → ℝ)}
    {f : (ℕ → ℝ) → E} (hs : DependsOnPrefix k (fun ω => ω ∈ s)) (hf : DependsOnPrefix k f) :
    DependsOnPrefix k (s.indicator f) := by
  intro ω ω' h
  have h1 : (ω ∈ s) = (ω' ∈ s) := hs ω ω' h
  by_cases hω : ω ∈ s
  · have hω' : ω' ∈ s := h1 ▸ hω
    rw [indicator_of_mem hω, indicator_of_mem hω', hf ω ω' h]
  · have hω' : ω' ∉ s := h1 ▸ hω
    rw [indicator_of_notMem hω, indicator_of_notMem hω']

theorem dependsOnPrefix_firstEntry_eq (A : Set ℝ) (k : ℕ) :
    DependsOnPrefix k (fun ω => ω ∈ {ω | firstEntry A ω = k}) :=
  fun _ _ h => propext (firstEntry_eq_congr h)

theorem dependsOnPrefix_isLadderTime (A : Set ℝ) (k : ℕ) :
    DependsOnPrefix k (fun ω => ω ∈ {ω | IsLadderTime A k ω}) :=
  fun _ _ h => propext (isLadderTime_congr h)

theorem dependsOnPrefix_cexp_partialSum (z : ℂ) (k : ℕ) :
    DependsOnPrefix k (fun ω => cexp (z * partialSum k ω)) :=
  fun _ _ h => by dsimp only; rw [partialSum_congr h]

/-! ### Moments of the walk -/

theorem integrable_cexp_partialSum {z : ℂ} (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (n : ℕ) : Integrable (fun ω => cexp (z * partialSum n ω)) (pathLaw ρ) ∧
      ∫ ω, cexp (z * partialSum n ω) ∂pathLaw ρ = stepTransform ρ z ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (fun ω => cexp (z * partialSum (n + 1) ω)) =
        fun ω => cexp (z * partialSum n ω) * (fun ω' : ℕ → ℝ => cexp (z * ω' 0)) (shift n ω) := by
      funext ω
      simp [partialSum_succ, mul_add, Complex.exp_add]
    have hF : Measurable fun ω => cexp (z * partialSum n ω) := by fun_prop
    have hG : Measurable fun ω' : ℕ → ℝ => cexp (z * ω' 0) := by fun_prop
    have hGi : Integrable (fun ω' : ℕ → ℝ => cexp (z * ω' 0)) (pathLaw ρ) :=
      (measurePreserving_eval (ρ := ρ) 0).integrable_comp_of_integrable hz
    rw [hsplit]
    refine ⟨integrable_mul_shift hF (dependsOnPrefix_cexp_partialSum z n) hG ih.1 hGi, ?_⟩
    rw [integral_mul_shift hF (dependsOnPrefix_cexp_partialSum z n) hG, ih.2,
      integral_comp_eval 0 hz.aestronglyMeasurable, pow_succ]
    rfl

theorem integral_cexp_partialSum {z : ℂ} (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (n : ℕ) : ∫ ω, cexp (z * partialSum n ω) ∂pathLaw ρ = stepTransform ρ z ^ n :=
  (integrable_cexp_partialSum hz n).2

theorem integrable_exp_partialSum {c : ℝ} (hc : Integrable (fun y : ℝ => Real.exp (c * y)) ρ)
    (n : ℕ) : Integrable (fun ω => Real.exp (c * partialSum n ω)) (pathLaw ρ) ∧
      ∫ ω, Real.exp (c * partialSum n ω) ∂pathLaw ρ = (∫ y, Real.exp (c * y) ∂ρ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsplit : (fun ω => Real.exp (c * partialSum (n + 1) ω)) =
        fun ω => Real.exp (c * partialSum n ω) *
          (fun ω' : ℕ → ℝ => Real.exp (c * ω' 0)) (shift n ω) := by
      funext ω
      simp [partialSum_succ, mul_add, Real.exp_add]
    have hF : Measurable fun ω => Real.exp (c * partialSum n ω) := by fun_prop
    have hG : Measurable fun ω' : ℕ → ℝ => Real.exp (c * ω' 0) := by fun_prop
    have hFd : DependsOnPrefix n fun ω => Real.exp (c * partialSum n ω) :=
      fun _ _ h => by dsimp only; rw [partialSum_congr h]
    have hGi : Integrable (fun ω' : ℕ → ℝ => Real.exp (c * ω' 0)) (pathLaw ρ) :=
      (measurePreserving_eval (ρ := ρ) 0).integrable_comp_of_integrable hc
    rw [hsplit]
    refine ⟨integrable_mul_shift hF hFd hG ih.1 hGi, ?_⟩
    rw [integral_mul_shift hF hFd hG, ih.2, integral_comp_eval 0 hc.aestronglyMeasurable,
      pow_succ]

theorem norm_cexp_mul_ofReal (z : ℂ) (x : ℝ) : ‖cexp (z * x)‖ = Real.exp (z.re * x) := by
  rw [Complex.norm_exp]
  simp

omit [IsProbabilityMeasure ρ] in
theorem integrable_cexp_iff_exp_re {z : ℂ} :
    Integrable (fun y : ℝ => cexp (z * y)) ρ ↔
      Integrable (fun y : ℝ => Real.exp (z.re * y)) ρ := by
  rw [← integrable_norm_iff (by fun_prop)]
  simp_rw [norm_cexp_mul_ofReal]

/-! ### Decomposition at the first entrance -/

theorem indicator_firstEntry_eq_mul_shift {k n : ℕ} (hkn : k ≤ n) (z : ℂ) (ω : ℕ → ℝ) :
    {ω | firstEntry A ω = k}.indicator (fun ω => cexp (z * partialSum n ω)) ω =
      {ω | firstEntry A ω = k}.indicator (fun ω => cexp (z * partialSum k ω)) ω *
        cexp (z * partialSum (n - k) (shift k ω)) := by
  by_cases h : ω ∈ {ω | firstEntry A ω = k}
  · rw [indicator_of_mem h, indicator_of_mem h, ← Complex.exp_add, ← mul_add,
      ← Complex.ofReal_add, ← partialSum_add, Nat.add_sub_cancel' hkn]
  · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]

theorem integral_indicator_firstEntry_eq (hA : MeasurableSet A) {z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ) {k n : ℕ} (hkn : k ≤ n) :
    ∫ ω, {ω | firstEntry A ω = k}.indicator (fun ω => cexp (z * partialSum n ω)) ω
        ∂pathLaw ρ = entryCoeff ρ A z k * stepTransform ρ z ^ (n - k) := by
  simp_rw [indicator_firstEntry_eq_mul_shift hkn]
  have hF : Measurable ({ω | firstEntry A ω = k}.indicator fun ω => cexp (z * partialSum k ω)) :=
    (by fun_prop : Measurable fun ω => cexp (z * partialSum k ω)).indicator
      (measurableSet_firstEntry_eq hA k)
  have hFd := (dependsOnPrefix_firstEntry_eq A k).indicator (dependsOnPrefix_cexp_partialSum z k)
  have hG : Measurable fun ω => cexp (z * partialSum (n - k) ω) := by fun_prop
  rw [integral_mul_shift (G := fun ω => cexp (z * partialSum (n - k) ω)) hF hFd hG,
    integral_indicator (measurableSet_firstEntry_eq hA k), integral_cexp_partialSum hz]
  rfl

/-- Decomposition at the first entrance time into `A`:
`φ(z)^n = E[e^{z S_n}; n < τ] + ∑_{k ≤ n} E[e^{z S_k}; τ = k] φ(z)^{n-k}`. -/
theorem stepTransform_pow_eq_survival_add (hA : MeasurableSet A) {z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ) (n : ℕ) :
    stepTransform ρ z ^ n = survivalCoeff ρ A z n +
      ∑ k ∈ Finset.range (n + 1), entryCoeff ρ A z k * stepTransform ρ z ^ (n - k) := by
  set f : (ℕ → ℝ) → ℂ := fun ω => cexp (z * partialSum n ω) with hf
  have hfi : Integrable f (pathLaw ρ) := (integrable_cexp_partialSum hz n).1
  have hpt : ∀ ω, f ω = {ω | (n : ℕ∞) < firstEntry A ω}.indicator f ω +
      ∑ k ∈ Finset.range (n + 1), {ω | firstEntry A ω = k}.indicator f ω := by
    intro ω
    by_cases h : (n : ℕ∞) < firstEntry A ω
    · rw [indicator_of_mem (show ω ∈ {ω | (n : ℕ∞) < firstEntry A ω} from h)]
      rw [Finset.sum_eq_zero, add_zero]
      intro k hk
      refine indicator_of_notMem ?_ _
      intro hk'
      simp only [mem_ofPred_eq] at hk'
      rw [hk', Nat.cast_lt] at h
      exact absurd (Finset.mem_range.mp hk) (by omega)
    · rw [indicator_of_notMem (show ω ∉ {ω | (n : ℕ∞) < firstEntry A ω} from h), zero_add]
      have hlt : firstEntry A ω < ⊤ := lt_of_le_of_lt (not_lt.mp h) (ENat.natCast_lt_top n)
      obtain ⟨k₀, hk₀⟩ := firstEntry_lt_top_iff.mp hlt
      have hk₀n : k₀ ≤ n := by
        have := not_lt.mp h
        rw [hk₀, Nat.cast_le] at this
        exact this
      rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_range.mpr (by omega))]
      · rw [indicator_of_mem (show ω ∈ {ω | firstEntry A ω = k₀} from hk₀)]
      · intro k _ hk
        refine indicator_of_notMem ?_ _
        intro hk'
        simp only [mem_ofPred_eq] at hk'
        rw [hk₀, Nat.cast_inj] at hk'
        exact hk hk'.symm
  have hint : ∫ ω, f ω ∂pathLaw ρ = ∫ ω, ({ω | (n : ℕ∞) < firstEntry A ω}.indicator f ω +
      ∑ k ∈ Finset.range (n + 1), {ω | firstEntry A ω = k}.indicator f ω) ∂pathLaw ρ :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [← integral_cexp_partialSum hz n, hint, integral_add
    (hfi.indicator (measurableSet_coe_lt_firstEntry hA n))
    (integrable_finsetSum _ fun k _ => hfi.indicator (measurableSet_firstEntry_eq hA k)),
    integral_finsetSum _ fun k _ => hfi.indicator (measurableSet_firstEntry_eq hA k),
    integral_indicator (measurableSet_coe_lt_firstEntry hA n)]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  exact integral_indicator_firstEntry_eq hA hz (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-! ### Renewal of ladder times -/

/-- A half-line type set: closed under addition, and `x ∈ A`, `y ∉ A` give `x - y ∈ A`.
The four half-lines `Ioi 0`, `Ici 0`, `Iio 0`, `Iic 0` are the examples. -/
structure IsLadderSet (A : Set ℝ) : Prop where
  add_mem : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A
  sub_mem : ∀ x ∈ A, ∀ y ∉ A, x - y ∈ A

theorem isLadderSet_Iic : IsLadderSet (Iic (0 : ℝ)) :=
  ⟨fun x hx y hy => by simp only [mem_Iic] at *; linarith,
    fun x hx y hy => by simp only [mem_Iic, not_le] at *; linarith⟩

theorem isLadderSet_Ioi : IsLadderSet (Ioi (0 : ℝ)) :=
  ⟨fun x hx y hy => by simp only [mem_Ioi] at *; linarith,
    fun x hx y hy => by simp only [mem_Ioi, not_lt] at *; linarith⟩

theorem isLadderSet_Iio : IsLadderSet (Iio (0 : ℝ)) :=
  ⟨fun x hx y hy => by simp only [mem_Iio] at *; linarith,
    fun x hx y hy => by simp only [mem_Iio, not_lt] at *; linarith⟩

theorem isLadderSet_Ici : IsLadderSet (Ici (0 : ℝ)) :=
  ⟨fun x hx y hy => by simp only [mem_Ici] at *; linarith,
    fun x hx y hy => by simp only [mem_Ici, not_le] at *; linarith⟩

theorem partialSum_shift (k m : ℕ) (ω : ℕ → ℝ) :
    partialSum m (shift k ω) = partialSum (k + m) ω - partialSum k ω := by
  rw [partialSum_add]; ring

/-- On `{τ = k}`, `n ≥ k` is an `A`-ladder time iff `n - k` is one for the shifted path. -/
theorem isLadderTime_iff_shift (hA : IsLadderSet A) {ω : ℕ → ℝ} {k n : ℕ}
    (hk : firstEntry A ω = k) (hkn : k ≤ n) :
    IsLadderTime A n ω ↔ IsLadderTime A (n - k) (shift k ω) := by
  obtain ⟨hk0, hkA, hbefore⟩ := firstEntry_eq_coe_iff.mp hk
  have hsh : ∀ j, partialSum (n - k) (shift k ω) - partialSum j (shift k ω) =
      partialSum n ω - partialSum (k + j) ω := by
    intro j
    rw [partialSum_shift, partialSum_shift, Nat.add_sub_cancel' hkn]
    ring
  constructor
  · intro h j hj
    rw [hsh]
    exact h (k + j) (by omega)
  · intro h j hj
    -- `S_k - S_j ∈ A` for `j < k`
    have hkj : ∀ j < k, partialSum k ω - partialSum j ω ∈ A := by
      intro j hj
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · simpa using hkA
      · exact hA.sub_mem _ hkA _ (hbefore j hjpos hj)
    by_cases hjk : k ≤ j
    · have := h (j - k) (by omega)
      rwa [hsh, Nat.add_sub_cancel' hjk] at this
    · replace hjk := Nat.lt_of_not_le hjk
      rcases Nat.eq_or_lt_of_le hkn with rfl | hlt
      · exact hkj j hjk
      · have h0 := h 0 (by omega)
        rw [hsh, add_zero] at h0
        have := hA.add_mem _ h0 _ (hkj j hjk)
        rwa [show partialSum n ω - partialSum k ω + (partialSum k ω - partialSum j ω) =
          partialSum n ω - partialSum j ω by ring] at this

/-- A positive `A`-ladder time is at least the first entrance time into `A`. -/
theorem firstEntry_le_of_isLadderTime {ω : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (h : IsLadderTime A n ω) : firstEntry A ω ≤ n := by
  refine not_lt.mp fun hlt => ?_
  have h0 := h 0 hn
  simp only [partialSum_zero, sub_zero] at h0
  exact coe_lt_firstEntry_iff.mp hlt n hn le_rfl h0

theorem isLadderTime_zero (A : Set ℝ) (ω : ℕ → ℝ) : IsLadderTime A 0 ω :=
  fun _ hj => absurd hj (Nat.not_lt_zero _)

theorem entryCoeff_zero (ρ : Measure ℝ) (A : Set ℝ) (z : ℂ) : entryCoeff ρ A z 0 = 0 := by
  have h : {ω | firstEntry A ω = ((0 : ℕ) : ℕ∞)} = ∅ := by
    ext ω
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
    intro h0
    exact (lt_irrefl 0) (firstEntry_eq_coe_iff.mp h0).1
  simp only [entryCoeff, h, Measure.restrict_empty, integral_zero_measure]

theorem ladderTimeCoeff_zero (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (A : Set ℝ) (z : ℂ) :
    ladderTimeCoeff ρ A z 0 = 1 := by
  have h : {ω | IsLadderTime A 0 ω} = univ := eq_univ_of_forall (isLadderTime_zero A)
  simp [ladderTimeCoeff, h]

theorem indicator_isLadderTime_eq_sum (hA : IsLadderSet A) (z : ℂ) {n : ℕ} (hn : 0 < n)
    (ω : ℕ → ℝ) :
    {ω | IsLadderTime A n ω}.indicator (fun ω => cexp (z * partialSum n ω)) ω =
      ∑ k ∈ Finset.range (n + 1),
        {ω | firstEntry A ω = k}.indicator (fun ω => cexp (z * partialSum k ω)) ω *
          {ω | IsLadderTime A (n - k) ω}.indicator
            (fun ω => cexp (z * partialSum (n - k) ω)) (shift k ω) := by
  by_cases hL : IsLadderTime A n ω
  · rw [indicator_of_mem (show ω ∈ {ω | IsLadderTime A n ω} from hL)]
    have hle := firstEntry_le_of_isLadderTime hn hL
    obtain ⟨k₀, hk₀⟩ := firstEntry_lt_top_iff.mp (lt_of_le_of_lt hle (ENat.natCast_lt_top n))
    have hk₀n : k₀ ≤ n := by rw [hk₀, Nat.cast_le] at hle; exact hle
    rw [Finset.sum_eq_single_of_mem k₀ (Finset.mem_range.mpr (by omega))]
    · have hsh := (isLadderTime_iff_shift hA hk₀ hk₀n).mp hL
      rw [indicator_of_mem (show ω ∈ {ω | firstEntry A ω = k₀} from hk₀),
        indicator_of_mem (show shift k₀ ω ∈ {ω | IsLadderTime A (n - k₀) ω} from hsh),
        ← Complex.exp_add, ← mul_add, ← Complex.ofReal_add, ← partialSum_add,
        Nat.add_sub_cancel' hk₀n]
    · intro k _ hk
      rw [indicator_of_notMem, zero_mul]
      intro hk'
      simp only [mem_ofPred_eq] at hk'
      rw [hk₀, Nat.cast_inj] at hk'
      exact hk hk'.symm
  · rw [indicator_of_notMem (show ω ∉ {ω | IsLadderTime A n ω} from hL)]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    by_cases hτ : firstEntry A ω = k
    · have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hsh : shift k ω ∉ {ω | IsLadderTime A (n - k) ω} := fun h =>
        hL ((isLadderTime_iff_shift hA hτ hkn).mpr h)
      rw [indicator_of_notMem hsh, mul_zero]
    · rw [indicator_of_notMem (show ω ∉ {ω | firstEntry A ω = k} from hτ), zero_mul]

/-- Renewal of `A`-ladder times at the first entrance into `A`:
`d_n = [n = 0] + ∑_{k ≤ n} E[e^{z S_k}; τ = k] d_{n-k}`. The integrability hypotheses hold
when `e^{z ·}` is `ρ`-integrable or when `Re z · x ≤ 0` on `A`. -/
theorem ladderTimeCoeff_eq (hAm : MeasurableSet A) (hA : IsLadderSet A) {z : ℂ}
    (hF : ∀ k : ℕ, Integrable
      ({ω | firstEntry A ω = k}.indicator fun ω => cexp (z * partialSum k ω)) (pathLaw ρ))
    (hG : ∀ m, Integrable
      ({ω | IsLadderTime A m ω}.indicator fun ω => cexp (z * partialSum m ω)) (pathLaw ρ))
    (n : ℕ) :
    ladderTimeCoeff ρ A z n = (if n = 0 then 1 else 0) +
      ∑ k ∈ Finset.range (n + 1), entryCoeff ρ A z k * ladderTimeCoeff ρ A z (n - k) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ladderTimeCoeff_zero, entryCoeff_zero]
  rw [if_neg hn.ne', zero_add, ladderTimeCoeff, ← integral_indicator
    (measurableSet_isLadderTime hAm n)]
  simp_rw [indicator_isLadderTime_eq_sum hA z hn]
  have hFm : ∀ k : ℕ, Measurable
      ({ω | firstEntry A ω = k}.indicator fun ω => cexp (z * partialSum k ω)) := fun k =>
    (by fun_prop : Measurable fun ω => cexp (z * partialSum k ω)).indicator
      (measurableSet_firstEntry_eq hAm k)
  have hGm : ∀ m, Measurable
      ({ω | IsLadderTime A m ω}.indicator fun ω => cexp (z * partialSum m ω)) := fun m =>
    (by fun_prop : Measurable fun ω => cexp (z * partialSum m ω)).indicator
      (measurableSet_isLadderTime hAm m)
  have hFd : ∀ k : ℕ, DependsOnPrefix k
      ({ω | firstEntry A ω = k}.indicator fun ω => cexp (z * partialSum k ω)) := fun k =>
    (dependsOnPrefix_firstEntry_eq A k).indicator (dependsOnPrefix_cexp_partialSum z k)
  rw [integral_finsetSum _ fun k _ =>
    integrable_mul_shift (hFm k) (hFd k) (hGm (n - k)) (hF k) (hG (n - k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_mul_shift (hFm k) (hFd k) (hGm (n - k)),
    integral_indicator (measurableSet_firstEntry_eq hAm k),
    integral_indicator (measurableSet_isLadderTime hAm (n - k))]
  rfl

/-! ### Time reversal -/

theorem coe_lt_firstEntry_compl_reverse_iff {n : ℕ} (ω : ℕ → ℝ) :
    (n : ℕ∞) < firstEntry Aᶜ (reverse n ω) ↔ IsLadderTime A n ω := by
  rw [coe_lt_firstEntry_iff]
  constructor
  · intro h i hi
    have := h (n - i) (by omega) (by omega)
    rw [partialSum_reverse (by omega), Nat.sub_sub_self hi.le] at this
    simpa using this
  · intro h j hj hjn
    rw [partialSum_reverse hjn]
    simpa using h (n - j) (by omega)

/-- Time reversal: `E[e^{z S_n}; n < τ_{Aᶜ}] = E[e^{z S_n}; S_n - S_j ∈ A ∀ j < n]`. -/
theorem survivalCoeff_compl_eq_ladderTimeCoeff (hAm : MeasurableSet A) (z : ℂ) (n : ℕ) :
    survivalCoeff ρ Aᶜ z n = ladderTimeCoeff ρ A z n := by
  set H : (ℕ → ℝ) → ℂ :=
    {ω | (n : ℕ∞) < firstEntry Aᶜ ω}.indicator fun ω => cexp (z * partialSum n ω) with hH
  have hHm : Measurable H :=
    (by fun_prop : Measurable fun ω => cexp (z * partialSum n ω)).indicator
      (measurableSet_coe_lt_firstEntry hAm.compl n)
  have hpt : ∀ ω, {ω | IsLadderTime A n ω}.indicator (fun ω => cexp (z * partialSum n ω)) ω =
      H (reverse n ω) := by
    intro ω
    have hS : partialSum n (reverse n ω) = partialSum n ω := by
      rw [partialSum_reverse le_rfl, Nat.sub_self, partialSum_zero, sub_zero]
    by_cases h : IsLadderTime A n ω
    · rw [indicator_of_mem (show ω ∈ {ω | IsLadderTime A n ω} from h), hH,
        indicator_of_mem (show reverse n ω ∈ {ω | (n : ℕ∞) < firstEntry Aᶜ ω} from
          (coe_lt_firstEntry_compl_reverse_iff ω).mpr h), hS]
    · rw [indicator_of_notMem (show ω ∉ {ω | IsLadderTime A n ω} from h), hH,
        indicator_of_notMem (show reverse n ω ∉ {ω | (n : ℕ∞) < firstEntry Aᶜ ω} from
          fun h' => h ((coe_lt_firstEntry_compl_reverse_iff ω).mp h'))]
  rw [survivalCoeff, ladderTimeCoeff, ← integral_indicator (measurableSet_isLadderTime hAm n),
    ← integral_indicator (measurableSet_coe_lt_firstEntry hAm.compl n)]
  simp_rw [hpt]
  exact (integral_comp_reverse n hHm.aestronglyMeasurable).symm

end PGM.WienerHopf
