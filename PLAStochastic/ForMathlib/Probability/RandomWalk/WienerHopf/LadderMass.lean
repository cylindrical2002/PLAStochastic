import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Series

/-!
# Exponential masses of ladder heights

For a half-line type set `A` with dual first entrance `τ_{Aᶜ}` and a real `θ` with `θ x ≤ 0` on
`A` (e.g. `A = Iic 0`, `θ ≥ 0`, so that `τ_{Aᶜ} = τ₊`):

* `sum_survival_exp_le`: the pre-ladder occupation measure has exponential mass
  `∑_{n < N} E[e^{θ S_n}; n < τ_{Aᶜ}] ≤ (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`;
* `expEntryMass_compl_le`: the ladder height `S_{τ_{Aᶜ}}` has the exponential moment
  `E[e^{θ S_{τ_{Aᶜ}}}; τ_{Aᶜ} < ∞] ≤ (∫ e^{θ y} dρ) (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`;
* `expEntryMass_le_one_sub`: `1 - E[e^{θ S_{τ_A}}; τ_A < ∞] ≥ ∫_A (1 - e^{θ y}) dρ(y)`.

With `A = Iic 0`: `E[e^{θ H₊}; τ₊ < ∞] ≤ E e^{θ Y} / (1 - E[e^{θ H₋}; τ₋ < ∞])`, and the
denominator is at least `(1 - e^{-θ b}) ρ(-∞, -b]`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : Set ℝ}

/-- `E[e^{θ S_τ}; τ < ∞]` for the first entrance time `τ` into `A` (real `θ`, `s = 1`). -/
def expEntryMass (ρ : Measure ℝ) (A : Set ℝ) (θ : ℝ) : ℝ :=
  ∫ ω in {ω | firstEntry A ω < ⊤}, Real.exp (θ * entryValue A ω) ∂pathLaw ρ

omit [IsProbabilityMeasure ρ] in
theorem ofReal_setIntegral_exp (E : Set (ℕ → ℝ)) (θ : ℝ) (n : ℕ) :
    ((∫ ω in E, Real.exp (θ * partialSum n ω) ∂pathLaw ρ : ℝ) : ℂ) =
      ∫ ω in E, cexp ((θ : ℂ) * partialSum n ω) ∂pathLaw ρ := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Complex.ofReal_exp, Complex.ofReal_mul]

omit [IsProbabilityMeasure ρ] in
theorem ofReal_expEntryMass (A : Set ℝ) (θ : ℝ) :
    ((expEntryMass ρ A θ : ℝ) : ℂ) = entryTransform ρ A 1 θ := by
  rw [expEntryMass, entryTransform, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [one_pow, one_mul, Complex.ofReal_exp, Complex.ofReal_mul]

theorem integrableOn_ladderTime_of_bounded (hAm : MeasurableSet A) {z : ℂ}
    (hzA : ∀ x ∈ A, z.re * x ≤ 0) (m : ℕ) :
    IntegrableOn (fun ω => cexp (z * partialSum m ω)) {ω | IsLadderTime A m ω} (pathLaw ρ) := by
  refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
    (by fun_prop : Measurable fun ω => cexp (z * partialSum m ω)).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_isLadderTime hAm m)).mpr
      (Filter.Eventually.of_forall fun ω hω => ?_))
  rw [norm_cexp_mul_ofReal, Real.exp_le_one_iff]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have := hω 0 hm
    simp only [partialSum_zero, sub_zero] at this
    exact hzA _ this

/-! ### A renewal inequality for nonnegative sequences -/

/-- If `d_n = [n = 0] + ∑_{k ≤ n} f_k d_{n-k}` with `f, d ≥ 0` and `∑ f ≤ F < 1`, then
`∑_{n < N} d_n ≤ (1 - F)⁻¹`. -/
theorem sum_range_le_of_renewal {f d : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hd0 : ∀ n, 0 ≤ d n)
    {F : ℝ} (hF : ∀ N, ∑ k ∈ range N, f k ≤ F) (hF1 : F < 1)
    (hren : ∀ n, d n = (if n = 0 then 1 else 0) + ∑ k ∈ range (n + 1), f k * d (n - k))
    (N : ℕ) : ∑ n ∈ range N, d n ≤ (1 - F)⁻¹ := by
  have hpos : 0 < 1 - F := by linarith
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [hpos.le]
  have hsplit : ∑ n ∈ range N, d n = 1 +
      ∑ m ∈ range N, ∑ k ∈ range (N - m), f m * d k := by
    rw [Finset.sum_congr rfl fun n _ => hren n, Finset.sum_add_distrib,
      Finset.sum_range_diag_flip N fun m k => f m * d k]
    congr 1
    rw [Finset.sum_ite_eq' (range N) 0 (fun _ => (1 : ℝ)), if_pos (Finset.mem_range.mpr hN)]
  have hle : ∑ m ∈ range N, ∑ k ∈ range (N - m), f m * d k ≤
      F * ∑ n ∈ range N, d n := by
    calc ∑ m ∈ range N, ∑ k ∈ range (N - m), f m * d k
        ≤ ∑ m ∈ range N, f m * ∑ n ∈ range N, d n := by
          refine Finset.sum_le_sum fun m _ => ?_
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.sub_le N m)) fun i _ _ => hd0 i) (hf0 m)
      _ = (∑ m ∈ range N, f m) * ∑ n ∈ range N, d n := by rw [Finset.sum_mul]
      _ ≤ F * ∑ n ∈ range N, d n :=
          mul_le_mul_of_nonneg_right (hF N) (Finset.sum_nonneg fun i _ => hd0 i)
  rw [← one_div, le_div_iff₀ hpos]
  nlinarith

/-! ### The occupation mass before the dual ladder epoch -/

theorem expEntryMass_eq_tsum (hAm : MeasurableSet A) {θ : ℝ} (hθ : ∀ x ∈ A, θ * x ≤ 0) :
    Summable (fun n : ℕ => ∫ ω in {ω | firstEntry A ω = n},
      Real.exp (θ * partialSum n ω) ∂pathLaw ρ) ∧
    expEntryMass ρ A θ = ∑' n : ℕ, ∫ ω in {ω | firstEntry A ω = n},
      Real.exp (θ * partialSum n ω) ∂pathLaw ρ := by
  have hzA : ∀ x ∈ A, ((θ : ℂ)).re * x ≤ 0 := by simpa using hθ
  have hsum := summable_entry_of_bounded (ρ := ρ) hAm (s := 1) (by simp) hzA
  simp only [norm_one, one_pow, one_mul, norm_cexp_mul_ofReal, Complex.ofReal_re] at hsum
  refine ⟨hsum, ?_⟩
  apply Complex.ofReal_injective
  rw [ofReal_expEntryMass, entryTransform_eq_tsum_of_bounded hAm (by simp) hzA,
    Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [one_pow, one_mul, entryCoeff, ofReal_setIntegral_exp]

/-- The pre-ladder occupation measure has exponential mass at most
`(1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`:
`∑_{n < N} E[e^{θ S_n}; n < τ_{Aᶜ}] ≤ (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`. -/
theorem sum_survival_exp_le (hAm : MeasurableSet A) (hA : IsLadderSet A) {θ : ℝ}
    (hθ : ∀ x ∈ A, θ * x ≤ 0) (hF : expEntryMass ρ A θ < 1) (N : ℕ) :
    ∑ n ∈ range N, ∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
      Real.exp (θ * partialSum n ω) ∂pathLaw ρ ≤ (1 - expEntryMass ρ A θ)⁻¹ := by
  have hzA : ∀ x ∈ A, ((θ : ℂ)).re * x ≤ 0 := by simpa using hθ
  set f : ℕ → ℝ := fun k => ∫ ω in {ω | firstEntry A ω = k},
    Real.exp (θ * partialSum k ω) ∂pathLaw ρ
  set d : ℕ → ℝ := fun m => ∫ ω in {ω | (m : ℕ∞) < firstEntry Aᶜ ω},
    Real.exp (θ * partialSum m ω) ∂pathLaw ρ
  have hdL : ∀ m, ((d m : ℝ) : ℂ) = ladderTimeCoeff ρ A θ m := fun m => by
    rw [ofReal_setIntegral_exp, ← survivalCoeff_compl_eq_ladderTimeCoeff hAm]
    rfl
  have hfE : ∀ k, ((f k : ℝ) : ℂ) = entryCoeff ρ A θ k := fun k => by
    rw [ofReal_setIntegral_exp]
    rfl
  have hren : ∀ n, d n = (if n = 0 then 1 else 0) +
      ∑ k ∈ range (n + 1), f k * d (n - k) := by
    intro n
    apply Complex.ofReal_injective
    push_cast
    rw [hdL]
    simp_rw [hfE, hdL]
    have h := ladderTimeCoeff_eq (ρ := ρ) (z := (θ : ℂ)) hAm hA
      (fun k => (integrableOn_entry_of_bounded hAm hzA k).integrable_indicator
        (measurableSet_firstEntry_eq hAm k))
      (fun m => (integrableOn_ladderTime_of_bounded hAm hzA m).integrable_indicator
        (measurableSet_isLadderTime hAm m)) n
    rw [h]
    split_ifs <;> simp
  obtain ⟨hfs, hfeq⟩ := expEntryMass_eq_tsum (ρ := ρ) hAm hθ
  have hf0 : ∀ k, 0 ≤ f k := fun k => integral_nonneg fun _ => (Real.exp_pos _).le
  have hd0 : ∀ n, 0 ≤ d n := fun n => integral_nonneg fun _ => (Real.exp_pos _).le
  refine sum_range_le_of_renewal hf0 hd0 (F := expEntryMass ρ A θ) (fun N => ?_) hF hren N
  rw [hfeq]
  exact hfs.sum_le_tsum _ fun k _ => hf0 k

/-! ### Exponential moments of the ladder height -/

theorem setIntegral_firstEntry_succ_le (hAm : MeasurableSet A) {θ : ℝ}
    (hM : Integrable (fun y : ℝ => Real.exp (θ * y)) ρ) (n : ℕ) :
    ∫ ω in {ω | firstEntry A ω = ((n + 1 : ℕ) : ℕ∞)},
        Real.exp (θ * partialSum (n + 1) ω) ∂pathLaw ρ ≤
      (∫ ω in {ω | (n : ℕ∞) < firstEntry A ω}, Real.exp (θ * partialSum n ω) ∂pathLaw ρ) *
        ∫ y, Real.exp (θ * y) ∂ρ := by
  set F : (ℕ → ℝ) → ℝ := {ω | (n : ℕ∞) < firstEntry A ω}.indicator
    fun ω => Real.exp (θ * partialSum n ω)
  set G : (ℕ → ℝ) → ℝ := fun ω => Real.exp (θ * ω 0)
  have hFm : Measurable F := (by fun_prop : Measurable fun ω => Real.exp (θ * partialSum n ω)).indicator
    (measurableSet_coe_lt_firstEntry hAm n)
  have hGm : Measurable G := by fun_prop
  have hFd : DependsOnPrefix n F := by
    refine DependsOnPrefix.indicator (fun ω ω' h => propext (coe_lt_firstEntry_congr h)) ?_
    exact fun _ _ h => by simp only [partialSum_congr h]
  have hFi : Integrable F (pathLaw ρ) :=
    (integrable_exp_partialSum hM n).1.indicator (measurableSet_coe_lt_firstEntry hAm n)
  have hGi : Integrable G (pathLaw ρ) :=
    (measurePreserving_eval (ρ := ρ) 0).integrable_comp_of_integrable hM
  have hprod := integral_mul_shift (ρ := ρ) hFm hFd hGm
  have hpt : ∀ ω, {ω | firstEntry A ω = ((n + 1 : ℕ) : ℕ∞)}.indicator
      (fun ω => Real.exp (θ * partialSum (n + 1) ω)) ω ≤ F ω * G (shift n ω) := by
    intro ω
    by_cases h : firstEntry A ω = ((n + 1 : ℕ) : ℕ∞)
    · have hlt : (n : ℕ∞) < firstEntry A ω := by rw [h]; exact_mod_cast Nat.lt_succ_self n
      have hmem : ω ∈ {ω | (n : ℕ∞) < firstEntry A ω} := hlt
      rw [indicator_of_mem (show ω ∈ {ω | firstEntry A ω = ((n + 1 : ℕ) : ℕ∞)} from h)]
      simp only [F, G, indicator_of_mem hmem, shift_apply, add_zero, partialSum_succ, mul_add,
        Real.exp_add, le_refl]
    · rw [indicator_of_notMem (show ω ∉ {ω | firstEntry A ω = ((n + 1 : ℕ) : ℕ∞)} from h)]
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
        (Real.exp_pos _).le
  rw [← integral_indicator (measurableSet_firstEntry_eq hAm (n + 1)),
    ← integral_indicator (measurableSet_coe_lt_firstEntry hAm n)]
  have hi := integral_comp_eval (ρ := ρ) 0 hM.aestronglyMeasurable
  calc _ ≤ ∫ ω, F ω * G (shift n ω) ∂pathLaw ρ :=
        integral_mono ((integrable_exp_partialSum hM (n + 1)).1.indicator
          (measurableSet_firstEntry_eq hAm (n + 1)))
          (integrable_mul_shift hFm hFd hGm hFi hGi) hpt
    _ = _ := by rw [hprod, hi]

/-- Ladder heights inherit exponential moments: if `θ x ≤ 0` on `A` and
`E[e^{θ S_{τ_A}}; τ_A < ∞] < 1`, then the ascending-type ladder height `S_{τ_{Aᶜ}}` satisfies
`E[e^{θ S_{τ_{Aᶜ}}}; τ_{Aᶜ} < ∞] ≤ (∫ e^{θ y} dρ) (1 - E[e^{θ S_{τ_A}}; τ_A < ∞])⁻¹`, together with
the summability of the series `∑ E[e^{θ S_n}; τ_{Aᶜ} = n]`. -/
theorem expEntryMass_compl_le (hAm : MeasurableSet A) (hA : IsLadderSet A) {θ : ℝ}
    (hθ : ∀ x ∈ A, θ * x ≤ 0) (hF : expEntryMass ρ A θ < 1)
    (hM : Integrable (fun y : ℝ => Real.exp (θ * y)) ρ) :
    Summable (fun n : ℕ => ∫ ω in {ω | firstEntry Aᶜ ω = n},
      Real.exp (θ * partialSum n ω) ∂pathLaw ρ) ∧
    IntegrableOn (fun ω => Real.exp (θ * entryValue Aᶜ ω)) {ω | firstEntry Aᶜ ω < ⊤}
      (pathLaw ρ) ∧
    expEntryMass ρ Aᶜ θ ≤ (∫ y, Real.exp (θ * y) ∂ρ) * (1 - expEntryMass ρ A θ)⁻¹ := by
  set e : ℕ → ℝ := fun n => ∫ ω in {ω | firstEntry Aᶜ ω = n},
    Real.exp (θ * partialSum n ω) ∂pathLaw ρ
  set M := ∫ y, Real.exp (θ * y) ∂ρ
  have hM0 : 0 ≤ M := integral_nonneg fun _ => (Real.exp_pos _).le
  have he0 : ∀ n, 0 ≤ e n := fun n => integral_nonneg fun _ => (Real.exp_pos _).le
  have he_zero : e 0 = 0 := by
    have h : {ω | firstEntry Aᶜ ω = ((0 : ℕ) : ℕ∞)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h0
      exact (lt_irrefl 0) (firstEntry_eq_coe_iff.mp h0).1
    simp only [e, h, Measure.restrict_empty, integral_zero_measure]
  have hpart : ∀ N, ∑ n ∈ range N, e n ≤ M * (1 - expEntryMass ρ A θ)⁻¹ := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact mul_nonneg hM0 (inv_nonneg.mpr (by linarith))
    obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_lt hN
    rw [zero_add, Finset.sum_range_succ', he_zero, add_zero]
    calc ∑ n ∈ range N, e (n + 1)
        ≤ ∑ n ∈ range N, (∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
            Real.exp (θ * partialSum n ω) ∂pathLaw ρ) * M :=
          Finset.sum_le_sum fun n _ => setIntegral_firstEntry_succ_le hAm.compl hM n
      _ = M * ∑ n ∈ range N, ∫ ω in {ω | (n : ℕ∞) < firstEntry Aᶜ ω},
            Real.exp (θ * partialSum n ω) ∂pathLaw ρ := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => mul_comm _ _
      _ ≤ M * (1 - expEntryMass ρ A θ)⁻¹ :=
          mul_le_mul_of_nonneg_left (sum_survival_exp_le hAm hA hθ hF N) hM0
  have hsum : Summable e := summable_of_sum_range_le he0 hpart
  have hint : ∀ n : ℕ, IntegrableOn (fun ω => Real.exp (θ * entryValue Aᶜ ω))
      {ω | firstEntry Aᶜ ω = n} (pathLaw ρ) := by
    intro n
    refine IntegrableOn.congr_fun ((integrable_exp_partialSum hM n).1.integrableOn) ?_
      (measurableSet_firstEntry_eq hAm.compl n)
    intro ω hω
    simp only [mem_ofPred_eq] at hω
    simp only [entryValue_of_eq hω]
  have hnorm : ∀ n : ℕ, ∫ ω in {ω | firstEntry Aᶜ ω = n},
      ‖Real.exp (θ * entryValue Aᶜ ω)‖ ∂pathLaw ρ = e n := by
    intro n
    refine setIntegral_congr_fun (measurableSet_firstEntry_eq hAm.compl n) fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, entryValue_of_eq hω]
  have hU : IntegrableOn (fun ω => Real.exp (θ * entryValue Aᶜ ω))
      (⋃ n : ℕ, {ω | firstEntry Aᶜ ω = n}) (pathLaw ρ) :=
    integrableOn_iUnion_of_summable_integral_norm hint (by simp_rw [hnorm]; exact hsum)
  have hval : expEntryMass ρ Aᶜ θ = ∑' n, e n := by
    rw [expEntryMass, setOf_firstEntry_lt_top_eq_iUnion,
      integral_iUnion (fun n => measurableSet_firstEntry_eq hAm.compl n)
        (pairwise_disjoint_firstEntry_eq Aᶜ) hU]
    refine tsum_congr fun n => setIntegral_congr_fun
      (measurableSet_firstEntry_eq hAm.compl n) fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω
    rw [entryValue_of_eq hω]
  refine ⟨hsum, by rwa [setOf_firstEntry_lt_top_eq_iUnion], ?_⟩
  rw [hval]
  exact Real.tsum_le_of_sum_range_le he0 hpart

/-! ### The gap `1 - E[e^{θ S_{τ_A}}; τ_A < ∞]` -/

/-- `E[e^{θ S_{τ_A}}; τ_A < ∞] ≤ 1 - ∫_A (1 - e^{θ y}) dρ(y)` when `θ x ≤ 0` on `A`: the first
step alone already enters `A`. -/
theorem expEntryMass_le_one_sub (hAm : MeasurableSet A) {θ : ℝ} (hθ : ∀ x ∈ A, θ * x ≤ 0) :
    expEntryMass ρ A θ ≤ 1 - ∫ y in A, (1 - Real.exp (θ * y)) ∂ρ := by
  set h : ℝ → ℝ := A.indicator fun y => 1 - Real.exp (θ * y)
  have hh0 : ∀ y, 0 ≤ h y := by
    intro y
    by_cases hy : y ∈ A
    · simp only [h, indicator_of_mem hy, sub_nonneg, Real.exp_le_one_iff]
      exact hθ y hy
    · simp [h, hy]
  have hh1 : ∀ y, h y ≤ 1 := by
    intro y
    by_cases hy : y ∈ A
    · simp only [h, indicator_of_mem hy]
      linarith [Real.exp_pos (θ * y)]
    · simp [h, hy]
  have hhm : Measurable h :=
    (by fun_prop : Measurable fun y : ℝ => 1 - Real.exp (θ * y)).indicator hAm
  have hhi : Integrable h ρ := Integrable.of_bound hhm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (hh0 y)]; exact hh1 y)
  have hpt : ∀ ω ∈ {ω | firstEntry A ω < ⊤},
      Real.exp (θ * entryValue A ω) ≤ 1 - h (ω 0) := by
    intro ω hω
    by_cases h0 : ω 0 ∈ A
    · have h1 : firstEntry A ω = ((1 : ℕ) : ℕ∞) := by
        rw [firstEntry_eq_coe_iff]
        refine ⟨Nat.one_pos, by simpa [partialSum] using h0, fun j hj hj1 => by omega⟩
      simp only [h, indicator_of_mem h0, sub_sub_cancel, entryValue_of_eq h1]
      simp [partialSum]
    · simp only [h, indicator_of_notMem h0, sub_zero, Real.exp_le_one_iff]
      exact hθ _ (entryValue_mem hω)
  have hmeas := measurableSet_firstEntry_lt_top hAm
  have hhi' : Integrable (fun ω : ℕ → ℝ => h (ω 0)) (pathLaw ρ) :=
    (measurePreserving_eval (ρ := ρ) 0).integrable_comp_of_integrable hhi
  have hint1 : IntegrableOn (fun ω => 1 - h (ω 0)) {ω | firstEntry A ω < ⊤} (pathLaw ρ) :=
    ((integrable_const 1).sub hhi').integrableOn
  have hint0 : IntegrableOn (fun ω => Real.exp (θ * entryValue A ω)) {ω | firstEntry A ω < ⊤}
      (pathLaw ρ) := by
    refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
      (Real.measurable_exp.comp ((measurable_entryValue hAm).const_mul θ)).aestronglyMeasurable
      ((ae_restrict_iff' hmeas).mpr (Filter.Eventually.of_forall fun ω hω => ?_))
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact hθ _ (entryValue_mem hω)
  calc expEntryMass ρ A θ ≤ ∫ ω in {ω | firstEntry A ω < ⊤}, (1 - h (ω 0)) ∂pathLaw ρ :=
        setIntegral_mono_on hint0 hint1 hmeas hpt
    _ ≤ ∫ ω, (1 - h (ω 0)) ∂pathLaw ρ :=
        setIntegral_le_integral ((integrable_const 1).sub hhi')
          (Filter.Eventually.of_forall fun ω => by simp only [Pi.zero_apply, sub_nonneg]; exact hh1 _)
    _ = 1 - ∫ y, h y ∂ρ := by
        rw [integral_sub (integrable_const 1) hhi', integral_const,
          integral_comp_eval 0 hhm.aestronglyMeasurable]
        simp
    _ = 1 - ∫ y in A, (1 - Real.exp (θ * y)) ∂ρ := by rw [integral_indicator hAm]

/-- A quantitative gap for the weak descending ladder: for `θ ≥ 0` and `b ≥ 0`,
`1 - E[e^{θ H₋}; τ₋ < ∞] ≥ (1 - e^{-θ b}) ρ(-∞, -b]`. -/
theorem one_sub_expEntryMass_Iic_ge {θ b : ℝ} (hθ : 0 ≤ θ) (hb : 0 ≤ b) :
    (1 - Real.exp (-(θ * b))) * ρ.real (Iic (-b)) ≤ 1 - expEntryMass ρ (Iic 0) θ := by
  have hθA : ∀ x ∈ Iic (0 : ℝ), θ * x ≤ 0 := fun x hx => mul_nonpos_of_nonneg_of_nonpos hθ hx
  have h := expEntryMass_le_one_sub (ρ := ρ) measurableSet_Iic hθA
  have hsub : Iic (-b) ⊆ Iic (0 : ℝ) := Iic_subset_Iic.mpr (by linarith)
  have hint : IntegrableOn (fun y : ℝ => 1 - Real.exp (θ * y)) (Iic 0) ρ := by
    refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _) (by fun_prop)
      ((ae_restrict_iff' measurableSet_Iic).mpr (Filter.Eventually.of_forall fun y hy => ?_))
    have h1 : Real.exp (θ * y) ≤ 1 := Real.exp_le_one_iff.mpr (hθA y hy)
    rw [Real.norm_of_nonneg (by linarith)]
    linarith [Real.exp_pos (θ * y)]
  have hnn : ∀ y ∈ Iic (0 : ℝ), 0 ≤ 1 - Real.exp (θ * y) := fun y hy => by
    have := Real.exp_le_one_iff.mpr (hθA y hy); linarith
  calc (1 - Real.exp (-(θ * b))) * ρ.real (Iic (-b))
      = ∫ y in Iic (-b), (1 - Real.exp (-(θ * b))) ∂ρ := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ y in Iic (-b), (1 - Real.exp (θ * y)) ∂ρ := by
        refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
          (hint.mono_set hsub) measurableSet_Iic fun y hy => ?_
        have : θ * y ≤ -(θ * b) := by
          have := mul_le_mul_of_nonneg_left (show y ≤ -b from hy) hθ; linarith
        linarith [Real.exp_le_exp.mpr this]
    _ ≤ ∫ y in Iic 0, (1 - Real.exp (θ * y)) ∂ρ :=
        setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Iic).mpr
          (Filter.Eventually.of_forall hnn)) (Filter.Eventually.of_forall hsub)
    _ ≤ 1 - expEntryMass ρ (Iic 0) θ := by linarith

/-- The dual gap for the strict ascending ladder: for `θ ≥ 0` and `b ≥ 0`,
`1 - E[e^{-θ H₊}; τ₊ < ∞] ≥ (1 - e^{-θ b}) ρ[b, ∞)` (for `b > 0`; with `Ioi 0` replaced by
`Ici b ⊆ Ioi 0`). -/
theorem one_sub_expEntryMass_Ioi_ge {θ b : ℝ} (hθ : 0 ≤ θ) (hb : 0 < b) :
    (1 - Real.exp (-(θ * b))) * ρ.real (Ici b) ≤ 1 - expEntryMass ρ (Ioi 0) (-θ) := by
  have hθA : ∀ x ∈ Ioi (0 : ℝ), -θ * x ≤ 0 := fun x hx => by
    have := mul_nonneg hθ (le_of_lt (show (0:ℝ) < x from hx)); linarith
  have h := expEntryMass_le_one_sub (ρ := ρ) measurableSet_Ioi hθA
  have hsub : Ici b ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le hb hy
  have hint : IntegrableOn (fun y : ℝ => 1 - Real.exp (-θ * y)) (Ioi 0) ρ := by
    refine Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _) (by fun_prop)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_))
    have h1 : Real.exp (-θ * y) ≤ 1 := Real.exp_le_one_iff.mpr (hθA y hy)
    rw [Real.norm_of_nonneg (by linarith)]
    linarith [Real.exp_pos (-θ * y)]
  have hnn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ 1 - Real.exp (-θ * y) := fun y hy => by
    have := Real.exp_le_one_iff.mpr (hθA y hy); linarith
  calc (1 - Real.exp (-(θ * b))) * ρ.real (Ici b)
      = ∫ y in Ici b, (1 - Real.exp (-(θ * b))) ∂ρ := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ y in Ici b, (1 - Real.exp (-θ * y)) ∂ρ := by
        refine setIntegral_mono_on (integrableOn_const (measure_ne_top _ _))
          (hint.mono_set hsub) measurableSet_Ici fun y hy => ?_
        have : -θ * y ≤ -(θ * b) := by
          have := mul_le_mul_of_nonneg_left (show b ≤ y from hy) hθ; linarith
        linarith [Real.exp_le_exp.mpr this]
    _ ≤ ∫ y in Ioi 0, (1 - Real.exp (-θ * y)) ∂ρ :=
        setIntegral_mono_set hint ((ae_restrict_iff' measurableSet_Ioi).mpr
          (Filter.Eventually.of_forall hnn)) (Filter.Eventually.of_forall hsub)
    _ ≤ 1 - expEntryMass ρ (Ioi 0) (-θ) := by linarith

end PGM.WienerHopf
