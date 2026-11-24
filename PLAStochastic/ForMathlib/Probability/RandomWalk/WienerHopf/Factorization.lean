import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Renewal

/-!
# The Wiener–Hopf factorization of an iid real random walk

For a half-line type set `A` (`IsLadderSet A`) with first entrance times `τ_A`, `τ_{Aᶜ}`:

* `entryTransform_eq_tsum`: `E[s^τ e^{z S_τ}; τ < ∞] = ∑ sⁿ E[e^{z S_n}; τ = n]`.
* `wienerHopf_of_isLadderSet`: if `e^{z y}` is `ρ`-integrable and
  `‖s‖ ∫ e^{Re z · y} dρ < 1`, then
  `1 - s φ(z) = (1 - E[s^{τ_{Aᶜ}} e^{z S}; τ_{Aᶜ} < ∞]) (1 - E[s^{τ_A} e^{z S}; τ_A < ∞])`,
  and `∑ sⁿ E[e^{z S_n}; n < τ_{Aᶜ}] (1 - E[s^{τ_A} e^{z S}; τ_A < ∞]) = 1`.
* `wienerHopf`: for `‖s‖ < 1` and `Re z = 0`,
  `1 - s φ(z) = (1 - χ₊(s, z)) (1 - χ₋(s, z))` with the strict ascending and weak descending
  ladders; `wienerHopf_weakAsc_strictDesc` is the dual factorization.

The hypothesis `‖s‖ ∫ e^{Re z · y} dρ < 1` covers `‖s‖ < 1, Re z = 0` and also real `s` up to
`1` on the part of a strip where the step transform is below one.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Finset
open scoped ENNReal

namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {A : Set ℝ}

/-! ### Generating-function algebra -/

/-- Cauchy products of generating functions: if `w = c + u ∗ v` coefficientwise, then
`W(s) = C(s) + U(s) V(s)` under absolute convergence. -/
theorem tsum_pow_mul_eq_add_mul {s : ℂ} {u v c w : ℕ → ℂ}
    (hu : Summable fun n => ‖s ^ n * u n‖) (hv : Summable fun n => ‖s ^ n * v n‖)
    (hc : Summable fun n => s ^ n * c n)
    (hw : ∀ n, w n = c n + ∑ k ∈ range (n + 1), u k * v (n - k)) :
    ∑' n, s ^ n * w n = ∑' n, s ^ n * c n + (∑' n, s ^ n * u n) * ∑' n, s ^ n * v n := by
  have hterm : ∀ n, s ^ n * w n = s ^ n * c n +
      ∑ k ∈ range (n + 1), (s ^ k * u k) * (s ^ (n - k) * v (n - k)) := by
    intro n
    rw [hw, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [show s ^ n = s ^ k * s ^ (n - k) by rw [← pow_add, Nat.add_sub_cancel' hkn]]
    ring
  simp_rw [hterm]
  rw [tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hu hv]
  exact hc.tsum_add (summable_norm_sum_mul_range_of_summable_norm hu hv).of_norm

/-! ### Coefficient bounds -/

theorem norm_setIntegral_cexp_partialSum_le {z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ) (E : Set (ℕ → ℝ)) (n : ℕ) :
    ‖∫ ω in E, cexp (z * partialSum n ω) ∂pathLaw ρ‖ ≤
      (∫ y, Real.exp (z.re * y) ∂ρ) ^ n := by
  have hre : Integrable (fun y : ℝ => Real.exp (z.re * y)) ρ :=
    integrable_cexp_iff_exp_re.mp hz
  calc ‖∫ ω in E, cexp (z * partialSum n ω) ∂pathLaw ρ‖
      ≤ ∫ ω in E, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := norm_integral_le_integral_norm _
    _ = ∫ ω in E, Real.exp (z.re * partialSum n ω) ∂pathLaw ρ := by
        simp_rw [norm_cexp_mul_ofReal]
    _ ≤ ∫ ω, Real.exp (z.re * partialSum n ω) ∂pathLaw ρ :=
        setIntegral_le_integral (integrable_exp_partialSum hre n).1
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = _ := (integrable_exp_partialSum hre n).2

omit [IsProbabilityMeasure ρ] in
theorem integral_exp_re_nonneg (z : ℂ) : 0 ≤ ∫ y, Real.exp (z.re * y) ∂ρ :=
  integral_nonneg fun _ => (Real.exp_pos _).le

theorem summable_norm_pow_mul_of_le {s : ℂ} {M : ℝ} (hM : 0 ≤ M) (hs : ‖s‖ * M < 1)
    {c : ℕ → ℂ} (hc : ∀ n, ‖c n‖ ≤ M ^ n) : Summable fun n => ‖s ^ n * c n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg s) hM) hs)
  rw [norm_mul, norm_pow, mul_pow]
  exact mul_le_mul_of_nonneg_left (hc n) (pow_nonneg (norm_nonneg s) n)

/-! ### The transform as a series -/

theorem setOf_firstEntry_lt_top_eq_iUnion (A : Set ℝ) :
    {ω | firstEntry A ω < ⊤} = ⋃ n : ℕ, {ω | firstEntry A ω = n} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  exact firstEntry_lt_top_iff

theorem pairwise_disjoint_firstEntry_eq (A : Set ℝ) :
    Pairwise (Function.onFun Disjoint fun n : ℕ => {ω | firstEntry A ω = n}) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
  simp only [mem_ofPred_eq] at hi hj
  exact_mod_cast hi.symm.trans hj

omit [IsProbabilityMeasure ρ] in
/-- `E[s^τ e^{z S_τ}; τ < ∞] = ∑ sⁿ E[e^{z S_n}; τ = n]` under absolute convergence. -/
theorem entryTransform_eq_tsum (hAm : MeasurableSet A) {s z : ℂ}
    (hint : ∀ n : ℕ, IntegrableOn (fun ω => cexp (z * partialSum n ω))
      {ω | firstEntry A ω = n} (pathLaw ρ))
    (hsum : Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ) :
    entryTransform ρ A s z = ∑' n, s ^ n * entryCoeff ρ A z n := by
  set g : (ℕ → ℝ) → ℂ := fun ω => s ^ (firstEntry A ω).toNat * cexp (z * entryValue A ω)
  have hg : ∀ n : ℕ, EqOn g (fun ω => s ^ n * cexp (z * partialSum n ω))
      {ω | firstEntry A ω = n} := by
    intro n ω hω
    simp only [mem_ofPred_eq] at hω
    simp only [g, hω, ENat.toNat_natCast, entryValue_of_eq hω]
  have hgi : ∀ n : ℕ, IntegrableOn g {ω | firstEntry A ω = n} (pathLaw ρ) := fun n =>
    IntegrableOn.congr_fun (Integrable.const_mul (hint n) (s ^ n)) (hg n).symm
      (measurableSet_firstEntry_eq hAm n)
  have hgn : ∀ n : ℕ, ∫ ω in {ω | firstEntry A ω = n}, ‖g ω‖ ∂pathLaw ρ =
      ‖s‖ ^ n * ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := by
    intro n
    rw [setIntegral_congr_fun (measurableSet_firstEntry_eq hAm n)
      (fun ω hω => congrArg norm (hg n hω))]
    simp_rw [norm_mul, norm_pow]
    exact integral_const_mul _ _
  have hU : IntegrableOn g (⋃ n : ℕ, {ω | firstEntry A ω = n}) (pathLaw ρ) :=
    integrableOn_iUnion_of_summable_integral_norm hgi (by simp_rw [hgn]; exact hsum)
  unfold entryTransform
  rw [setOf_firstEntry_lt_top_eq_iUnion,
    integral_iUnion (fun n => measurableSet_firstEntry_eq hAm n)
      (pairwise_disjoint_firstEntry_eq A) hU]
  refine tsum_congr fun n => ?_
  rw [setIntegral_congr_fun (measurableSet_firstEntry_eq hAm n) (hg n), entryCoeff]
  exact integral_const_mul _ _

theorem norm_cexp_le_one_of_firstEntry_eq {z : ℂ} (hzA : ∀ x ∈ A, z.re * x ≤ 0) {n : ℕ}
    {ω : ℕ → ℝ} (hω : firstEntry A ω = n) : ‖cexp (z * partialSum n ω)‖ ≤ 1 := by
  rw [norm_cexp_mul_ofReal, Real.exp_le_one_iff]
  exact hzA _ (firstEntry_eq_coe_iff.mp hω).2.1

theorem integrableOn_entry_of_bounded (hAm : MeasurableSet A) {z : ℂ}
    (hzA : ∀ x ∈ A, z.re * x ≤ 0) (n : ℕ) :
    IntegrableOn (fun ω => cexp (z * partialSum n ω)) {ω | firstEntry A ω = n} (pathLaw ρ) :=
  Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
    (by fun_prop : Measurable fun ω => cexp (z * partialSum n ω)).aestronglyMeasurable
    ((ae_restrict_iff' (measurableSet_firstEntry_eq hAm n)).mpr
      (Filter.Eventually.of_forall fun _ hω => norm_cexp_le_one_of_firstEntry_eq hzA hω))

/-- Absolute convergence of a ladder series whose integrand is bounded by one:
`∑ ‖s‖ⁿ E[|e^{z S_n}|; τ = n] ≤ ∑ P(τ = n) ≤ 1`. -/
theorem summable_entry_of_bounded (hAm : MeasurableSet A) {s z : ℂ} (hs : ‖s‖ ≤ 1)
    (hzA : ∀ x ∈ A, z.re * x ≤ 0) :
    Summable fun n : ℕ => ‖s‖ ^ n *
      ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ := by
  have hmeas : ∀ n : ℕ, ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖
      ∂pathLaw ρ ≤ (pathLaw ρ).real {ω | firstEntry A ω = n} := by
    intro n
    calc _ ≤ ∫ ω in {ω | firstEntry A ω = n}, (1 : ℝ) ∂pathLaw ρ :=
          setIntegral_mono_on (integrableOn_entry_of_bounded hAm hzA n).norm
            (integrableOn_const (measure_ne_top _ _)) (measurableSet_firstEntry_eq hAm n)
            fun _ hω => norm_cexp_le_one_of_firstEntry_eq hzA hω
      _ = _ := by simp
  have hP : Summable fun n : ℕ => (pathLaw ρ).real {ω | firstEntry A ω = n} :=
    summable_measure_toReal (fun n => measurableSet_firstEntry_eq hAm n)
      (pairwise_disjoint_firstEntry_eq A)
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => norm_nonneg _)) (fun n => ?_) hP
  calc _ ≤ 1 * ∫ ω in {ω | firstEntry A ω = n}, ‖cexp (z * partialSum n ω)‖ ∂pathLaw ρ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs)
          (integral_nonneg fun _ => norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hmeas n

/-- The series form of the transform when the integrand is bounded by one:
`‖s‖ ≤ 1` and `Re z · x ≤ 0` on `A`. -/
theorem entryTransform_eq_tsum_of_bounded (hAm : MeasurableSet A) {s z : ℂ} (hs : ‖s‖ ≤ 1)
    (hzA : ∀ x ∈ A, z.re * x ≤ 0) :
    entryTransform ρ A s z = ∑' n, s ^ n * entryCoeff ρ A z n :=
  entryTransform_eq_tsum hAm (integrableOn_entry_of_bounded hAm hzA)
    (summable_entry_of_bounded hAm hs hzA)

/-! ### The factorization -/

theorem integrableOn_cexp_partialSum {z : ℂ} (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (E : Set (ℕ → ℝ)) (n : ℕ) :
    IntegrableOn (fun ω => cexp (z * partialSum n ω)) E (pathLaw ρ) :=
  (integrable_cexp_partialSum hz n).1.integrableOn

theorem entryTransform_eq_tsum_of_lt_one (hAm : MeasurableSet A) {s z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (hs : ‖s‖ * ∫ y, Real.exp (z.re * y) ∂ρ < 1) :
    entryTransform ρ A s z = ∑' n, s ^ n * entryCoeff ρ A z n := by
  have hre : Integrable (fun y : ℝ => Real.exp (z.re * y)) ρ :=
    integrable_cexp_iff_exp_re.mp hz
  refine entryTransform_eq_tsum hAm (fun n => integrableOn_cexp_partialSum hz _ n) ?_
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (pow_nonneg (norm_nonneg _) _)
    (integral_nonneg fun _ => norm_nonneg _)) (fun n => ?_)
    (summable_geometric_of_lt_one (mul_nonneg (norm_nonneg s) (integral_exp_re_nonneg z)) hs)
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) _)
  calc _ = ∫ ω in {ω | firstEntry A ω = n}, Real.exp (z.re * partialSum n ω) ∂pathLaw ρ := by
        simp_rw [norm_cexp_mul_ofReal]
    _ ≤ ∫ ω, Real.exp (z.re * partialSum n ω) ∂pathLaw ρ :=
        setIntegral_le_integral (integrable_exp_partialSum hre n).1
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = _ := (integrable_exp_partialSum hre n).2

/-- The generating function of the survival coefficients:
`(∑ sⁿ E[e^{z S_n}; n < τ_{Aᶜ}]) (1 - E[s^{τ_A} e^{z S_{τ_A}}; τ_A < ∞]) = 1`. -/
theorem tsum_survivalCoeff_compl_mul (hAm : MeasurableSet A) (hA : IsLadderSet A) {s z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (hs : ‖s‖ * ∫ y, Real.exp (z.re * y) ∂ρ < 1) :
    (∑' n, s ^ n * survivalCoeff ρ Aᶜ z n) * (1 - entryTransform ρ A s z) = 1 := by
  set M := ∫ y, Real.exp (z.re * y) ∂ρ
  have hM := integral_exp_re_nonneg (ρ := ρ) z
  have hd : ∀ n, ‖ladderTimeCoeff ρ A z n‖ ≤ M ^ n := fun n =>
    norm_setIntegral_cexp_partialSum_le hz _ n
  have hf : ∀ n, ‖entryCoeff ρ A z n‖ ≤ M ^ n := fun n =>
    norm_setIntegral_cexp_partialSum_le hz _ n
  have hint : ∀ (E : Set (ℕ → ℝ)), MeasurableSet E → ∀ m : ℕ,
      Integrable (E.indicator fun ω => cexp (z * partialSum m ω)) (pathLaw ρ) :=
    fun E hE m => (integrable_cexp_partialSum hz m).1.indicator hE
  have hren := ladderTimeCoeff_eq (ρ := ρ) hAm hA
    (fun k => hint _ (measurableSet_firstEntry_eq hAm k) k)
    (fun m => hint _ (measurableSet_isLadderTime hAm m) m)
  have hD := tsum_pow_mul_eq_add_mul (summable_norm_pow_mul_of_le hM hs hf)
    (summable_norm_pow_mul_of_le hM hs hd)
    (c := fun n => if n = 0 then 1 else 0)
    (by
      refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
      simp only [Finset.mem_singleton] at hn
      simp [hn]) hren
  have h1 : ∑' n, s ^ n * (if n = 0 then (1 : ℂ) else 0) = 1 := by
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  rw [h1, ← entryTransform_eq_tsum_of_lt_one hAm hz hs] at hD
  simp_rw [survivalCoeff_compl_eq_ladderTimeCoeff hAm z]
  linear_combination hD

/-- **Wiener–Hopf factorization** for a half-line type set `A`:
`1 - s φ(z) = (1 - E[s^{τ_{Aᶜ}} e^{z S}; τ_{Aᶜ} < ∞]) (1 - E[s^{τ_A} e^{z S}; τ_A < ∞])`
whenever `e^{z ·}` is `ρ`-integrable and `‖s‖ ∫ e^{Re z · y} dρ(y) < 1`. -/
theorem wienerHopf_of_isLadderSet (hAm : MeasurableSet A) (hA : IsLadderSet A) {s z : ℂ}
    (hz : Integrable (fun y : ℝ => cexp (z * y)) ρ)
    (hs : ‖s‖ * ∫ y, Real.exp (z.re * y) ∂ρ < 1) :
    1 - s * stepTransform ρ z =
      (1 - entryTransform ρ Aᶜ s z) * (1 - entryTransform ρ A s z) := by
  set M := ∫ y, Real.exp (z.re * y) ∂ρ
  have hM := integral_exp_re_nonneg (ρ := ρ) z
  have hφ : ‖stepTransform ρ z‖ ≤ M := by
    have := norm_setIntegral_cexp_partialSum_le hz (ρ := ρ) univ 1
    simpa [Measure.restrict_univ, integral_cexp_partialSum hz] using this
  have hsφ : ‖s * stepTransform ρ z‖ < 1 := by
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hφ (norm_nonneg s)) hs
  have ha : ∀ n, ‖stepTransform ρ z ^ n‖ ≤ M ^ n := fun n => by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hφ n
  have hf : ∀ n, ‖entryCoeff ρ Aᶜ z n‖ ≤ M ^ n := fun n =>
    norm_setIntegral_cexp_partialSum_le hz _ n
  have hg : ∀ n, ‖survivalCoeff ρ Aᶜ z n‖ ≤ M ^ n := fun n =>
    norm_setIntegral_cexp_partialSum_le hz _ n
  have hX := tsum_pow_mul_eq_add_mul (summable_norm_pow_mul_of_le hM hs hf)
    (summable_norm_pow_mul_of_le hM hs ha) (summable_norm_pow_mul_of_le hM hs hg).of_norm
    (stepTransform_pow_eq_survival_add hAm.compl hz)
  rw [← entryTransform_eq_tsum_of_lt_one hAm.compl hz hs] at hX
  have hgeo : ∑' n, s ^ n * stepTransform ρ z ^ n = (1 - s * stepTransform ρ z)⁻¹ := by
    simp_rw [← mul_pow]
    exact tsum_geometric_of_norm_lt_one hsφ
  have hne : 1 - s * stepTransform ρ z ≠ 0 := by
    intro h
    have : ‖s * stepTransform ρ z‖ = 1 := by
      rw [show s * stepTransform ρ z = 1 by linear_combination -h, norm_one]
    exact (lt_irrefl _) (this ▸ hsφ)
  have hXinv : (∑' n, s ^ n * stepTransform ρ z ^ n) * (1 - s * stepTransform ρ z) = 1 := by
    rw [hgeo, inv_mul_cancel₀ hne]
  have hD := tsum_survivalCoeff_compl_mul hAm hA hz hs
  set X := ∑' n, s ^ n * stepTransform ρ z ^ n
  set D := ∑' n, s ^ n * survivalCoeff ρ Aᶜ z n
  set F₁ := entryTransform ρ Aᶜ s z
  set F₂ := entryTransform ρ A s z
  set q := s * stepTransform ρ z
  linear_combination ((1 - F₁) * (1 - F₂)) * hXinv - (1 - q) * (1 - F₂) * hX - (1 - q) * hD

theorem integrable_cexp_of_re_eq_zero {z : ℂ} (hz : z.re = 0) :
    Integrable (fun y : ℝ => cexp (z * y)) ρ :=
  Integrable.of_bound (by fun_prop) 1
    (Filter.Eventually.of_forall fun y => by rw [norm_cexp_mul_ofReal, hz]; simp)

theorem integral_exp_re_of_re_eq_zero {z : ℂ} (hz : z.re = 0) :
    ∫ y, Real.exp (z.re * y) ∂ρ = 1 := by
  simp [hz]

/-- **Wiener–Hopf factorization** (W2): for `‖s‖ < 1` and `Re z = 0`,
`1 - s φ(z) = (1 - χ₊(s, z)) (1 - χ₋(s, z))`, where `χ₊` is the transform of the strict
ascending ladder `(τ₊, S_{τ₊})` and `χ₋` that of the weak descending ladder. -/
theorem wienerHopf (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s z : ℂ} (hs : ‖s‖ < 1)
    (hz : z.re = 0) :
    1 - s * stepTransform ρ z = (1 - ascTransform ρ s z) * (1 - descTransform ρ s z) := by
  have h := wienerHopf_of_isLadderSet (ρ := ρ) measurableSet_Iic isLadderSet_Iic
    (s := s) (integrable_cexp_of_re_eq_zero hz)
    (by rw [integral_exp_re_of_re_eq_zero hz, mul_one]; exact hs)
  rwa [compl_Iic] at h

/-- The dual factorization with the weak ascending ladder `inf {n ≥ 1 : S n ≥ 0}` and the strict
descending ladder `inf {n ≥ 1 : S n < 0}`. -/
theorem wienerHopf_weakAsc_strictDesc (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s z : ℂ}
    (hs : ‖s‖ < 1) (hz : z.re = 0) :
    1 - s * stepTransform ρ z =
      (1 - entryTransform ρ (Ici 0) s z) * (1 - entryTransform ρ (Iio 0) s z) := by
  have h := wienerHopf_of_isLadderSet (ρ := ρ) measurableSet_Iio isLadderSet_Iio
    (s := s) (integrable_cexp_of_re_eq_zero hz)
    (by rw [integral_exp_re_of_re_eq_zero hz, mul_one]; exact hs)
  rwa [compl_Iio] at h

/-- `∑ sⁿ E[e^{z S_n}; n < τ₊] = (1 - χ₋(s, z))⁻¹` for `‖s‖ < 1`, `Re z = 0`. -/
theorem tsum_survival_asc_mul (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s z : ℂ}
    (hs : ‖s‖ < 1) (hz : z.re = 0) :
    (∑' n, s ^ n * survivalCoeff ρ (Ioi 0) z n) * (1 - descTransform ρ s z) = 1 := by
  have h := tsum_survivalCoeff_compl_mul (ρ := ρ) measurableSet_Iic isLadderSet_Iic
    (s := s) (integrable_cexp_of_re_eq_zero hz)
    (by rw [integral_exp_re_of_re_eq_zero hz, mul_one]; exact hs)
  rwa [compl_Iic] at h

/-- `∑ sⁿ E[e^{z S_n}; n < τ₋] = (1 - χ₊(s, z))⁻¹` for `‖s‖ < 1`, `Re z = 0`. -/
theorem tsum_survival_desc_mul (ρ : Measure ℝ) [IsProbabilityMeasure ρ] {s z : ℂ}
    (hs : ‖s‖ < 1) (hz : z.re = 0) :
    (∑' n, s ^ n * survivalCoeff ρ (Iic 0) z n) * (1 - ascTransform ρ s z) = 1 := by
  have h := tsum_survivalCoeff_compl_mul (ρ := ρ) measurableSet_Ioi isLadderSet_Ioi
    (s := s) (integrable_cexp_of_re_eq_zero hz)
    (by rw [integral_exp_re_of_re_eq_zero hz, mul_one]; exact hs)
  rwa [compl_Ioi] at h

end PGM.WienerHopf
