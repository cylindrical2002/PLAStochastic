import PLAStochastic.Index.GEP.Universality.ClassProperties
import PLAStochastic.Index.GEP.OrbitClosure.SumDensity
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Moments.Variance

/-!
# WP5 characteristic-function deficits and singular remainders

A Fourier deficit of a finite submeasure passes to any probability measure that dominates
it. This is the bridge needed for a bounded density component with an arbitrary singular
remainder. The last result converts the existing WP2 squared-modulus estimate into a linear
deficit; constructing uniform tilted components is a separate step.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem charFun_add_measure_real (μ η : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (t : ℝ) : charFun (μ + η) t = charFun μ t + charFun η t := by
  simp only [charFun_eq_integral_innerProbChar]
  exact integral_add_measure
    ((BoundedContinuousFunction.innerProbChar t).integrable μ)
    ((BoundedContinuousFunction.innerProbChar t).integrable η)

theorem charFun_smul_measure_real (μ : Measure ℝ) (c : ℝ≥0∞) (t : ℝ) :
    charFun (c • μ) t = c.toReal • charFun μ t := by
  simp only [charFun_apply_real, integral_smul_measure]

/-- A submeasure's deficit survives any remainder, including a singular one. -/
theorem norm_charFun_le_of_submeasure_gap {μ η : Measure ℝ} [IsProbabilityMeasure μ]
    (hη : η ≤ μ) {t δ : ℝ} (hgap : ‖charFun η t‖ ≤ η.real univ - δ) :
    ‖charFun μ t‖ ≤ 1 - δ := by
  let : IsFiniteMeasure η := isFiniteMeasure_of_le μ hη
  have hdecomp : μ - η + η = μ := Measure.sub_add_cancel_of_le hη
  have hmass : (μ - η).real univ + η.real univ = 1 := by
    rw [← measureReal_add_apply, hdecomp, probReal_univ]
  calc ‖charFun μ t‖ = ‖charFun (μ - η) t + charFun η t‖ := by
          rw [← charFun_add_measure_real, hdecomp]
    _ ≤ ‖charFun (μ - η) t‖ + ‖charFun η t‖ := norm_add_le _ _
    _ ≤ (μ - η).real univ + (η.real univ - δ) :=
          add_le_add (norm_charFun_le t) hgap
    _ = 1 - δ := by linarith

/-- A probability component of mass `p` transfers its deficit with factor `p`. -/
theorem norm_charFun_le_of_component_gap {μ ρ : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] {p t δ : ℝ} (hp : 0 ≤ p)
    (hpart : ENNReal.ofReal p • ρ ≤ μ) (hgap : ‖charFun ρ t‖ ≤ 1 - δ) :
    ‖charFun μ t‖ ≤ 1 - p * δ := by
  apply norm_charFun_le_of_submeasure_gap hpart
  simp only [charFun_smul_measure_real, norm_smul, Real.norm_eq_abs,
    ENNReal.toReal_ofReal hp, abs_of_nonneg hp, measureReal_ennreal_smul_apply,
    probReal_univ, mul_one]
  calc p * ‖charFun ρ t‖ ≤ p * (1 - δ) := mul_le_mul_of_nonneg_left hgap hp
    _ = p - p * δ := by ring

theorem norm_charFun_mixPM_le_of_left (ν ρ : ProbabilityMeasure ℝ) (s : ℝ) {t δ : ℝ}
    (hgap : ‖charFun (ν : Measure ℝ) t‖ ≤ 1 - δ) :
    ‖charFun (mixPM ν ρ s : Measure ℝ) t‖ ≤ 1 - (1 - mixParam s) * δ := by
  apply norm_charFun_le_of_component_gap (sub_nonneg.mpr (mixParam_le_one s)) ?_ hgap
  rw [coe_mixPM]
  exact Measure.le_add_right le_rfl

/-- The WP2 squared-modulus estimate gives a linear characteristic-function deficit. -/
theorem norm_charFun_le_of_locBd_moments {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {M m σ : ℝ} (hM : LocBd M μ) (h2 : MemLp id 2 μ) (hm : ∫ x, x ∂μ = m)
    (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2) (hσ : 0 < σ) (t : ℝ) :
    ‖charFun μ t‖ ≤ 1 - (c0CharFn * min 1 (t ^ 2 * σ ^ 2) / (M * σ) ^ 2) / 2 := by
  have h := one_sub_norm_charFun_sq_ge hM h2 hm hvar hσ t
  nlinarith [sq_nonneg (1 - ‖charFun μ t‖)]

/-- The density and variance upper bounds give one gap away from the origin.
The constant does not depend on the actual positive variance `σ²`. -/
theorem norm_charFun_le_uniform_of_locBd_moments {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {M m σ V t₀ : ℝ} (hM : LocBd M μ) (hM0 : 0 < M) (h2 : MemLp id 2 μ)
    (hm : ∫ x, x ∂μ = m) (hvar : ∫ x, (x - m) ^ 2 ∂μ = σ ^ 2)
    (hσ : 0 < σ) (hV : σ ^ 2 ≤ V) (ht₀ : 0 < t₀) {t : ℝ} (ht : t₀ ≤ |t|) :
    ‖charFun μ t‖ ≤ 1 - c0CharFn * min (t₀ ^ 2) (1 / V) / M ^ 2 / 2 := by
  have hV0 : 0 < V := (sq_pos_of_pos hσ).trans_le hV
  have htt : t₀ ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
  have hmin : min (t₀ ^ 2) (1 / V) * σ ^ 2 ≤ min 1 (t ^ 2 * σ ^ 2) := by
    refine le_min ?_ ?_
    · calc min (t₀ ^ 2) (1 / V) * σ ^ 2 ≤ (1 / V) * σ ^ 2 :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
        _ ≤ (1 / V) * V := mul_le_mul_of_nonneg_left hV (by positivity)
        _ = 1 := by field_simp
    · exact mul_le_mul_of_nonneg_right ((min_le_left _ _).trans htt) (sq_nonneg _)
  have hquot : c0CharFn * min (t₀ ^ 2) (1 / V) / M ^ 2 ≤
      c0CharFn * min 1 (t ^ 2 * σ ^ 2) / (M * σ) ^ 2 := by
    calc c0CharFn * min (t₀ ^ 2) (1 / V) / M ^ 2 =
        c0CharFn * (min (t₀ ^ 2) (1 / V) * σ ^ 2) / (M * σ) ^ 2 := by
          field_simp
      _ ≤ c0CharFn * min 1 (t ^ 2 * σ ^ 2) / (M * σ) ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmin c0CharFn_pos.le) (sq_nonneg _)
  have h := norm_charFun_le_of_locBd_moments hM h2 hm hvar hσ t
  linarith

/-- A uniformly bounded density component transfers a uniform gap to the full law. -/
theorem norm_charFun_le_uniform_of_component {μ ρ : Measure ℝ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] {p M m σ V t₀ : ℝ}
    (hp : 0 ≤ p) (hpart : ENNReal.ofReal p • ρ ≤ μ)
    (hM : LocBd M ρ) (hM0 : 0 < M) (h2 : MemLp id 2 ρ)
    (hm : ∫ x, x ∂ρ = m) (hvar : ∫ x, (x - m) ^ 2 ∂ρ = σ ^ 2)
    (hσ : 0 < σ) (hV : σ ^ 2 ≤ V) (ht₀ : 0 < t₀) {t : ℝ} (ht : t₀ ≤ |t|) :
    ‖charFun μ t‖ ≤ 1 - p * (c0CharFn * min (t₀ ^ 2) (1 / V) / M ^ 2 / 2) := by
  exact norm_charFun_le_of_component_gap hp hpart
    (norm_charFun_le_uniform_of_locBd_moments hM hM0 h2 hm hvar hσ hV ht₀ ht)

theorem LocBd.const_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {M : ℝ}
    (hM : LocBd M μ) : 0 < M := by
  by_contra h
  have hle := hM univ MeasurableSet.univ
  simp [ENNReal.ofReal_of_nonpos (le_of_not_gt h)] at hle

/-- A bounded density excludes the zero-variance case without a quantitative lower bound. -/
theorem LocBd.variance_pos {μ : Measure ℝ} [IsProbabilityMeasure μ] {M : ℝ}
    (hM : LocBd M μ) (h2 : MemLp id 2 μ) : 0 < variance id μ := by
  by_contra h
  have hzero : variance id μ = 0 :=
    le_antisymm (le_of_not_gt h) (variance_nonneg id μ)
  have hae := ae_eq_integral_of_variance_eq_zero h2 hzero
  have hmass : μ {∫ x, x ∂μ} = 1 := by
    apply (mem_ae_iff_prob_eq_one (measurableSet_singleton _)).mp
    exact hae
  have hle := hM {∫ x, x ∂μ} (measurableSet_singleton _)
  simp [hmass] at hle

/-- A density bound and an upper second-moment bound give a uniform Cramér gap.
No lower variance parameter is needed in the resulting constant. -/
theorem norm_charFun_le_uniform_of_locBd {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {M C t₀ : ℝ} (hM : LocBd M μ) (h2 : MemLp id 2 μ)
    (hC : ∫ x, x ^ 2 ∂μ ≤ C) (ht₀ : 0 < t₀) {t : ℝ} (ht : t₀ ≤ |t|) :
    ‖charFun μ t‖ ≤ 1 - c0CharFn * min (t₀ ^ 2) (1 / C) / M ^ 2 / 2 := by
  have hv := hM.variance_pos h2
  have hvar : ∫ x, (x - ∫ y, y ∂μ) ^ 2 ∂μ = Real.sqrt (variance id μ) ^ 2 := by
    rw [Real.sq_sqrt hv.le, variance_eq_integral h2.aemeasurable]
    rfl
  have hbound : Real.sqrt (variance id μ) ^ 2 ≤ C := by
    rw [Real.sq_sqrt hv.le]
    exact (variance_le_expectation_sq h2.aestronglyMeasurable).trans hC
  exact norm_charFun_le_uniform_of_locBd_moments hM hM.const_pos h2 rfl hvar
    (Real.sqrt_pos.mpr hv) hbound ht₀ ht

end

end PGM
