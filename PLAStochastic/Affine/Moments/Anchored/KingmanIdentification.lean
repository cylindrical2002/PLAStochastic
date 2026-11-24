import PLAStochastic.ForMathlib.Probability.KingmanSum.FiniteCDF
import PLAStochastic.ForMathlib.Probability.KingmanSum.CDFLimit
import PLAStochastic.Affine.Moments.Anchored.SumCDF
import PLAStochastic.ForMathlib.Probability.KingmanSum.LaplaceClosedForm

/-!
# Identifying the actual Brownian supremum sum with independent exponentials

Both probability measures have the same closed CDF. The finite convolution,
coefficient limit and summable majorant are proved in separate modules. The
Laplace product and closed forms below are therefore statements about the
actual Brownian functional, not an assumed transform.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The CDF of the constructed independent infinite sum has the spectral expansion. -/
theorem kingmanCDF_eq_sumCDFSeries {s : ℝ} (hs : 0 < s) :
    kingmanCDF s = sumCDFSeries s := by
  have ht := kingmanPartialCDF_tendsto s
  simp only [kingmanPartialCDF_formula _ hs.le] at ht
  exact tendsto_nhds_unique ht (kingmanCDFExpansion_tendsto hs)

private theorem measure_le_zero_of_ae_pos {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {X : Ω → ℝ} (hX : ∀ᵐ ω ∂ν, 0 < X ω) {s : ℝ} (hs : s ≤ 0) :
    ν {ω | X ω ≤ s} = 0 := by
  apply measure_mono_null (t := {ω | ¬ 0 < X ω})
  · intro ω hω
    change X ω ≤ s at hω
    exact not_lt.mpr (hω.trans hs)
  · exact ae_iff.mp hX

/-- The law of the infinite holding-time sum, including the nonpositive half-line. -/
theorem kingmanSumMeasure_Iic (s : ℝ) : kingmanSumMeasure (Iic s) =
    if 0 < s then ENNReal.ofReal (sumCDFSeries s) else 0 := by
  rw [kingmanSumMeasure, Measure.map_apply kingmanTotalReal_measurable measurableSet_Iic]
  by_cases hs : 0 < s
  · rw [if_pos hs, ← kingmanCDF_eq_sumCDFSeries hs]
    unfold kingmanCDF
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rfl
  · rw [if_neg hs]
    exact measure_le_zero_of_ae_pos kingmanTotalReal_ae_pos (le_of_not_gt hs)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Equality of genuine pushforward measures proves the independent-series identity. -/
theorem map_realDriftedSum_eq_kingmanSumMeasure (hB : IsBrownianReal B μ) :
    μ.map (fun ω => realDriftedSum (B · ω) 1) = kingmanSumMeasure := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hS := aemeasurable_realDriftedSum hB
  have : IsProbabilityMeasure (μ.map (fun ω => realDriftedSum (B · ω) 1)) :=
    Measure.isProbabilityMeasure_map hS
  apply Measure.ext_of_Iic
  intro s
  rw [Measure.map_apply_of_aemeasurable hS measurableSet_Iic, kingmanSumMeasure_Iic]
  by_cases hs : 0 < s
  · rw [if_pos hs]
    exact measure_realDriftedSum_le hB hs
  · rw [if_neg hs]
    exact measure_le_zero_of_ae_pos (realDriftedSum_positive_ae hB) (le_of_not_gt hs)

theorem realDriftedSum_hasLaw_kingman (hB : IsBrownianReal B μ) :
    HasLaw (fun ω => realDriftedSum (B · ω) 1) kingmanSumMeasure μ :=
  ⟨aemeasurable_realDriftedSum hB, map_realDriftedSum_eq_kingmanSumMeasure hB⟩

theorem identDistrib_realDriftedSum_kingmanTotalReal (hB : IsBrownianReal B μ) :
    IdentDistrib (fun ω => realDriftedSum (B · ω) 1) kingmanTotalReal μ kingmanMeasure :=
  ⟨aemeasurable_realDriftedSum hB, kingmanTotalReal_measurable.aemeasurable,
    map_realDriftedSum_eq_kingmanSumMeasure hB⟩

/-- The actual anchored lifetime is twice the inverse independent exponential sum. -/
theorem identDistrib_anchoredLifetime_two_div_kingmanTotalReal (hB : IsBrownianReal B μ) :
    IdentDistrib (anchoredUnitLifetime B) (fun ω => 2 / kingmanTotalReal ω)
      μ kingmanMeasure := by
  exact (identDistrib_anchoredLifetime_real_two_div_realDriftedSum hB).trans
    ((identDistrib_realDriftedSum_kingmanTotalReal hB).comp (by fun_prop :
      Measurable (fun x : ℝ => 2 / x)))

/-- The transform equality holds as an equality of integrals for every real parameter. -/
theorem integral_laplace_realDriftedSum (hB : IsBrownianReal B μ) (z : ℝ) :
    (∫ ω, Real.exp (-(z * realDriftedSum (B · ω) 1)) ∂μ) = kingmanLaplace z :=
  ((identDistrib_realDriftedSum_kingmanTotalReal hB).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.exp (-(z * x))))).integral_eq

theorem realDriftedSum_laplace_product (hB : IsBrownianReal B μ) {z : ℝ} (hz : 0 ≤ z) :
    (∫ ω, Real.exp (-(z * realDriftedSum (B · ω) 1)) ∂μ) =
      ∏' n, kingmanRate n / (kingmanRate n + z) := by
  rw [integral_laplace_realDriftedSum hB z, kingmanLaplace_eq_tprod hz]

theorem realDriftedSum_laplace_cos (hB : IsBrownianReal B μ) {z : ℝ}
    (hz : 0 < z) (hz' : z ≤ 1 / 4) :
    (∫ ω, Real.exp (-(z * realDriftedSum (B · ω) 1)) ∂μ) =
      Real.pi * z / Real.cos (Real.pi / 2 * Real.sqrt (1 - 4 * z)) := by
  rw [integral_laplace_realDriftedSum hB z, kingmanLaplace_eq_cos hz hz']

theorem realDriftedSum_laplace_cosh (hB : IsBrownianReal B μ) {z : ℝ}
    (hz : 1 / 4 ≤ z) :
    (∫ ω, Real.exp (-(z * realDriftedSum (B · ω) 1)) ∂μ) =
      Real.pi * z / Real.cosh (Real.pi / 2 * Real.sqrt (4 * z - 1)) := by
  rw [integral_laplace_realDriftedSum hB z, kingmanLaplace_eq_cosh hz]

theorem integral_realDriftedSum (hB : IsBrownianReal B μ) :
    (∫ ω, realDriftedSum (B · ω) 1 ∂μ) = 1 := by
  rw [(identDistrib_realDriftedSum_kingmanTotalReal hB).integral_eq, integral_kingmanTotalReal]

/-- The gamma-integral formula now uses the evaluated independent-sum transform. -/
theorem anchoredUnitLifetime_moment_kingmanLaplace (hB : IsBrownianReal B μ)
    {q : ℝ} (hq : 0 < q) :
    IntegrableOn (fun z : ℝ => z ^ (q - 1) * kingmanLaplace z) (Ioi 0) ∧
      (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) = (2 : ℝ) ^ q / Real.Gamma q *
        ∫ z : ℝ in Ioi 0, z ^ (q - 1) * kingmanLaplace z := by
  have h := anchoredUnitLifetime_moment_laplace_integral hB hq
  simpa only [mul_comm (realDriftedSum _ 1), integral_laplace_realDriftedSum hB] using h

end BrownianAffine
