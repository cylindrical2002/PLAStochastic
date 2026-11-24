import PLAStochastic.ForMathlib.Probability.CDF.QuantileTransport
import PLAStochastic.Index.GEP.OrbitClosure.CharFunDensity

/-! # WP5: positive Gaussian-smoothed densities and their quantiles -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Filter Topology
open scoped Real ENNReal NNReal

/-- The pointwise density of a Gaussian smoothing, in the symmetric convention
used by the Fourier identity in `GEPClosureCharFun`. -/
def saGaussianDensity (μ : Measure ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  ∫ y, gaussianPDFReal x v y ∂μ

theorem saGaussianDensity_nonneg (μ : Measure ℝ) (v : ℝ≥0) (x : ℝ) :
    0 ≤ saGaussianDensity μ v x := integral_nonneg (gaussianPDFReal_nonneg _ _)

theorem saGaussianDensity_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 < saGaussianDensity μ v x := by
  apply (integral_pos_iff_support_of_nonneg (gaussianPDFReal_nonneg x v)
    (integrable_gaussianPDFReal_of_finite μ x v)).mpr
  have he : Function.support (gaussianPDFReal x v) = univ := by
    ext y
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (gaussianPDFReal_pos x v y hv).ne'
  rw [he, measure_univ]
  norm_num

theorem saGaussianDensity_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (v : ℝ≥0) (x : ℝ) : saGaussianDensity μ v x ≤ (√(2 * π * v))⁻¹ := by
  calc
    _ ≤ ∫ _ : ℝ, (√(2 * π * v))⁻¹ ∂μ :=
      integral_mono (integrable_gaussianPDFReal_of_finite μ x v) (integrable_const _)
        (fun y => gaussianPDFReal_le_inv_sqrt x y v)
    _ = _ := by simp

theorem continuous_saGaussianDensity (μ : Measure ℝ) [IsFiniteMeasure μ] (v : ℝ≥0) :
    Continuous (saGaussianDensity μ v) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => (√(2 * π * v))⁻¹)
    (fun x => (measurable_gaussianPDFReal x v).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => ?_) (integrable_const _) (ae_of_all _ fun y => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact gaussianPDFReal_le_inv_sqrt x y v
  · unfold gaussianPDFReal
    fun_prop

theorem sa_gaussianPDFReal_symm (x y : ℝ) (v : ℝ≥0) :
    gaussianPDFReal x v y = gaussianPDFReal y v x := by
  unfold gaussianPDFReal
  rw [sub_sq_comm x y]

/-- The pointwise smoothing density represents the actual convolution law. -/
theorem saGaussianDensity_law (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ≥0} (hv : v ≠ 0) :
    volume.withDensity (fun x => ENNReal.ofReal (saGaussianDensity μ v x)) =
      μ ∗ gaussianReal 0 v := by
  ext A hA
  rw [withDensity_apply _ hA, Measure.conv, Measure.map_apply measurable_add hA,
    Measure.prod_apply (measurable_add hA)]
  have hpt (x : ℝ) : ENNReal.ofReal (saGaussianDensity μ v x) =
      ∫⁻ y, ENNReal.ofReal (gaussianPDFReal y v x) ∂μ := by
    rw [saGaussianDensity, ofReal_integral_eq_lintegral_ofReal
      (integrable_gaussianPDFReal_of_finite μ x v)
      (ae_of_all _ (gaussianPDFReal_nonneg _ _))]
    apply lintegral_congr
    intro y
    rw [sa_gaussianPDFReal_symm]
  simp_rw [hpt]
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro y
  have hmap := congrArg (fun ρ : Measure ℝ => ρ A)
    (gaussianReal_map_const_add (μ := 0) (v := v) y)
  rw [Measure.map_apply (by fun_prop) hA, zero_add] at hmap
  change (∫⁻ x in A, gaussianPDF y v x) = _
  rw [← gaussianReal_apply y hv A]
  exact hmap.symm

/-- Any everywhere positive probability density has a regular CDF. -/
theorem saCDF_withDensity {q : ℝ → ℝ} (hm : Measurable q) (hp : ∀ x, 0 < q x)
    [IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (q x)))] :
    SACDF (cdf (volume.withDensity (fun x => ENNReal.ofReal (q x)))) := by
  have hac : volume ≪ volume.withDensity (fun x => ENNReal.ofReal (q x)) :=
    withDensity_absolutelyContinuous' hm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hp x)).ne')
  let := hac.isOpenPosMeasure
  exact saCDF_cdf _

/-- Smoothing makes the quantile transport applicable even when the original law
has atoms or a singular component. -/
theorem saCDF_gaussian_smoothing (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {v : ℝ≥0} (hv : v ≠ 0) : SACDF (cdf (μ ∗ gaussianReal 0 v)) := by
  have hl := saGaussianDensity_law μ hv
  have : IsProbabilityMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (saGaussianDensity μ v x))) := by
    rw [hl]
    infer_instance
  rw [← hl]
  exact saCDF_withDensity (continuous_saGaussianDensity μ v).measurable
    (saGaussianDensity_pos μ hv)

theorem saCDF_gaussianReal (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    SACDF (cdf (gaussianReal m v)) := by
  let := nullSingletonClass_gaussianReal (μ := m) hv
  let := (gaussianReal_absolutelyContinuous' m hv).isOpenPosMeasure
  exact saCDF_cdf _

end

end PGM
