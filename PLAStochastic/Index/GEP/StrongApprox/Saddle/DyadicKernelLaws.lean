import PLAStochastic.Index.GEP.StrongApprox.Saddle.ConditionalGaussianRatio
import PLAStochastic.Index.GEP.StrongApprox.Quantile.SplitLaw

/-! # WP5: the saddle kernels are the actual dyadic convolution and split laws -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped Real ENNReal NNReal

theorem sa_convPow_add (μ : Measure ℝ) [IsProbabilityMeasure μ] (n m : ℕ) :
    convPow μ (n + m) = convPow μ n ∗ convPow μ m := by
  apply Measure.ext_of_charFun
  funext t
  simp only [charFun_convPow, charFun_conv, pow_add]

theorem sa_gaussian_smoothing_conv (μ ρ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ρ] (v w : ℝ≥0) :
    (μ ∗ gaussianReal 0 v) ∗ (ρ ∗ gaussianReal 0 w) =
      (μ ∗ ρ) ∗ gaussianReal 0 (v + w) := by
  have he : (μ ∗ gaussianReal 0 v) ∗ (ρ ∗ gaussianReal 0 w) =
      (μ ∗ ρ) ∗ (gaussianReal 0 v ∗ gaussianReal 0 w) := by
    apply Measure.ext_of_charFun
    funext t
    simp only [charFun_conv]
    ring
  rw [he, gaussianReal_conv_gaussianReal, zero_add]

/-- The sum density used in the saddle estimates is a genuine positive bounded
probability density for every nonempty block and positive smoothing width. -/
theorem saDensity_centeredSum (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {l : ℕ} (hl : 0 < l) : SADensity (saCenteredSumDensity ν s l) := by
  let : IsProbabilityMeasure ((ν : Measure ℝ).map (fun y => y - 1)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  apply saDensity_gaussian
  exact mul_ne_zero (by exact_mod_cast hl.ne')
    (by simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge])

theorem saDensity_centeredSum_law (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {l : ℕ} (hl : 0 < l) :
    ((saDensity_centeredSum ν hs hl).law : Measure ℝ) =
      convPow ((ν : Measure ℝ).map (fun y => y - 1)) l ∗
        gaussianReal 0 ((l : ℝ≥0) * Real.toNNReal (s ^ 2)) := by
  let : IsProbabilityMeasure ((ν : Measure ℝ).map (fun y => y - 1)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  exact saGaussianDensity_law _ (mul_ne_zero (by exact_mod_cast hl.ne')
    (by simp [Real.toNNReal_eq_zero, (sq_pos_of_pos hs).not_ge]))

/-- Pointwise convolution identity, obtained from equality of actual laws and
continuity of both densities. -/
theorem saSumDensity_centeredSum (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {l : ℕ} (hl : 0 < l) :
    saSumDensity (saCenteredSumDensity ν s l) = saCenteredSumDensity ν s (2 * l) := by
  let : IsProbabilityMeasure ((ν : Measure ℝ).map (fun y => y - 1)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  have h2l : 0 < 2 * l := by omega
  apply (saDensity_centeredSum ν hs hl).sumDensity.eq_of_law (saDensity_centeredSum ν hs h2l)
  change volume.withDensity (fun x => ENNReal.ofReal
    (saSumDensity (saCenteredSumDensity ν s l) x)) = _
  rw [(saDensity_centeredSum ν hs hl).sumDensity_law,
    saDensity_centeredSum_law ν hs hl, saDensity_centeredSum_law ν hs h2l,
    sa_gaussian_smoothing_conv, ← sa_convPow_add]
  have hn : l + l = 2 * l := by omega
  rw [hn]
  congr 2
  push_cast
  ring

/-- The quotient estimated in the saddle calculation is exactly the normalized
conditional split kernel consumed by the dyadic quantile sampler. -/
theorem saSplitDensity_centeredSum (ν : ProbabilityMeasure ℝ) {s : ℝ} (hs : 0 < s)
    {l : ℕ} (hl : 0 < l) (u t : ℝ) :
    saSplitDensity (saCenteredSumDensity ν s l) (2 * l * u) (l * (u + t)) =
      saCenteredSumDensity ν s l (l * (u + t)) *
        saCenteredSumDensity ν s l (l * (u - t)) /
        saCenteredSumDensity ν s (2 * l) (2 * l * u) := by
  rw [saSplitDensity, saSumDensity_centeredSum ν hs hl]
  congr 2
  congr 1
  ring

end

end PGM
