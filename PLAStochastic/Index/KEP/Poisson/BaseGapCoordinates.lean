import PLAStochastic.Index.KEP.Poisson.BaseGap
import PLAStochastic.ForMathlib.Probability.Hellinger.Reparametrization
import PLAStochastic.ForMathlib.Probability.Distributions.LogExponential

/-!
# Exact inverse coordinates and derivative bounds for the actual Poisson gap

The normalized cumulative intensity is the inverse of the normalized physical
gap. Both are global increasing maps. The pullback exponential density is the
actual inverse-gap law, including its complete Jacobian.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

def kepPoissonNormalizedTime {f : ℝ → ℝ} {flo fhi L : ℝ}
    (_hf : KepIntensityProfile f flo fhi L) (n x z : ℝ) : ℝ :=
  n * (kepIntensityPrimitive f (x + z / (n * f x)) - kepIntensityPrimitive f x)

theorem kepPoissonNormalizedTime_gap {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x t : ℝ) :
    kepPoissonNormalizedTime hf n x (kepPoissonNormalizedGap hf n x t) = t := by
  have hnf : n * f x ≠ 0 := (mul_pos hn (hf.f_pos x)).ne'
  unfold kepPoissonNormalizedTime kepPoissonNormalizedGap
  rw [mul_div_cancel_left₀ _ hnf, add_sub_cancel,
    kepPoissonArrival_intensity, add_sub_cancel_left, mul_div_cancel₀ _ hn.ne']

theorem kepPoissonNormalizedGap_time {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x z : ℝ) :
    kepPoissonNormalizedGap hf n x (kepPoissonNormalizedTime hf n x z) = z := by
  have hnf : n * f x ≠ 0 := (mul_pos hn (hf.f_pos x)).ne'
  have ha : kepPoissonArrival hf n x (kepPoissonNormalizedTime hf n x z) =
      x + z / (n * f x) := by
    unfold kepPoissonArrival kepPoissonNormalizedTime
    rw [mul_div_cancel_left₀ _ hn.ne', add_sub_cancel]
    exact (kepIntensityOrderIso hf).symm_apply_apply _
  unfold kepPoissonNormalizedGap
  rw [ha, add_sub_cancel_left, mul_div_cancel₀ _ hnf]

theorem kepPoissonNormalizedGap_strictMono {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) :
    StrictMono (kepPoissonNormalizedGap hf n x) := by
  intro s t hst
  have ha : kepPoissonArrival hf n x s < kepPoissonArrival hf n x t :=
    (kepIntensityOrderIso hf).symm.strictMono
      (add_lt_add_of_le_of_lt le_rfl ((div_lt_div_iff_of_pos_right hn).mpr hst))
  exact mul_lt_mul_of_pos_left (sub_lt_sub_right ha x) (mul_pos hn (hf.f_pos x))

def kepPoissonGapOrderIso {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) : ℝ ≃o ℝ where
  toEquiv :=
    { toFun := kepPoissonNormalizedGap hf n x
      invFun := kepPoissonNormalizedTime hf n x
      left_inv := kepPoissonNormalizedTime_gap hf hn x
      right_inv := kepPoissonNormalizedGap_time hf hn x }
  map_rel_iff' := (kepPoissonNormalizedGap_strictMono hf hn x).le_iff_le

theorem kepPoissonGapOrderIso_apply {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x t : ℝ) :
    kepPoissonGapOrderIso hf hn x t = kepPoissonNormalizedGap hf n x t := rfl

def kepPoissonGapDerivative {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t : ℝ) : ℝ :=
  f x / f (kepPoissonArrival hf n x t)

theorem kepPoissonGapDerivative_pos {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x t : ℝ) :
    0 < kepPoissonGapDerivative hf n x t := div_pos (hf.f_pos x) (hf.f_pos _)

theorem kepPoissonGapDerivative_measurable {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (n x : ℝ) :
    Measurable (kepPoissonGapDerivative hf n x) := by
  have hc : Continuous (kepPoissonArrival hf n x) :=
    (kepPoissonArrival_continuous hf n).comp (continuous_const.prodMk continuous_id)
  exact measurable_const.div (hf.continuous.measurable.comp hc.measurable)

def kepPoissonInverseGapDensity {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) :
    HellingerDensity (volume : Measure ℝ) :=
  positiveExpDensity.pullbackOrderIso (kepPoissonGapOrderIso hf hn x)
    (kepPoissonGapDerivative hf n x) (kepPoissonNormalizedGap_hasDerivAt hf hn x)
    (kepPoissonGapDerivative_measurable hf n x) (kepPoissonGapDerivative_pos hf n x)

theorem kepPoissonInverseGapDensity_toMeasure {f : ℝ → ℝ} {flo fhi L n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) :
    (kepPoissonInverseGapDensity hf hn x).toMeasure =
      (expMeasure 1).map (kepPoissonNormalizedTime hf n x) := by
  exact (HellingerDensity.pullbackOrderIso_toMeasure _ _ _ _ _ _).trans
    (by rw [positiveExpDensity_toMeasure]; rfl)

theorem kepPoissonGapDerivative_sub_one_bound {f : ℝ → ℝ} {flo fhi L n t : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (ht : 0 ≤ t) (x : ℝ) :
    |kepPoissonGapDerivative hf n x t - 1| ≤ (L / flo ^ 2) * t / n := by
  let y := kepPoissonArrival hf n x t
  have hy := kepPoissonArrival_ge hf hn ht x
  have hfy := hf.f_pos y
  have hlo := hf.pos
  have hL := hf.lip_nonneg
  have hnum : |f x - f y| ≤ L * (y - x) := by
    have h := hf.lip x y
    rw [abs_sub_comm x y, abs_of_nonneg (show 0 ≤ y - x from sub_nonneg.mpr hy)] at h
    exact h
  have he : |kepPoissonGapDerivative hf n x t - 1| = |f x - f y| / f y := by
    unfold kepPoissonGapDerivative
    rw [div_sub_one hfy.ne', abs_div, abs_of_pos hfy]
  rw [he]
  calc
    _ ≤ (L * (y - x)) / f y := div_le_div_of_nonneg_right hnum hfy.le
    _ ≤ (L * (y - x)) / flo := div_le_div_of_nonneg_left
      (mul_nonneg hL (sub_nonneg.mpr hy)) hlo (hf.lower y)
    _ ≤ (L * (t / (n * flo))) / flo := by
      gcongr
      exact (kepPoissonArrival_gap_bracket hf hn ht x).2
    _ = _ := by field_simp

end

end PGM
