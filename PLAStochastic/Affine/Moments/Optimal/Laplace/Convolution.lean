import PLAStochastic.Affine.Process.Killed.WidthScaling
import PLAStochastic.Brownian.Killed.OrderedBoundary.Integral

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The unit-width three-piece path kernel, weighted by the gap between extrema. -/
def optimalMomentConvolutionIntegrand (a b T v w : ℝ) : ℝ :=
  heatBoundaryLeft 1 v a * (w*heatCrossBoundary 1 w) * heatBoundaryRight 1 (T-v-w) b

/-- The manuscript's unit-width time convolution. -/
def optimalMomentConvolution (a b T : ℝ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), ∫ w in Ioo (0 : ℝ) (T-v), optimalMomentConvolutionIntegrand a b T v w

/-- The nonnegative version retains Tonelli identities before proving finiteness. -/
def optimalMomentConvolutionENN (a b T : ℝ) : ℝ≥0∞ :=
  ∫⁻ v in Ioi (0 : ℝ), ∫⁻ w in Ioo (0 : ℝ) (T-v),
    ENNReal.ofReal (optimalMomentConvolutionIntegrand a b T v w)

theorem measurable_optimalMomentConvolutionIntegrand :
    Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ =>
      optimalMomentConvolutionIntegrand p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hA := measurable_heatSpatialSeries_comp (measurable_const (a := (1:ℝ)))
    (by fun_prop : Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.2.2.2.1))
    (by fun_prop : Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.1)) (measurable_const (a := (0:ℝ))) 0 1
  have hC := (measurable_heatSpatialSeries_comp (measurable_const (a := (1:ℝ)))
    (by fun_prop : Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.2.2.2.2))
    (measurable_const (a := (1:ℝ))) (measurable_const (a := (0:ℝ))) 1 1).neg
  have hR := (measurable_heatSpatialSeries_comp (measurable_const (a := (1:ℝ)))
    (by fun_prop : Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.2.2.1-p.2.2.2.1-p.2.2.2.2))
    (by fun_prop : Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.2.1))
    (measurable_const (a := (1:ℝ))) 0 1).neg
  exact (hA.mul ((by fun_prop : Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => p.2.2.2.2)).mul hC)).mul hR

theorem optimalMomentConvolutionIntegrand_pos {a b T v w : ℝ}
    (ha : a ∈ Ioo 0 1) (hb : b ∈ Ioo 0 1) (hv : 0 < v) (hw : w ∈ Ioo 0 (T-v)) :
    0 < optimalMomentConvolutionIntegrand a b T v w := by
  exact mul_pos (mul_pos (heatBoundaryLeft_strictlyPositive (by norm_num) hv ha)
    (mul_pos hw.1 (heatCrossBoundary_strictlyPositive (by norm_num) hw.1)))
    (heatBoundaryRight_strictlyPositive (by norm_num) (by linarith [hw.2]) hb)

theorem measurable_optimalMomentConvolutionENN :
    Measurable (fun p : ℝ × ℝ × ℝ => optimalMomentConvolutionENN p.1 p.2.1 p.2.2) := by
  let F : ((ℝ × ℝ × ℝ) × ℝ) × ℝ → ℝ≥0∞ := fun p =>
    (Ioo 0 (p.1.1.2.2-p.1.2)).indicator
      (fun w => ENNReal.ofReal (optimalMomentConvolutionIntegrand p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 w)) p.2
  have hm : Measurable F := by
    have hk := measurable_optimalMomentConvolutionIntegrand.comp (f := fun p : ((ℝ × ℝ × ℝ) × ℝ) × ℝ =>
      (p.1.1.1,p.1.1.2.1,p.1.1.2.2,p.1.2,p.2)) (by fun_prop)
    have hs : MeasurableSet {p : ((ℝ × ℝ × ℝ) × ℝ) × ℝ | p.2 ∈ Ioo 0 (p.1.1.2.2-p.1.2)} := by
      simp only [mem_Ioo]
      measurability
    exact hk.ennreal_ofReal.indicator hs
  have hi : Measurable (fun p : (ℝ × ℝ × ℝ) × ℝ => ∫⁻ w, F (p,w)) := hm.lintegral_prod_right'
  have ho : Measurable (fun p : ℝ × ℝ × ℝ => ∫⁻ v in Ioi (0:ℝ), ∫⁻ w, F ((p,v),w)) :=
    hi.lintegral_prod_right'
  convert! ho using 1
  funext p
  unfold optimalMomentConvolutionENN
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro v hv
  exact (lintegral_indicator measurableSet_Ioo _).symm

end BrownianAffine
