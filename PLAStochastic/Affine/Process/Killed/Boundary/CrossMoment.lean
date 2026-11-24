import PLAStochastic.Affine.Process.Killed.Boundary.CrossDerivative
import PLAStochastic.Affine.Process.Killed.Boundary.SpatialGreen
import PLAStochastic.ForMathlib.MeasureTheory.Integral.PositiveQuadrantSum

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem measurable_heatBoundaryRight (r : ℝ) :
    Measurable (fun p : ℝ × ℝ => heatBoundaryRight r p.2 p.1) := by
  apply Measurable.neg
  apply Measurable.tsum
  intro n
  dsimp only [heatSpatialMode]
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The differentiated semigroup, absolute Fubini, and the positive-quadrant identity
identify the first time moment of the true cross-boundary kernel. -/
theorem integral_laplace_heatCrossBoundary_moment (hB : IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    (∫ t in Ioi (0 : ℝ), t*Real.exp (-(k^2/2)*t)*heatCrossBoundary r t) =
      boundaryPairTransform r k := by
  let T : Measure ℝ := volume.restrict (Ioi 0)
  let Y : Measure ℝ := volume.restrict (Icc 0 r)
  let f : ℝ → ℝ := fun t => Real.exp (-(k^2/2)*t)*heatCrossBoundary r t
  let H : (ℝ × ℝ) × ℝ → ℝ := fun q =>
    (Real.exp (-(k^2/2)*q.1.1)*heatBoundaryRight r q.1.1 q.2)*
      (Real.exp (-(k^2/2)*q.1.2)*heatBoundaryLeft r q.1.2 q.2)
  have hf : Measurable f := (show Measurable (fun t : ℝ => Real.exp (-(k^2/2)*t)) by fun_prop).mul
    (measurable_heatCrossBoundary r)
  have hm : Measurable H := by
    have hR : Measurable (fun q : (ℝ × ℝ) × ℝ => heatBoundaryRight r q.1.1 q.2) := (measurable_heatBoundaryRight r).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.2,q.1.1)) (by fun_prop)
    have hL : Measurable (fun q : (ℝ × ℝ) × ℝ => heatBoundaryLeft r q.1.2 q.2) := (measurable_heatBoundaryLeft r).comp (f := fun q : (ℝ × ℝ) × ℝ => (q.2,q.1.2)) (by fun_prop)
    exact ((show Measurable (fun q : (ℝ × ℝ) × ℝ => Real.exp (-(k^2/2)*q.1.1)) by fun_prop).mul hR).mul
      ((show Measurable (fun q : (ℝ × ℝ) × ℝ => Real.exp (-(k^2/2)*q.1.2)) by fun_prop).mul hL)
  have hw : IntegrableOn (fun t => t*f t) (Ioi 0) := by
    convert! (hasDerivAt_crossBoundaryTransform hB hr (by positivity : 0 < k^2/2)).1 using 1
    funext t
    dsimp only [f]
    ring
  have hp : ∀ᵐ p : ℝ × ℝ ∂T.prod T, 0 < p.1 ∧ 0 < p.2 := by
    apply (ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact ⟨hs,ht⟩
  have hsum (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : (∫ y, H ((s,t),y) ∂Y) = f (s+t) := by
    have heq (y : ℝ) : H ((s,t),y) = Real.exp (-(k^2/2)*(s+t))*
        (heatBoundaryRight r s y*heatBoundaryLeft r t y) := by
      dsimp only [H]
      rw [show -(k^2/2)*(s+t)=-(k^2/2)*s+-(k^2/2)*t by ring, Real.exp_add]
      ring
    simp only [heq]
    rw [integral_const_mul, integral_heatBoundaryRight_mul_left hr hs ht]
  have hnorm (s t : ℝ) (hs : 0 < s) (ht : 0 < t) : (∫ y, ‖H ((s,t),y)‖ ∂Y) = f (s+t) := by
    rw [← hsum s t hs ht]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    apply Real.norm_of_nonneg
    exact mul_nonneg
      (mul_nonneg (Real.exp_nonneg _) (heatBoundaryRight_nonneg hB hr (T := ⟨s,hs.le⟩) hs hy))
      (mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_nonneg hB hr (T := ⟨t,ht.le⟩) ht hy))
  have hi : Integrable H ((T.prod T).prod Y) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hp] with p hp
      apply Continuous.integrableOn_Icc
      dsimp only [H]
      exact (continuous_const.mul (continuous_heatBoundaryRight hr hp.1)).mul
        (continuous_const.mul (continuous_heatBoundaryLeft hr hp.2))
    · apply ((integrable_positiveQuadrant_add_iff hf).mpr hw).congr
      filter_upwards [hp] with p hp
      exact (hnorm p.1 p.2 hp.1 hp.2).symm
  have hswap := integral_integral_swap (f := fun p : ℝ × ℝ => fun y : ℝ => H (p,y)) hi
  calc
    _ = ∫ u in Ioi (0 : ℝ), u*f u := by congr 1; funext u; dsimp only [f]; ring
    _ = ∫ p : ℝ × ℝ, f (p.1+p.2) ∂T.prod T :=
      (integral_positiveQuadrant_add_eq_weighted_signed hf hw).symm
    _ = ∫ p : ℝ × ℝ, ∫ y, H (p,y) ∂Y ∂T.prod T := by
      apply integral_congr_ae
      filter_upwards [hp] with p hp
      exact (hsum p.1 p.2 hp.1 hp.2).symm
    _ = ∫ y, ∫ p : ℝ × ℝ, H (p,y) ∂T.prod T ∂Y := hswap
    _ = boundaryPairTransform r k := by
      apply integral_congr_ae
      filter_upwards [ae_mem_Ioo_volume_Icc r] with y hy
      dsimp only [H]
      rw [integral_prod_mul (fun s : ℝ => Real.exp (-(k^2/2)*s)*heatBoundaryRight r s y)
        (fun t : ℝ => Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t y)]
      change (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryRight r t y)*
          (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t y) = _
      rw [integral_laplace_heatBoundaryRight hB hr hk hy, integral_laplace_heatBoundaryLeft hB hr hk hy]
      rfl

end BrownianAffine
