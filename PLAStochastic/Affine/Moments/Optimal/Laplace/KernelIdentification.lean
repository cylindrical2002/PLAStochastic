import PLAStochastic.Affine.Moments.Optimal.Laplace.TimeTransforms
import PLAStochastic.Affine.Moments.Optimal.Spatial.KernelDerivatives

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem next_timeTransform_eq {a b : ℝ} (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1)
    {n : ℕ} {H J : ℝ→ℝ} (hH : ∀k,0<k→ optimalMomentTimeTransform n a b k=H k)
    (hD : ∀k,0<k→HasDerivAt H (-k*J k) k) {k : ℝ} (hk : 0<k) :
    optimalMomentTimeTransform (n+1) a b k=J k := by
  have he : H =ᶠ[𝓝 k] optimalMomentTimeTransform n a b := by
    filter_upwards [Ioi_mem_nhds hk] with x hx
    exact (hH x hx).symm
  have hd := (hasDerivAt_optimalMomentTimeTransform ha hb hk n).congr_of_eventuallyEq he
  exact mul_left_cancel₀ (neg_ne_zero.mpr hk.ne') (hd.unique (hD k hk))

theorem optimalMomentTimeTransform_eq_spatial0 {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    optimalMomentTimeTransform 0 a b k=spatialLaplaceFormula0 k a b := by
  rw [spatialLaplaceFormula0_eq,optimalMomentTimeTransform_zero ha hb hk]

theorem optimalMomentTimeTransform_eq_spatial1 {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    optimalMomentTimeTransform 1 a b k=spatialLaplaceFormula1 k a b :=
  next_timeTransform_eq ha hb (fun _ hx => optimalMomentTimeTransform_eq_spatial0 ha hb hx)
    (fun _ hx => hasDerivAt_spatialLaplaceFormula0 hx.ne' a b) hk

theorem optimalMomentTimeTransform_eq_spatial2 {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    optimalMomentTimeTransform 2 a b k=spatialLaplaceFormula2 k a b :=
  next_timeTransform_eq ha hb (fun _ hx => optimalMomentTimeTransform_eq_spatial1 ha hb hx)
    (fun _ hx => hasDerivAt_spatialLaplaceFormula1 hx.ne' a b) hk

theorem optimalMomentTimeTransform_eq_spatial3 {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) :
    optimalMomentTimeTransform 3 a b k=spatialLaplaceFormula3 k a b :=
  next_timeTransform_eq ha hb (fun _ hx => optimalMomentTimeTransform_eq_spatial2 ha hb hx)
    (fun _ hx => hasDerivAt_spatialLaplaceFormula2 hx.ne' a b) hk

end BrownianAffine
