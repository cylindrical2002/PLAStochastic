import PLAStochastic.Brownian.Killed.Width.UniformQuotient

/-! # Analytic double-boundary limit for ordered first-contact kernels

The identification with the actual ordered-extrema law is a separate probabilistic step.
The second time parameter is the elapsed time between the two contacts.
-/
noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The unnormalized kernel in the exact two-boundary first-contact convolution. -/
def orderedContactLayerKernel (r e d T s v x z : ℝ) : ℝ :=
  heatBoundaryLeft r s x / 2 * heatBoundaryRight (r+e) v e / 2 *
    dirichletHeatKernel (r+e+d) (T-s-v) (r+e) (z+e)

/-- The normalized layer, written as a product of the actual boundary quotients. -/
def orderedContactLayerQuotient (r e d T s v x z : ℝ) : ℝ :=
  heatBoundaryLeft r s x * (heatBoundaryRight (r+e) v e / e) *
    (dirichletHeatKernel (r+e+d) (T-s-v) (r+e) (z+e) / d) / 4

/-- The candidate ordered-contact density kernel in first-time / elapsed-time coordinates. -/
def orderedContactDensityKernel (r T s v x z : ℝ) : ℝ :=
  heatBoundaryLeft r s x * heatCrossBoundary r v * heatBoundaryRight r (T-s-v) z / 4

theorem orderedContactLayerQuotient_eq (r e d T s v x z : ℝ) :
    orderedContactLayerQuotient r e d T s v x z =
      orderedContactLayerKernel r e d T s v x z / (e*d) := by
  unfold orderedContactLayerQuotient orderedContactLayerKernel
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- All six nonperturbation parameters may vary jointly in the interior time region. -/
theorem tendsto_orderedContactDensityKernel {ι : Type*} {l : Filter ι}
    {r T s v x z : ι → ℝ} {r₀ T₀ s₀ v₀ x₀ z₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (hT : Tendsto T l (𝓝 T₀))
    (hs : Tendsto s l (𝓝 s₀)) (hv : Tendsto v l (𝓝 v₀))
    (hx : Tendsto x l (𝓝 x₀)) (hz : Tendsto z l (𝓝 z₀))
    (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) (hv₀ : 0 < v₀) (hrem : s₀+v₀ < T₀) :
    Tendsto (fun i => orderedContactDensityKernel (r i) (T i) (s i) (v i) (x i) (z i)) l
      (𝓝 (orderedContactDensityKernel r₀ T₀ s₀ v₀ x₀ z₀)) := by
  have hA := tendsto_heatSpatialSeries_joint hr hs hx (tendsto_const_nhds (x := (0 : ℝ))) hr₀ hs₀ 0 1
  have hC := (tendsto_heatSpatialSeries_joint hr hv hr (tendsto_const_nhds (x := (0 : ℝ))) hr₀ hv₀ 1 1).neg
  have hR := (tendsto_heatSpatialSeries_joint hr ((hT.sub hs).sub hv) hz hr hr₀
    (by linarith : 0 < T₀-s₀-v₀) 0 1).neg
  exact ((hA.mul hC).mul hR).div_const 4

/-- The true two-boundary quotient converges jointly, without freezing other parameters. -/
theorem tendsto_orderedContactLayerQuotient {ι : Type*} {l : Filter ι}
    {r e d T s v x z : ι → ℝ} {r₀ T₀ s₀ v₀ x₀ z₀ : ℝ}
    (hr : Tendsto r l (𝓝 r₀)) (he : Tendsto e l (𝓝 0)) (hd : Tendsto d l (𝓝 0))
    (hT : Tendsto T l (𝓝 T₀)) (hs : Tendsto s l (𝓝 s₀)) (hv : Tendsto v l (𝓝 v₀))
    (hx : Tendsto x l (𝓝 x₀)) (hz : Tendsto z l (𝓝 z₀))
    (hr₀ : 0 < r₀) (hs₀ : 0 < s₀) (hv₀ : 0 < v₀) (hrem : s₀+v₀ < T₀)
    (hepos : ∀ᶠ i in l, 0 < e i) (hdpos : ∀ᶠ i in l, 0 < d i) :
    Tendsto (fun i => orderedContactLayerQuotient (r i) (e i) (d i) (T i) (s i) (v i) (x i) (z i)) l
      (𝓝 (orderedContactDensityKernel r₀ T₀ s₀ v₀ x₀ z₀)) := by
  have hA := tendsto_heatSpatialSeries_joint hr hs hx (tendsto_const_nhds (x := (0 : ℝ))) hr₀ hs₀ 0 1
  have hre : Tendsto (fun i => r i+e i) l (𝓝 r₀) := by simpa only [add_zero] using hr.add he
  have hred : Tendsto (fun i => r i+e i+d i) l (𝓝 r₀) := by simpa only [add_zero] using hre.add hd
  have hze : Tendsto (fun i => z i+e i) l (𝓝 z₀) := by simpa only [add_zero] using hz.add he
  have hC := tendsto_heatBoundaryRight_left_quotient hre hv he hr₀ hv₀ hepos
  have hR := tendsto_dirichletHeatKernel_right_quotient hred ((hT.sub hs).sub hv) hre hze hr₀
    (by linarith : 0 < T₀-s₀-v₀) (hdpos.mono (fun i hi => lt_add_of_pos_right _ hi))
  simpa only [orderedContactLayerQuotient, orderedContactDensityKernel, heatBoundaryLeft,
    add_sub_cancel_left] using! ((hA.mul hC).mul hR).div_const 4

end BrownianAffine
