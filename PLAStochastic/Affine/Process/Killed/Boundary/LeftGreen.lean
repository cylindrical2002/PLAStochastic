import PLAStochastic.Brownian.Killed.Boundary.LeftTransform
import PLAStochastic.Affine.Process.Killed.InitialLimit
import Mathlib.MeasureTheory.Function.JacobianOneDim

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

 theorem integral_Ioi_translate (d : ℝ) (f : ℝ → ℝ) :
    (∫ t in Ioi (0 : ℝ), f (d+t)) = ∫ t in Ioi d, f t := by
  have him : (fun t : ℝ => d+t) '' Ioi 0 = Ioi d := by
    ext y
    constructor
    · rintro ⟨t,ht,rfl⟩
      change d < d+t
      exact lt_add_of_pos_right d ht
    · intro hy
      refine ⟨y-d, ?_, by ring⟩
      change 0 < y-d
      change d < y at hy
      exact sub_pos.mpr hy
  have hd (t : ℝ) : HasDerivAt (fun u : ℝ => d+u) 1 t := by simpa using (hasDerivAt_id t).const_add d
  have he := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun t _ => (hd t).hasDerivWithinAt) (add_right_injective d).injOn f
  rw [him] at he
  simpa only [abs_one, one_smul] using he.symm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The differentiated semigroup and genuine Fubini identify the remaining-time transform. -/
theorem integral_heatKernel_mul_leftBoundaryTransform (hB : IsBrownianReal B μ)
    {r k d : ℝ} (hr : 0 < r) (hk : 0 < k) (hd : 0 < d) (x : ℝ) :
    (∫ y in Icc (0 : ℝ) r, dirichletHeatKernel r d x y*leftBoundaryTransform r k y) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryLeft r (d+t) x := by
  have hi := (integrable_leftBoundaryLaplaceKernel hB hr hk).bdd_mul
    (c := ∑' n, heatSpatialBound r d 0 0 n)
    (f := fun p : ℝ × ℝ => dirichletHeatKernel r d x p.1)
    ((continuous_heatKernel_right hr hd x).measurable.comp measurable_fst).aestronglyMeasurable
    (Eventually.of_forall (fun p => norm_heatSpatialSeries_le hr hd 0 0 x p.1))
  have hswap := integral_integral_swap (f := fun y t : ℝ =>
    dirichletHeatKernel r d x y*(Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t y)) hi
  have heq (y : ℝ) : dirichletHeatKernel r d x y*leftBoundaryTransform r k y =
      ∫ t in Ioi (0 : ℝ), dirichletHeatKernel r d x y*(Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t y) := by
    rw [integral_const_mul]
    rfl
  simp only [heq]
  rw [hswap]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have heq' (y : ℝ) : dirichletHeatKernel r d x y*(Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t y) =
      Real.exp (-(k^2/2)*t)*(dirichletHeatKernel r d x y*heatBoundaryLeft r t y) := by ring
  simp only [heq']
  rw [integral_const_mul, integral_heatKernel_mul_boundaryLeft hr hd ht]

/-- The full boundary transform dominates every killed semigroup step applied to it. -/
theorem leftBoundaryTransform_ge_heat_step (hB : IsBrownianReal B μ)
    {r k d x : ℝ} (hr : 0 < r) (hk : 0 < k) (hd : 0 < d) (hx : x ∈ Ioo 0 r) :
    Real.exp (-(k^2/2)*d)*(∫ y in Icc (0 : ℝ) r,
      dirichletHeatKernel r d x y*leftBoundaryTransform r k y) ≤ leftBoundaryTransform r k x := by
  rw [integral_heatKernel_mul_leftBoundaryTransform hB hr hk hd, ← integral_const_mul]
  have heq (t : ℝ) : Real.exp (-(k^2/2)*d)*(Real.exp (-(k^2/2)*t)*heatBoundaryLeft r (d+t) x) =
      Real.exp (-(k^2/2)*(d+t))*heatBoundaryLeft r (d+t) x := by
    rw [show -(k^2/2)*(d+t) = -(k^2/2)*d + -(k^2/2)*t by ring, Real.exp_add]
    ring
  simp only [heq]
  rw [integral_Ioi_translate d (fun t => Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x)]
  apply setIntegral_mono_set (laplace_heatBoundaryLeft_integrable_bound hB hr hk hx).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_nonneg hB hr
      (T := ⟨t,ht.le⟩) ht ⟨hx.1.le,hx.2.le⟩)
  · exact Eventually.of_forall (fun t ht => lt_trans hd ht)

/-- Every interior starting point has the exact inward boundary transform.
The small-time killed semigroup excludes any mass loss in the Fatou boundary limit. -/
theorem leftBoundaryTransform_eq_green (hB : IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    leftBoundaryTransform r k x = leftBoundaryGreen r k x := by
  apply le_antisymm (leftBoundaryTransform_le_green hB hr hk hx)
  have hstep (n : ℕ) : Real.exp (-(k^2/2)*(reciprocalMesh n : ℝ)) *
      (∫ y in Icc (0 : ℝ) r, dirichletHeatKernel r (reciprocalMesh n) x y*leftBoundaryGreen r k y) ≤
        leftBoundaryTransform r k x := by
    have heq : (∫ y in Icc (0 : ℝ) r, dirichletHeatKernel r (reciprocalMesh n) x y*leftBoundaryGreen r k y) =
        ∫ y in Icc (0 : ℝ) r, dirichletHeatKernel r (reciprocalMesh n) x y*leftBoundaryTransform r k y := by
      apply integral_congr_ae
      filter_upwards [leftBoundaryTransform_ae_eq_green hB hr hk] with y hy
      rw [hy]
    rw [heq]
    exact leftBoundaryTransform_ge_heat_step hB hr hk (reciprocalMesh_pos n) hx
  have hmesh : Tendsto (fun n => (reciprocalMesh n : ℝ)) atTop (𝓝 0) :=
    NNReal.continuous_coe.continuousAt.tendsto.comp reciprocalMesh_tendsto_zero
  have hexp : Tendsto (fun n => Real.exp (-(k^2/2)*(reciprocalMesh n : ℝ))) atTop (𝓝 1) := by
    simpa only [Function.comp_def, mul_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp (hmesh.const_mul (-(k^2/2)))
  have hinit := tendsto_integral_heatKernel_reciprocalMesh hB hr hx (continuous_leftBoundaryGreen r k)
  have hlim := hexp.mul hinit
  simp only [one_mul] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall hstep)

 theorem integral_laplace_heatBoundaryLeft (hB : IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x) =
      2*Real.sinh (k*(r-x))/Real.sinh (k*r) := leftBoundaryTransform_eq_green hB hr hk hx

 theorem integral_laplace_heatBoundaryRight (hB : IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryRight r t x) =
      2*Real.sinh (k*x)/Real.sinh (k*r) := by
  simp only [heatBoundaryRight_reflection hr.ne']
  simpa only [sub_sub_cancel] using integral_laplace_heatBoundaryLeft hB hr hk
    (x := r-x) ⟨sub_pos.mpr hx.2,sub_lt_self _ hx.1⟩

end BrownianAffine
