import PLAStochastic.Brownian.Killed.Boundary.LaplaceBounds
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The actual Laplace integral of the inward boundary kernel. -/
def leftBoundaryTransform (r k x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x

/-- Explicit candidate for that transform at an interior starting point. -/
def leftBoundaryGreen (r k x : ℝ) : ℝ := 2*Real.sinh (k*(r-x))/Real.sinh (k*r)

theorem continuous_leftBoundaryGreen (r k : ℝ) : Continuous (leftBoundaryGreen r k) := by
  change Continuous (fun x => 2*Real.sinh (k*(r-x))/Real.sinh (k*r))
  fun_prop

theorem measurable_heatBoundaryLeft (r : ℝ) : Measurable (fun p : ℝ × ℝ => heatBoundaryLeft r p.2 p.1) := by
  apply Measurable.tsum
  intro n
  dsimp only [heatSpatialMode]
  fun_prop

theorem measurable_leftBoundaryLaplaceKernel (r k : ℝ) :
    Measurable (fun p : ℝ × ℝ => Real.exp (-(k^2/2)*p.2)*heatBoundaryLeft r p.2 p.1) :=
  (show Measurable (fun p : ℝ × ℝ => Real.exp (-(k^2/2)*p.2)) by fun_prop).mul (measurable_heatBoundaryLeft r)

theorem measurable_leftBoundaryTransform (r k : ℝ) : Measurable (leftBoundaryTransform r k) :=
  (measurable_leftBoundaryLaplaceKernel r k).stronglyMeasurable.integral_prod_right'.measurable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem leftBoundaryTransform_nonneg (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) : 0 ≤ leftBoundaryTransform r k x := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_nonneg hB hr (T := ⟨t,ht.le⟩) ht hx)

theorem leftBoundaryTransform_le_green (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k x : ℝ} (hr : 0 < r) (hk : 0 < k) (hx : x ∈ Ioo 0 r) :
    leftBoundaryTransform r k x ≤ leftBoundaryGreen r k x :=
  (laplace_heatBoundaryLeft_integrable_bound hB hr hk hx).2

theorem ae_mem_Ioo_volume_Icc (r : ℝ) : ∀ᵐ x ∂volume.restrict (Icc (0 : ℝ) r), x ∈ Ioo 0 r :=
  ae_mem_Ioo_of_ae_mem_Icc_of_ac (ae_restrict_mem measurableSet_Icc) Measure.absolutelyContinuous_restrict

/-- Joint integrability in position and time follows from the proved pointwise Laplace upper bound. -/
theorem integrable_leftBoundaryLaplaceKernel (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    Integrable (fun p : ℝ × ℝ => Real.exp (-(k^2/2)*p.2)*heatBoundaryLeft r p.2 p.1)
      ((volume.restrict (Icc (0 : ℝ) r)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let F : ℝ × ℝ → ℝ := fun p => Real.exp (-(k^2/2)*p.2)*heatBoundaryLeft r p.2 p.1
  have hm : Measurable F := measurable_leftBoundaryLaplaceKernel r k
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact (ae_mem_Ioo_volume_Icc r).mono (fun x hx =>
      (laplace_heatBoundaryLeft_integrable_bound hB hr hk hx).1)
  · have hc := (continuous_leftBoundaryGreen r k).integrableOn_Icc (μ := volume) (a := 0) (b := r)
    apply hc.mono' (hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable)
    filter_upwards [ae_mem_Ioo_volume_Icc r] with x hx
    have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ F (x,t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.exp_nonneg _) (heatBoundaryLeft_nonneg hB hr
        (T := ⟨t,ht.le⟩) ht ⟨hx.1.le,hx.2.le⟩)
    have heq : (∫ t in Ioi (0 : ℝ), ‖F (x,t)‖) = leftBoundaryTransform r k x :=
      integral_congr_ae (hn.mono (fun t ht => Real.norm_of_nonneg ht))
    rw [heq, Real.norm_of_nonneg (leftBoundaryTransform_nonneg hB hr ⟨hx.1.le,hx.2.le⟩)]
    exact leftBoundaryTransform_le_green hB hr hk hx

 theorem integrableOn_leftBoundaryTransform (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) : IntegrableOn (leftBoundaryTransform r k) (Icc 0 r) :=
  (integrable_leftBoundaryLaplaceKernel hB hr hk).integral_prod_left

 theorem integral_leftBoundaryTransform_sine (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) (n : ℕ) :
    (∫ x in Icc (0 : ℝ) r, leftBoundaryTransform r k x*Real.sin (heatFrequency r n*x)) =
      heatFrequency r n/(k^2/2+heatFrequency r n^2/2) := by
  have hi := (integrable_leftBoundaryLaplaceKernel hB hr hk).mul_bdd
    (c := 1) (g := fun p : ℝ × ℝ => Real.sin (heatFrequency r n*p.1)) (by fun_prop)
    (Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _))
  have hswap := integral_integral_swap (f := fun x t : ℝ =>
    (Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x)*Real.sin (heatFrequency r n*x)) hi
  have heq (x : ℝ) : leftBoundaryTransform r k x*Real.sin (heatFrequency r n*x) =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x)*Real.sin (heatFrequency r n*x) := by
    rw [integral_mul_const]
    rfl
  simp only [heq]
  rw [hswap]
  have hin : (fun t => ∫ x in Icc (0 : ℝ) r,
      (Real.exp (-(k^2/2)*t)*heatBoundaryLeft r t x)*Real.sin (heatFrequency r n*x)) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => heatFrequency r n * Real.exp (-(k^2/2+heatFrequency r n^2/2)*t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mul_assoc]
    rw [integral_const_mul, integral_heatBoundaryLeft_sine hr ht n]
    rw [show -(k^2/2+heatFrequency r n^2/2)*t = -(k^2/2)*t + -(heatFrequency r n^2)*t/2 by ring,
      Real.exp_add]
    ring
  rw [integral_congr_ae hin, integral_const_mul,
    integral_exp_mul_Ioi (neg_neg_of_pos (heatResolventDenom_pos hr (by positivity) n)) 0]
  simp only [mul_zero, Real.exp_zero, div_neg, neg_div, neg_neg, mul_one_div]

 theorem integral_leftBoundaryGreen_sine {r k : ℝ} (hr : 0 < r) (hk : 0 < k) (n : ℕ) :
    (∫ x in Icc (0 : ℝ) r, leftBoundaryGreen r k x*Real.sin (heatFrequency r n*x)) =
      heatFrequency r n/(k^2/2+heatFrequency r n^2/2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
  have heq (x : ℝ) : leftBoundaryGreen r k x*Real.sin (heatFrequency r n*x) =
      (2/Real.sinh (k*r))*(Real.sinh (k*(r-x))*Real.sin (heatFrequency r n*x)) := by
    unfold leftBoundaryGreen
    ring
  simp only [heq]
  rw [intervalIntegral.integral_const_mul, integral_reflected_sinh_mul_sin hr hk n 0]
  simp only [sub_zero, mul_zero, Real.sin_zero, mul_zero, zero_add, Real.cos_zero, mul_one]
  have hs : Real.sinh (k*r) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne'
  field_simp

/-- One positive sine weight suffices to upgrade the Fatou upper bound to equality almost everywhere. -/
theorem leftBoundaryTransform_ae_eq_green (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    leftBoundaryTransform r k =ᵐ[volume.restrict (Icc (0 : ℝ) r)] leftBoundaryGreen r k := by
  let f : ℝ → ℝ := fun x => (leftBoundaryGreen r k x-leftBoundaryTransform r k x)*Real.sin (heatFrequency r 0*x)
  have hi : IntegrableOn f (Icc 0 r) :=
    ((continuous_leftBoundaryGreen r k).integrableOn_Icc.sub (integrableOn_leftBoundaryTransform hB hr hk)).mul_bdd
      (c := 1) (by fun_prop) (Eventually.of_forall (fun x => Real.abs_sin_le_one _))
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) r)] f := by
    filter_upwards [ae_mem_Ioo_volume_Icc r] with x hx
    exact mul_nonneg (sub_nonneg.mpr (leftBoundaryTransform_le_green hB hr hk hx)) (heatFirstSine_pos hr hx).le
  have hzero : (∫ x in Icc (0 : ℝ) r, f x) = 0 := by
    have hA := (integrableOn_leftBoundaryTransform hB hr hk).mul_bdd
      (c := 1) (g := fun x => Real.sin (heatFrequency r 0*x)) (by fun_prop)
      (Eventually.of_forall (fun x => Real.abs_sin_le_one _))
    have hG := ((continuous_leftBoundaryGreen r k).mul
      (show Continuous (fun x => Real.sin (heatFrequency r 0*x)) by fun_prop)).integrableOn_Icc (μ := volume) (a := 0) (b := r)
    change IntegrableOn (fun x => leftBoundaryGreen r k x * Real.sin (heatFrequency r 0*x)) (Icc 0 r) at hG
    simp only [f, sub_mul]
    rw [integral_sub hG hA, integral_leftBoundaryGreen_sine hr hk,
      integral_leftBoundaryTransform_sine hB hr hk, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hzero
  filter_upwards [hae, ae_mem_Ioo_volume_Icc r] with x hx hxm
  change (leftBoundaryGreen r k x-leftBoundaryTransform r k x)*Real.sin (heatFrequency r 0*x)=0 at hx
  exact (sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_right (heatFirstSine_pos hr hxm).ne')).symm

end BrownianAffine
