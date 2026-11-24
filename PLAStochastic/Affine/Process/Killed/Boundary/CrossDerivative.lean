import PLAStochastic.Affine.Process.Killed.Boundary.LeftGreen
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def crossBoundaryTransform (r lam : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-lam*t)*heatCrossBoundary r t

theorem measurable_heatCrossBoundary (r : ℝ) : Measurable (heatCrossBoundary r) := by
  apply Measurable.neg
  apply Measurable.tsum
  intro n
  dsimp only [heatSpatialMode]
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem integrableOn_crossBoundaryLaplace (hB : IsBrownianReal B μ)
    {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam) :
    IntegrableOn (fun t => Real.exp (-lam*t)*heatCrossBoundary r t) (Ioi 0) := by
  have hk : 0 < Real.sqrt (2*lam) := Real.sqrt_pos.mpr (by positivity)
  have h := (laplace_heatCrossBoundary_integrable_bound hB hr hk).1
  rwa [Real.sq_sqrt (by positivity), mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h

private theorem time_exp_decay_bound {lam a t : ℝ} (hlam : 0 < lam) (ha : lam/2 ≤ a) (ht : 0 ≤ t) :
    t*Real.exp (-a*t) ≤ (4/lam)*Real.exp (-(lam/4)*t) := by
  have hc : 0 < lam/4 := by positivity
  have hbasic := Real.mul_exp_neg_le_exp_neg_one ((lam/4)*t)
  have hone : Real.exp (-1) ≤ 1 := by simp
  have htbound : t*Real.exp (-((lam/4)*t)) ≤ 4/lam := by
    apply (le_div_iff₀ hlam).mpr
    nlinarith [hbasic.trans hone]
  have hsplit : -a*t ≤ -((lam/4)*t) + -((lam/4)*t) := by nlinarith
  calc
    _ ≤ t*Real.exp (-((lam/4)*t) + -((lam/4)*t)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsplit) ht
    _ = (t*Real.exp (-((lam/4)*t)))*Real.exp (-((lam/4)*t)) := by rw [Real.exp_add]; ring
    _ ≤ _ := by simpa only [neg_mul] using mul_le_mul_of_nonneg_right htbound (Real.exp_nonneg (-((lam/4)*t)))

/-- A genuine dominated parameter derivative; its integrable majorant follows from the
proved Laplace finiteness at a smaller positive parameter. -/
theorem hasDerivAt_crossBoundaryTransform (hB : IsBrownianReal B μ)
    {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam) :
    IntegrableOn (fun t => t*Real.exp (-lam*t)*heatCrossBoundary r t) (Ioi 0) ∧
      HasDerivAt (crossBoundaryTransform r)
        (-(∫ t in Ioi (0 : ℝ), t*Real.exp (-lam*t)*heatCrossBoundary r t)) lam := by
  let F : ℝ → ℝ → ℝ := fun a t => Real.exp (-a*t)*heatCrossBoundary r t
  let F' : ℝ → ℝ → ℝ := fun a t => -t*Real.exp (-a*t)*heatCrossBoundary r t
  have hm (a : ℝ) : Measurable (F a) :=
    (show Measurable (fun t : ℝ => Real.exp (-a*t)) by fun_prop).mul (measurable_heatCrossBoundary r)
  have hm' (a : ℝ) : Measurable (F' a) := by
    exact ((measurable_id.neg.mul (by fun_prop)).mul (measurable_heatCrossBoundary r))
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ a ∈ Ioo (lam/2) (2*lam),
      ‖F' a t‖ ≤ (4/lam)*(Real.exp (-(lam/4)*t)*heatCrossBoundary r t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht a ha
    have hC : 0 ≤ heatCrossBoundary r t := heatCrossBoundary_nonneg hB hr (T := ⟨t,ht.le⟩) ht
    change ‖-t*Real.exp (-a*t)*heatCrossBoundary r t‖ ≤ _
    simp only [norm_mul, norm_neg, Real.norm_of_nonneg ht.le,
      Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg hC]
    calc
      _ ≤ ((4/lam)*Real.exp (-(lam/4)*t))*heatCrossBoundary r t :=
        mul_le_mul_of_nonneg_right (time_exp_decay_bound hlam ha.1.le ht.le) hC
      _ = _ := by ring
  have hd : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), ∀ a ∈ Ioo (lam/2) (2*lam), HasDerivAt (F · t) (F' a t) a := by
    filter_upwards [] with t a ha
    convert! ((((hasDerivAt_id a).neg).mul_const t).exp).mul_const (heatCrossBoundary r t) using 1
    simp only [F', Pi.neg_apply, id_eq]
    ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith : lam/2 < lam) (by linarith : lam < 2*lam))
    (Eventually.of_forall (fun a => (hm a).aestronglyMeasurable))
    (integrableOn_crossBoundaryLaplace hB hr hlam) (hm' lam).aestronglyMeasurable hbound
    ((integrableOn_crossBoundaryLaplace hB hr (by positivity : 0 < lam/4)).const_mul (4/lam)) hd
  constructor
  · change Integrable (fun t => t*Real.exp (-lam*t)*heatCrossBoundary r t) (volume.restrict (Ioi 0))
    convert! h.1.neg using 1
    funext t
    dsimp only [F', Pi.neg_apply]
    ring
  · change HasDerivAt (fun a => ∫ t in Ioi (0 : ℝ), Real.exp (-a*t)*heatCrossBoundary r t)
      (-(∫ t in Ioi (0 : ℝ), t*Real.exp (-lam*t)*heatCrossBoundary r t)) lam
    simpa only [F, F', neg_mul, integral_neg] using h.2

end BrownianAffine
