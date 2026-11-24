import PLAStochastic.Index.CEPS.BrownianCoeff.EntranceIntegral
import PLAStochastic.Index.CEPS.BrownianCoeff.Holomorphy

/-!
# Jointly removable Brownian entrance and kernel singularities

Continuity is proved for the analytic definitions in all parameters at the joint
zero. The half-line subtraction is absent on a neighborhood of that point.
-/

noncomputable section

open Complex Filter Topology

namespace PGM

@[simp] theorem cepsBrownianEntranceIntegral_zero : cepsBrownianEntranceIntegral 0 0 = 1 / 2 := by
  unfold cepsBrownianEntranceIntegral
  simpa using integral_one_sub_unit_complex

@[simp] theorem cepsBrownianH_zero (v : ℂ) : cepsBrownianH v 0 0 = 1 / v := by
  rw [cepsBrownianH_integral]
  simp only [Complex.ofReal_zero, zero_div, cepsBrownianSquare, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, add_zero, cepsBrownianEntranceIntegral_zero, cepsBrownianSinhc_zero, div_one]
  ring

@[simp] theorem cepsBrownianU_zero (v : ℂ) : cepsBrownianU v 0 0 = v / 2 := by
  simp [cepsBrownianU, cepsBrownianSquare]

private theorem brownian_a_continuousAt {p : ℂ × (ℝ × ℂ)} (hv : p.1 ≠ 0) :
    ContinuousAt (fun q : ℂ × (ℝ × ℂ) => (q.2.1 : ℂ) / q.1) p := by
  have ha : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => (q.2.1 : ℂ)) p := by fun_prop
  have hvfun : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => q.1) p := by fun_prop
  exact ha.div hvfun hv

private theorem brownian_square_continuousAt {p : ℂ × (ℝ × ℂ)} (hv : p.1 ≠ 0) :
    ContinuousAt (fun q : ℂ × (ℝ × ℂ) => cepsBrownianSquare q.1 q.2.1 q.2.2) p := by
  have ha := brownian_a_continuousAt hv
  have hz : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => 2 * q.2.2) p := by fun_prop
  have hvfun : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => q.1) p := by fun_prop
  exact (ha.pow 2).add (hz.div hvfun hv)

theorem cepsBrownianH_continuousAt {p : ℂ × (ℝ × ℂ)} (hv : p.1 ≠ 0)
    (hs : cepsBrownianSinhc (cepsBrownianSquare p.1 p.2.1 p.2.2) ≠ 0) :
    ContinuousAt (fun q : ℂ × (ℝ × ℂ) => cepsBrownianH q.1 q.2.1 q.2.2) p := by
  have ha := brownian_a_continuousAt hv
  have hu := brownian_square_continuousAt hv
  have hI := cepsBrownianEntranceIntegral_continuous.continuousAt.comp (ha.prodMk hu)
  have hS := cepsBrownianSinhc_differentiable.continuous.continuousAt.comp hu
  have hvfun : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => q.1) p := by fun_prop
  have hc : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => 2 / q.1) p := continuousAt_const.div hvfun hv
  have h := (hc.mul hI).div hS hs
  apply h.congr_of_eventuallyEq
  filter_upwards [] with q
  exact cepsBrownianH_integral q.1 q.2.1 q.2.2

theorem cepsBrownianU_continuousAt {p : ℂ × (ℝ × ℂ)} (hv : p.1 ≠ 0)
    (hs : cepsBrownianSinhc (cepsBrownianSquare p.1 p.2.1 p.2.2) ≠ 0) :
    ContinuousAt (fun q : ℂ × (ℝ × ℂ) => cepsBrownianU q.1 q.2.1 q.2.2) p := by
  have ha := brownian_a_continuousAt hv
  have hu := brownian_square_continuousAt hv
  have hvfun : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => q.1 / 2) p := by fun_prop
  exact (hvfun.mul ha.cexp).div
    (cepsBrownianSinhc_differentiable.continuous.continuousAt.comp hu) hs

theorem cepsBrownianKernel_joint_zero {v : ℂ} (hv : v ≠ 0) :
    ContinuousAt (fun q : ℂ × (ℝ × ℂ) => cepsBrownianKernel q.1 q.2.1 q.2.2) (v, (0, 0)) := by
  have ha := brownian_a_continuousAt (p := (v, (0, 0))) hv
  have hu := brownian_square_continuousAt (p := (v, (0, 0))) hv
  have hs : cepsBrownianSinhc (cepsBrownianSquare v 0 0) ≠ 0 := by simp [cepsBrownianSquare]
  have hH := cepsBrownianH_continuousAt (p := (v, (0, 0))) hv hs
  have hS := cepsBrownianSinhc_differentiable.continuous.continuousAt.comp hu
  have hS' := cepsBrownianSinhc_differentiable.deriv.continuous.continuousAt.comp hu
  have hfirst := (((hH.pow 2).mul ha.cexp).mul hS').div (hS.pow 2) (pow_ne_zero 2 hs)
  have hl : ∀ᶠ q : ℂ × (ℝ × ℂ) in 𝓝 (v, (0, 0)), q.2.1 < 1 := by
    have hc : ContinuousAt (fun q : ℂ × (ℝ × ℂ) => q.2.1) (v, (0, 0)) := by fun_prop
    exact hc.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  apply hfirst.congr_of_eventuallyEq
  filter_upwards [hl] with q hq
  simp only [cepsBrownianKernel, not_le.mpr hq, ite_false, add_zero]
  rfl

end PGM
