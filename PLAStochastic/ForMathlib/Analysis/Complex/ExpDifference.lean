import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Uniform exponential differences on a bounded complex disc -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem norm_cexp_sub_cexp_le {a b : ℂ} {M : ℝ} (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖exp a - exp b‖ ≤ Real.exp M * ‖a - b‖ := by
  have hd : ∀ z ∈ closedBall (0 : ℂ) M, DifferentiableAt ℂ exp z :=
    fun z _ => (hasDerivAt_exp z).differentiableAt
  have hh := (convex_closedBall (0 : ℂ) M).norm_image_sub_le_of_norm_deriv_le hd
    (fun z hz => by
      rw [(hasDerivAt_exp z).deriv, norm_exp]
      exact Real.exp_le_exp.mpr ((re_le_norm z).trans (mem_closedBall_zero_iff.mp hz)))
    (mem_closedBall_zero_iff.mpr hb) (mem_closedBall_zero_iff.mpr ha)
  exact hh

end PGM
