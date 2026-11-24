import PLAStochastic.Index.KEP.ReferenceScale.GraphPinRemainderBounds

/-!
# Scalar norm bounds for both actual graph transfers

The compact exponential factors and the original numerator are paid before
the tail estimates. The numerator bound applies to all updated exterior pins.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepLogSlopeNorm_exp2_div_sq {G : ℝ → ℝ} (hG : Continuous G) {D : ℝ} (hD : 1 ≤ D) :
    kepLogSlopeNorm (fun s => Real.exp (2 * s) * G s / D ^ 2) ≤ 4 * kepLogSlopeNorm G := by
  have hD0 : 0 < D ^ 2 := by positivity
  have hD1 : 1 ≤ D ^ 2 := by nlinarith
  have he : (fun s => Real.exp (2 * s) * G s / D ^ 2) =
      fun s => (Real.exp (2 * s) / D ^ 2) * G s := by funext s; ring
  rw [he]
  apply kepLogSlopeNorm_mul_bound
    (F := fun s => Real.exp (2 * s) / D ^ 2)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).div_const (D ^ 2)) hG
  intro s hs
  rw [abs_of_pos (div_pos (Real.exp_pos _) hD0)]
  apply (div_le_iff₀ hD0).mpr
  have hh := (kep_logSlope_exp_bounds hs).2.2.1
  linarith

theorem kepGraphTransferredScalar_norm_bound {R R' : ℝ → ℝ}
    (hR : Continuous R) (hR' : Continuous R') {D : ℝ} (hD : 1 ≤ D) :
    kepLogSlopeNorm (kepGraphTransferredScalar D R R') ≤
      2 * (kepLogSlopeNorm R + kepLogSlopeNorm R') := by
  have hh := kepLogSlopeNorm_exp_div (G := fun s => R s + R' s) (hR.add hR') hD
  have hs := kepLogSlopeNorm_add_le hR hR'
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

theorem kepGraphSecondScalar_norm_bound {R R' R'' : ℝ → ℝ}
    (hR : Continuous R) (hR' : Continuous R') (hR'' : Continuous R'')
    {D : ℝ} (hD : 1 ≤ D) :
    kepLogSlopeNorm (fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2) ≤
      4 * (2 * kepLogSlopeNorm R + 3 * kepLogSlopeNorm R' + kepLogSlopeNorm R'') := by
  have hc : Continuous (fun s => 2 * R s + 3 * R' s + R'' s) := by fun_prop
  have hh := kepLogSlopeNorm_exp2_div_sq hc hD
  have hs := kepLogSlopeNorm_add_six (F₁ := fun s => 2 * R s) (F₂ := fun s => 3 * R' s)
    (F₃ := R'') (F₄ := fun _ => 0) (F₅ := fun _ => 0) (F₆ := fun _ => 0)
    (hR.const_mul 2) (hR'.const_mul 3) hR'' continuous_const continuous_const continuous_const
  have hzero : kepLogSlopeNorm (fun _ => (0 : ℝ)) = 0 := by
    simp only [kepLogSlopeNorm, abs_zero, integral_zero]
  simp only [add_zero, hzero, kepLogSlopeNorm_const_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)] at hs
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by norm_num))

end

end PGM
