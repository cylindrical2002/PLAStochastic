import PLAStochastic.Index.CEPS.Scaled.SlopeSubtraction

/-! # Cancellation of endpoint weights in relative errors -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsNorm_weighted_error_mul_le {E I a p w : ℂ} {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (horder : 0 ≤ ((p - a) * w).re)
    (hE : ‖E‖ ≤ C * (Real.exp (-(a * w).re) + Real.exp (-(p * w).re)))
    (hI : ‖I‖ ≤ K * Real.exp ((a * w).re)) :
    ‖E * I‖ ≤ 2 * C * K := by
  have he : (a * w).re - (p * w).re ≤ 0 := by
    rw [sub_mul, sub_re] at horder
    linarith
  have hp : Real.exp ((a * w).re - (p * w).re) ≤ 1 := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr he
  have hid : (Real.exp (-(a * w).re) + Real.exp (-(p * w).re)) * Real.exp ((a * w).re) =
      1 + Real.exp ((a * w).re - (p * w).re) := by
    rw [add_mul, ← Real.exp_add, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
    congr 1
    ring
  rw [norm_mul]
  calc
    _ ≤ (C * (Real.exp (-(a * w).re) + Real.exp (-(p * w).re))) *
        (K * Real.exp ((a * w).re)) :=
      mul_le_mul hE hI (norm_nonneg _) (by positivity)
    _ = C * K * (1 + Real.exp ((a * w).re - (p * w).re)) := by
      rw [show C * (Real.exp (-(a * w).re) + Real.exp (-(p * w).re)) *
        (K * Real.exp ((a * w).re)) = C * K *
          ((Real.exp (-(a * w).re) + Real.exp (-(p * w).re)) * Real.exp ((a * w).re)) by ring, hid]
    _ ≤ 2 * C * K := by nlinarith [mul_nonneg hC hK]

theorem cepsNormal_dslope_relative_error_identity {f g : ℂ → ℂ} {a p Δ : ℂ}
    (hga : g a ≠ 0) (hΔ : Δ ≠ 0) (hS : dslope g a p ≠ 0)
    (hid : Δ * g a = -(p - a) * dslope g a p) :
    (dslope f a p - dslope g a p) / dslope g a p =
      (((f a - g a) - (f p - g p)) * (g a)⁻¹) * Δ⁻¹ := by
  have hfd := sub_smul_dslope f a p
  have hgd := sub_smul_dslope g a p
  rw [smul_eq_mul] at hfd hgd
  field_simp [hga, hΔ, hS]
  linear_combination (dslope f a p - dslope g a p) * hid - (dslope g a p) * (hfd - hgd)

end PGM
