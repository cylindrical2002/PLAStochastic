import PLAStochastic.Index.CEPS.Scaled.TrueSubtractedPair

/-! # Extracting scale powers outside a positive physical cutoff -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_cutoff_tail_power_le {u : ℂ} {K X E b δ : ℝ}
    (hK : 0 ≤ K) (hX : 0 ≤ X) (hE : 0 ≤ E) (hδ : 0 < δ)
    (hscale : δ ≤ b * X) (hu : ‖u‖ ≤ K * X ^ 3 * E) (n : ℕ) :
    ‖u‖ ≤ (K / δ ^ n) * b ^ n * X ^ (n + 3) * E := by
  have hp := pow_le_pow_left₀ hδ.le hscale n
  have hco : K ≤ (K / δ ^ n) * b ^ n * X ^ n := by
    calc
      _ = (K / δ ^ n) * δ ^ n := (div_mul_cancel₀ K (pow_pos hδ n).ne').symm
      _ ≤ (K / δ ^ n) * (b * X) ^ n := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [mul_pow]; ring
  apply hu.trans
  calc
    _ ≤ ((K / δ ^ n) * b ^ n * X ^ n) * X ^ 3 * E :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hco (pow_nonneg hX _)) hE
    _ = _ := by rw [pow_add]; ring

end PGM
