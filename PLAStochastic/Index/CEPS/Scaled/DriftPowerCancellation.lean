import PLAStochastic.Index.CEPS.Scaled.KernelFrequencyConstants

/-! # Cancel drift weights using two additional Taylor powers -/

noncomputable section
namespace PGM

theorem cepsDrift_square_weight_cancel_taylor {d C X E b lam : ℝ} (N : ℕ)
    (hb : 0 < b) (hl : lam ≠ 0) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hX : |lam| ≤ X)
    (h : d * |lam| ^ 2 ≤ C * X ^ 3 * E * |b * lam| ^ (N + 2)) :
    d ≤ C * b ^ (N + 2) * X ^ (N + 3) * E := by
  have hX0 : 0 ≤ X := (abs_nonneg lam).trans hX
  have hL2 : 0 < |lam| ^ 2 := pow_pos (abs_pos.mpr hl) 2
  have hpow : |b * lam| ^ (N + 2) = b ^ (N + 2) * |lam| ^ N * |lam| ^ 2 := by
    rw [abs_mul, abs_of_pos hb, mul_pow, pow_add]
    ring
  have hc : d ≤ C * b ^ (N + 2) * X ^ 3 * E * |lam| ^ N := by
    apply le_of_mul_le_mul_right (a := |lam| ^ 2) _ hL2
    apply h.trans_eq
    rw [hpow]
    ring
  calc
    d ≤ C * b ^ (N + 2) * X ^ 3 * E * |lam| ^ N := hc
    _ ≤ C * b ^ (N + 2) * X ^ 3 * E * X ^ N := by gcongr
    _ = _ := by rw [pow_add]; ring

theorem cepsDrift_taylor_value_budget {d C X E b lam : ℝ} (N : ℕ)
    (hb : 0 ≤ b) (hC : 0 ≤ C) (hE : 0 ≤ E) (hX : |lam| ≤ X)
    (h : d ≤ C * X * E * |b * lam| ^ N) :
    d ≤ C * b ^ N * X ^ (N + 1) * E := by
  have hX0 : 0 ≤ X := (abs_nonneg lam).trans hX
  rw [abs_mul, abs_of_nonneg hb, mul_pow] at h
  calc
    d ≤ C * X * E * (b ^ N * |lam| ^ N) := h
    _ ≤ C * X * E * (b ^ N * X ^ N) := by gcongr
    _ = _ := by rw [pow_succ]; ring

end PGM
