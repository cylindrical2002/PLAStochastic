import PLAStochastic.Index.CEPS.Scaled.FrequencyShift

/-! # Rightward shifts retain the actual frequency scale disc -/

noncomputable section
open Complex Set Metric
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hD : 0 < D)

include hD in
theorem cepsScaledTrueDecay_shift_mem_frequency (M lam : ℝ) (z : ℂ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) {s : ℝ}
    (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    b ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam (z + (s : ℂ))) := by
  have hf := frequencyShiftFactor_pos dom
  have ht := (lt_div_iff₀ (mul_pos hf (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖))).mp
    ((mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _))
  apply mem_ball_zero_iff.mpr
  apply (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z + (s : ℂ)‖)).mpr
  exact (mul_le_mul_of_nonneg_left (cepsFrequency_polynomial_shift dom hD lam z hs)
    (norm_nonneg b)).trans_lt ht

end PGM
