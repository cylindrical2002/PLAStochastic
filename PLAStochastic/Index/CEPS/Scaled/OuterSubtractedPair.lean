import PLAStochastic.Index.CEPS.Scaled.OuterNegativePair
import PLAStochastic.Index.CEPS.Scaled.OuterCentralPair
import PLAStochastic.Index.CEPS.Scaled.OuterPositivePair
import PLAStochastic.Index.CEPS.Scaled.OuterPairHolomorphy

/-! # A common drift-integrable envelope for the complete outer subtracted pair -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerSubtractedPairConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  |dom.outerNegativePairConstant N M| + |dom.outerCentralPairConstant N M| + |dom.outerPositivePairConstant N M|

private theorem outer_envelope_weaken {u : ℂ} {K K' X F c d : ℝ}
    (hF : 0 ≤ F) (hc : c ≤ d) (hK : |K| ≤ K')
    (hu : ‖u‖ ≤ K * X ^ 4 * Real.exp (-d * F)) :
    ‖u‖ ≤ K' * X ^ 4 * Real.exp (-c * F) := by
  have hE : Real.exp (-d * F) ≤ Real.exp (-c * F) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hc hF]
  calc
    _ ≤ |K| * X ^ 4 * Real.exp (-d * F) := hu.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))
        (Real.exp_pos _).le)
    _ ≤ |K| * X ^ 4 * Real.exp (-c * F) := mul_le_mul_of_nonneg_left hE (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity))
      (Real.exp_pos _).le

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_outer_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ}
    (hbs : b ∈ ball (0 : ℂ) (dom.outerPairScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z b‖ ≤ dom.outerSubtractedPairConstant N M *
      (1 + |lam| + Real.sqrt ‖z‖) ^ 4 *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  have hrate : dom.positiveEntranceBridgeDecayRate ≤ dom.entranceBridgeDecayRate := min_le_left _ _
  have hbP := ball_subset_ball (min_le_left _ _) hbs
  have hbWidth := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) hbs
  have hKn : |dom.outerNegativePairConstant N M| ≤ dom.outerSubtractedPairConstant N M := by
    unfold CepsCanonDomain.outerSubtractedPairConstant
    linarith [abs_nonneg (dom.outerCentralPairConstant N M), abs_nonneg (dom.outerPositivePairConstant N M)]
  have hKc : |dom.outerCentralPairConstant N M| ≤ dom.outerSubtractedPairConstant N M := by
    unfold CepsCanonDomain.outerSubtractedPairConstant
    linarith [abs_nonneg (dom.outerNegativePairConstant N M), abs_nonneg (dom.outerPositivePairConstant N M)]
  have hKp : |dom.outerPositivePairConstant N M| ≤ dom.outerSubtractedPairConstant N M := by
    unfold CepsCanonDomain.outerSubtractedPairConstant
    linarith [abs_nonneg (dom.outerNegativePairConstant N M), abs_nonneg (dom.outerCentralPairConstant N M)]
  unfold cepsScaledSurrogateSubtractedPair
  split_ifs with hlam
  · have hu := cepsScaledSurrogatePair_outer_positive_budget dom hW hθ hD hf hη hM N hN lam hlam hz houter hbP hbWidth
    apply outer_envelope_weaken (by positivity) le_rfl hKp
    simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hu
  · by_cases hneg : lam ≤ 0
    · have hu := cepsScaledSurrogatePair_outer_negative_budget dom hW hθ hD hf hη hM N hN lam hneg hz houter hbP hbWidth
      apply outer_envelope_weaken (by positivity) hrate hKn
      simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hu
    · have habs : |lam| ≤ 1 := by rw [abs_of_pos (lt_of_not_ge hneg)]; exact (lt_of_not_ge hlam).le
      have hu := cepsScaledSurrogatePair_outer_central_budget dom hW hθ hD hf hη hM N hN lam habs hz houter hbP hbWidth
      apply outer_envelope_weaken (by positivity) hrate hKc
      simpa only [neg_mul, neg_div, div_mul_eq_mul_div] using hu

end PGM
