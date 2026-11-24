import PLAStochastic.Index.CEPS.Scaled.PairComparisonRadius
import PLAStochastic.Index.CEPS.Scaled.CutoffTailPower
import PLAStochastic.Index.CEPS.Scaled.SubtractedPairError
import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegral

/-! # Complete-pair comparison with the actual physical cutoff kept fixed -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledSurrogateCutoffPair {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (b δ : ℝ) (z : ℂ) (lam : ℝ) : ℂ :=
  if |lam| ≤ δ / b then cepsScaledSurrogateSubtractedPair dom ρW N lam z b else 0

def CepsCanonDomain.cutoffPairErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  dom.subtractedPairErrorConstant (N + 1) M + dom.trueSubtractedPairConstant M / δ ^ (N + 2)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem cutoffPairErrorConstant_nonneg (N : ℕ) (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    0 ≤ dom.cutoffPairErrorConstant N M δ := by
  exact add_nonneg (subtractedPairErrorConstant_pos dom (N + 1) M).le
    (div_nonneg (trueSubtractedPairConstant_nonneg dom M) (pow_nonneg hδ.le _))

include hW hθ hD in
theorem cepsScaledCutoffPair_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {b δ δN : ℝ} (hb : 0 < b) (hδN : 0 < δN) (hδle : δN ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hδsmall : δN ≤ dom.pairComparisonScaleBase (N + 1) M / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase (N + 1) M / 4)
    (lam : ℝ) :
    ‖cepsScaledTrueCutoffPair dom ρW b δ z lam -
      cepsScaledSurrogateCutoffPair dom ρW (N + 1) b δN z lam‖ ≤
      dom.cutoffPairErrorConstant N M δN * b ^ (N + 2) *
        (1 + |lam| + Real.sqrt ‖z‖) ^ (N + 5) *
          Real.exp (-(dom.positiveBridgeDecayRate / 2) * (|lam| + Real.sqrt ‖z‖)) := by
  have hfreqpos := scaledFrequencyRadius_pos dom hD
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hCK := (subtractedPairErrorConstant_pos dom (N + 1) M).le
  have hTK := trueSubtractedPairConstant_nonneg dom M
  have hK := cutoffPairErrorConstant_nonneg dom N M hδN
  have hbase : dom.pairComparisonScaleBase (N + 1) M ≤ dom.trueDecayScaleBase M := min_le_left _ _
  have hbzT := hbz.trans_le (div_le_div_of_nonneg_right hbase (by norm_num))
  by_cases hsmall : |lam| ≤ δN / b
  · have hbig : |lam| ≤ δ / b := hsmall.trans (div_le_div_of_nonneg_right hδle hb.le)
    obtain ⟨hbT, hbS⟩ := cepsScaledPairComparison_mem_of_cutoff dom hW hθ hD (N + 1) hM0 hb hδsmall hbz hsmall
    have hbE : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius (N + 1) M lam z) := by
      simpa only [ofReal_zero, add_zero] using hbS 0 (by constructor <;> positivity)
    simp only [cepsScaledTrueCutoffPair, cepsScaledSurrogateCutoffPair, if_pos hsmall, if_pos hbig]
    apply (cepsScaledTrueSubtractedPair_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbT hbE).trans
    have hco : dom.subtractedPairErrorConstant (N + 1) M ≤ dom.cutoffPairErrorConstant N M δN :=
      le_add_of_nonneg_right (by positivity)
    gcongr
  · simp only [cepsScaledSurrogateCutoffPair, if_neg hsmall, sub_zero]
    by_cases hbig : |lam| ≤ δ / b
    · simp only [cepsScaledTrueCutoffPair, if_pos hbig]
      have hbT := cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD hM0 hb hδ hbzT hbig
      have hpow : δN ≤ b * (1 + |lam| + Real.sqrt ‖z‖) := by
        have h := (div_lt_iff₀ hb).mp (lt_of_not_ge hsmall)
        nlinarith [Real.sqrt_nonneg ‖z‖]
      have hu := cepsNorm_cutoff_tail_power_le hTK (by positivity) (Real.exp_pos _).le hδN hpow
        (cepsScaledTrueSubtractedPair_polynomial_budget dom hW hθ hD hf hη hM (by omega) lam hz hb hbT) (N + 2)
      have hco : dom.trueSubtractedPairConstant M / δN ^ (N + 2) ≤ dom.cutoffPairErrorConstant N M δN :=
        le_add_of_nonneg_left hCK
      apply hu.trans
      have hexp : N + 2 + 3 = N + 5 := by omega
      rw [hexp]
      gcongr
    · simp only [cepsScaledTrueCutoffPair, if_neg hbig, norm_zero]
      positivity

end PGM
