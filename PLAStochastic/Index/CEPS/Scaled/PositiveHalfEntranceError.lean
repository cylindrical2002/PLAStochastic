import PLAStochastic.Index.CEPS.Scaled.PositiveEntranceErrorConstants
import PLAStochastic.Index.CEPS.Scaled.TrueEntranceCorrection

/-! # Actual and surrogate half-line entrance error profiles -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

theorem cepsScaledSurrogateHalfEntrance_eq_prefactor {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsScaledSurrogateHalfEntrance dom ρW N lam z b =
      cepsScaledSurrogateMarkPrefactor dom ρW N lam z b /
        (b * z - cepsScaledSignedRoot D θ ρW lam z (-1) b) := by
  unfold cepsScaledSurrogateHalfEntrance cepsScaledSurrogateMarkPrefactor
  rw [div_mul_eq_div_div]

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledHalfEntrance_positive_comparison_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (_hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueHalfEntrance dom ρW lam z b‖ ≤ dom.positiveEntranceErrorConstant N M ∧
    ‖cepsScaledSurrogateHalfEntrance dom ρW N lam z b‖ ≤ 2 * dom.positiveEntranceErrorConstant N M ∧
    ‖cepsScaledTrueHalfEntrance dom ρW lam z b - cepsScaledSurrogateHalfEntrance dom ρW N lam z b‖ ≤
      dom.positiveEntranceErrorConstant N M * |b * lam| ^ (N + 1) := by
  let K := dom.positiveEntranceErrorConstant N M
  let e := |b * lam| ^ (N + 1)
  have hK : 0 ≤ K := (positiveEntranceErrorConstant_pos dom N M).le
  have hbound : ∀ c ∈ dom.positiveEntranceErrorConstants N M, c ≤ K :=
    fun _ hc => positiveEntranceErrorConstant_le dom N M hc
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hbP : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M /
      (1 + |lam| + Real.sqrt ‖z‖)) :=
    ball_subset_ball (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) hbD
  have hgap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD 0 M lam hlam hz hbP
  have hlow := positiveMarkerGapLower_pos dom hW hθ hD
  have hi : ‖(((b : ℂ) * z - cepsScaledSignedRoot D θ ρW lam z (-1) b)⁻¹)‖ ≤
      dom.positiveMarkerGapLower⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hlow.trans_le hgap) hlow).mpr hgap
  have ht := (cepsScaledTrueHalfEntrance_positive_budget dom hW hθ hD M lam hlam hz hbD).trans
    (hbound _ (by simp [CepsCanonDomain.positiveEntranceErrorConstants]))
  have hp := cepsScaledTrueMarkPrefactor_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN
  have hCP := trueMarkPrefactorErrorConstant_nonneg dom hD ((cepsSobolev_nonneg m η fW).trans hM) N
  have he : ‖cepsScaledTrueHalfEntrance dom ρW lam z b - cepsScaledSurrogateHalfEntrance dom ρW N lam z b‖ ≤ K * e := by
    rw [cepsScaledSurrogateHalfEntrance_eq_prefactor]
    unfold cepsScaledTrueHalfEntrance
    rw [← sub_div, div_eq_mul_inv, norm_mul]
    calc
      _ ≤ (dom.trueMarkPrefactorErrorConstant N M * e) * dom.positiveMarkerGapLower⁻¹ :=
        mul_le_mul hp hi (norm_nonneg _) (mul_nonneg hCP (pow_nonneg (abs_nonneg _) _))
      _ = (dom.trueMarkPrefactorErrorConstant N M / dom.positiveMarkerGapLower) * e := by ring
      _ ≤ K * e := mul_le_mul_of_nonneg_right
        (hbound _ (by simp [CepsCanonDomain.positiveEntranceErrorConstants])) (pow_nonneg (abs_nonneg _) _)
  have he1 : e ≤ 1 := pow_le_one₀ (abs_nonneg _)
    (cepsScaledTrueScale_drift_le_one dom hW hθ hD M lam hz hbD)
  refine ⟨ht, ?_, he⟩
  have hn := norm_sub_le (cepsScaledTrueHalfEntrance dom ρW lam z b)
    (cepsScaledTrueHalfEntrance dom ρW lam z b - cepsScaledSurrogateHalfEntrance dom ρW N lam z b)
  rw [sub_sub_cancel] at hn
  exact hn.trans ((add_le_add ht (he.trans (mul_le_of_le_one_right hK he1))).trans_eq (by ring))

end PGM
