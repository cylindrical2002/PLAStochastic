import PLAStochastic.Index.CEPS.Scaled.ContourCutoff
import PLAStochastic.Index.CEPS.Scaled.ContourEndpoint
import PLAStochastic.Index.CEPS.Scaled.NormalSeries

/-! # Fixed normal expression expanded using a smaller Sobolev contour -/

noncomputable section
open Complex Set Metric MeasureTheory PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_shrink_close {m : ℕ} {η M M' : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (hM' : 0 ≤ M')
    {b δ δ' : ℝ} (hb : 0 < b) (hδ' : 0 < δ') (hδle : δ' ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hsmall : δ' ≤ (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hbz' : b * (1 + Real.sqrt ‖z‖) < (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    (hEnd : (b : ℂ) ∈ ball (0 : ℂ) ((dom.shrink σ hσ hσc).trueEndpointScaleRadius M' z))
    (hDsc : b * (1 + Real.sqrt ‖z‖) < cepsDiscountFrequencyBase D θ) (n : ℕ) :
    ‖cepsScaledTrueNormalExpression dom ρW b δ z -
      cepsScaledTrueNormalExpression (dom.shrink σ hσ hσc) ρW b δ' z‖ ≤
      ((cepsMarkedDiscountBound D θ / (θ / 2)) * dom.trueCutoffTailIntegralConstant M δ' n) *
        b ^ n * (1 + Real.sqrt ‖z‖) ^ (n + 5) := by
  let H := 1 + Real.sqrt ‖z‖
  let d := cepsMarkedDiscountBound D θ / (θ / 2)
  have hd : 0 ≤ d := div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le
  have hT := trueCutoffTailIntegralConstant_nonneg dom M hδ' n
  have hI := cepsScaledTrueCutoffPair_shrink_integral_le dom hW hθ hD hσ hσc
    hf hη hM hm hM' hb hδ' hδle hδ hsmall hz hbz hbz' n
  have hc := half_pos (positiveBridgePolynomial_constants dom hW hθ hD 0 M).2
  have he : Real.exp (-(dom.positiveBridgeDecayRate / 2) * Real.sqrt ‖z‖) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le)
      (Real.sqrt_nonneg _))
  have hI' : ‖(∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
      (∫ lam : ℝ, cepsScaledTrueCutoffPair (dom.shrink σ hσ hσc) ρW b δ' z lam)‖ ≤
        dom.trueCutoffTailIntegralConstant M δ' n * b ^ n * H ^ (n + 3) := by
    exact hI.trans (mul_le_of_le_one_right (by positivity) he)
  have hD' := cepsScaledMarkedDiscount_frequency_budget hW hθ hD (z := z) (b := (b : ℂ))
    (by simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hb] using hDsc)
  have hdn : ‖cepsScaledMarkedDiscount ρW z b‖ ≤ d * H ^ 2 := by
    apply hD'.trans
    have hs := Real.sq_sqrt (norm_nonneg z)
    have hx : ‖z‖ ≤ H ^ 2 := by dsimp [H]; nlinarith [Real.sqrt_nonneg ‖z‖]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hx hd
  unfold cepsScaledTrueNormalExpression
  rw [← cepsScaledMarkedEndpoint_shrink_eq_on_disc dom hW hθ hD hσ hσc M' hz hb hEnd]
  rw [show (cepsScaledMarkedEndpoint (dom.shrink σ hσ hσc) ρW b z -
      cepsScaledMarkedDiscount ρW z b * (∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam)) -
      (cepsScaledMarkedEndpoint (dom.shrink σ hσ hσc) ρW b z -
        cepsScaledMarkedDiscount ρW z b *
          (∫ lam : ℝ, cepsScaledTrueCutoffPair (dom.shrink σ hσ hσc) ρW b δ' z lam)) =
      -cepsScaledMarkedDiscount ρW z b *
        ((∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam) -
          (∫ lam : ℝ, cepsScaledTrueCutoffPair (dom.shrink σ hσ hσc) ρW b δ' z lam)) by ring,
    norm_mul, norm_neg]
  calc
    _ ≤ (d * H ^ 2) * (dom.trueCutoffTailIntegralConstant M δ' n * b ^ n * H ^ (n + 3)) :=
      mul_le_mul hdn hI' (norm_nonneg _) (by positivity)
    _ = _ := by
      change _ = (d * dom.trueCutoffTailIntegralConstant M δ' n) * b ^ n * H ^ (n + 5)
      rw [show n + 5 = 2 + (n + 3) by omega, pow_add]
      ring

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_shrink_seriesApprox {m m' : ℕ} {η η' M M' : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (hf' : CepsSobolevClass m' η' fW) (hη' : 2 * (dom.shrink σ hσ hσc).c₀ ≤ η')
    (hM' : cepsSobolev m' η' fW ≤ M') (N : ℕ) (hN : N + 3 ≤ m')
    {b δ δ' : ℝ} (hb : 0 < b) (hδ' : 0 < δ') (hδle : δ' ≤ δ)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hsmall : δ' ≤ (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hbz' : b * (1 + Real.sqrt ‖z‖) < (dom.shrink σ hσ hσc).trueDecayScaleBase M' / 4)
    (hEnd : (b : ℂ) ∈ ball (0 : ℂ) ((dom.shrink σ hσ hσc).trueEndpointScaleRadius M' z))
    (hDsc : b * (1 + Real.sqrt ‖z‖) < cepsDiscountFrequencyBase D θ)
    (hSeries : b * (1 + Real.sqrt ‖z‖) < (dom.shrink σ hσ hσc).normalSeriesScaleBase N M') :
    SeriesApprox (cepsScaledTrueNormalExpression dom ρW b δ z)
      (cepsScaledNormalSeries (dom.shrink σ hσ hσc) ρW N z) N b
      (((dom.shrink σ hσ hσc).normalSeriesBudgetConstant N M' δ' +
        (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.trueCutoffTailIntegralConstant M δ' (N + 1)) *
          (1 + Real.sqrt ‖z‖) ^ (2 * N + 8)) := by
  let H := 1 + Real.sqrt ‖z‖
  let T := (cepsMarkedDiscountBound D θ / (θ / 2)) *
    dom.trueCutoffTailIntegralConstant M δ' (N + 1)
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.sqrt_nonneg ‖z‖]
  have hT : 0 ≤ T := mul_nonneg
    (div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le)
    (trueCutoffTailIntegralConstant_nonneg dom M hδ' (N + 1))
  have hA := cepsScaledTrueNormalExpression_seriesApprox (dom.shrink σ hσ hσc) hW hθ hD
    hf' hη' hM' N hN hδ' hsmall hb hz hSeries
  have hclose := cepsScaledTrueNormalExpression_shrink_close dom hW hθ hD hσ hσc
    hf hη hM hm ((cepsSobolev_nonneg m' η' fW).trans hM') hb hδ' hδle hδ hsmall
    hz hbz hbz' hEnd hDsc (N + 1)
  have hp : H ^ (N + 1 + 5) ≤ H ^ (2 * N + 8) := pow_le_pow_right₀ hH (by omega)
  have hclose' : ‖cepsScaledTrueNormalExpression dom ρW b δ z -
      cepsScaledTrueNormalExpression (dom.shrink σ hσ hσc) ρW b δ' z‖ ≤
      (T * H ^ (2 * N + 8)) * b ^ (N + 1) := by
    exact hclose.trans ((mul_le_mul_of_nonneg_left hp (mul_nonneg hT (pow_nonneg hb.le _))).trans_eq
      (by ring))
  have h := hA.of_close (mul_nonneg hT (pow_nonneg (by positivity : 0 ≤ H) _)) hclose'
  convert h using 1
  dsimp [T, H]
  ring

end PGM
