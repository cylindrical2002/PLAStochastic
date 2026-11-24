import PLAStochastic.Index.CEPS.Scaled.EndpointSeries
import PLAStochastic.Index.CEPS.Scaled.DiscountFrequencyTaylor
import PLAStochastic.Index.CEPS.Scaled.PairIntegralSeries
import PLAStochastic.Index.CEPS.Scaled.TrueTransformBudget

/-! # Arbitrary-order finite series for the fixed actual normal expression -/

noncomputable section
open Complex Set Metric MeasureTheory Finset PowerSeries
open PGM.WienerHopf
namespace PGM

def cepsScaledNormalSeries {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (z : ℂ) : PowerSeries ℂ :=
  complexTaylorSeries (cepsScaledSurrogateMarkedEndpoint dom ρW N z) 0 -
    complexTaylorSeries (cepsScaledMarkedDiscount ρW z) 0 * cepsScaledPairIntegralSeries dom ρW N z

def CepsCanonDomain.normalSeriesScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.trueEndpointScaleBase M / 2) (min (dom.pairPolynomialScaleBase N M / 4)
    (min (dom.pairIntegralTaylorScaleBase N M) (cepsDiscountFrequencyBase D θ / 2)))

def CepsCanonDomain.normalSeriesBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M δ : ℝ) : ℝ :=
  dom.endpointSeriesBudgetConstant N M + 3 * ((N : ℝ) + 2) ^ 2 *
    complexTaylorBudgetConstant N (cepsDiscountFrequencyBase D θ)
      (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.pairIntegralSeriesBudgetConstant N M δ

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem normalSeriesScaleBase_pos (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < dom.normalSeriesScaleBase N M := by
  have he := trueEndpointScaleRadius_pos dom hW hθ hD hM 0
  simp only [CepsCanonDomain.trueEndpointScaleRadius, norm_zero, Real.sqrt_zero, add_zero] at he
  have hP := pairPolynomialScaleBase_pos dom hW hθ hD N M
  have hI := pairIntegralTaylorScaleBase_pos dom hW hθ hD N hM
  have hDsc := cepsDiscountFrequencyBase_pos hD hθ
  unfold CepsCanonDomain.normalSeriesScaleBase
  positivity

include hW hθ hD in
theorem normalSeriesBudgetConstant_nonneg (N : ℕ) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) :
    0 ≤ dom.normalSeriesBudgetConstant N M δ := by
  have hR := pairPolynomialScaleBase_pos dom hW hθ hD N M
  have hE : 0 ≤ dom.endpointSeriesBudgetConstant N M := by
    unfold CepsCanonDomain.endpointSeriesBudgetConstant
    exact add_nonneg (complexTaylorBudgetConstant_nonneg N (half_pos hR) (by positivity)) (by positivity)
  have hDsc : 0 ≤ complexTaylorBudgetConstant N (cepsDiscountFrequencyBase D θ)
      (cepsMarkedDiscountBound D θ / (θ / 2)) :=
    complexTaylorBudgetConstant_nonneg N (cepsDiscountFrequencyBase_pos hD hθ)
      (div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le)
  have hI : 0 ≤ dom.pairIntegralSeriesBudgetConstant N M δ := by
    unfold CepsCanonDomain.pairIntegralSeriesBudgetConstant
    exact add_nonneg (actualPairIntegralTaylorConstant_nonneg dom hW hθ hD N hM hδ)
      (sum_nonneg fun j _ => pairIntegralCoeffBudgetConstant_nonneg dom hW hθ hD (N + 1) M j)
  unfold CepsCanonDomain.normalSeriesBudgetConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_seriesApprox {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 3 ≤ m)
    {δ : ℝ} (hδ : 0 < δ) (hδactual : δ ≤ dom.trueDecayScaleBase M / 4)
    {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.normalSeriesScaleBase N M) :
    SeriesApprox (cepsScaledTrueNormalExpression dom ρW b δ z)
      (cepsScaledNormalSeries dom ρW N z) N b
      (dom.normalSeriesBudgetConstant N M δ * (1 + Real.sqrt ‖z‖) ^ (2 * N + 8)) := by
  let H := 1 + Real.sqrt ‖z‖
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.sqrt_nonneg ‖z‖]
  have hB := hbz
  change b * H < min _ (min _ (min _ _)) at hB
  have hEnd := hB.trans_le (min_le_left _ _)
  have hPoly := hB.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hInt := hB.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hDsc := hB.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hactual : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb]
    unfold CepsCanonDomain.trueEndpointScaleRadius
    apply (lt_div_iff₀ (by positivity)).mpr
    dsimp [H] at hEnd
    nlinarith [mul_nonneg hb.le (Real.sqrt_nonneg ‖z‖)]
  have hb1 : b ≤ 1 := by
    have hI1 : dom.pairIntegralTaylorScaleBase N M ≤ 1 := min_le_left _ _
    have ht := hInt.trans_le hI1
    have hpos := mul_nonneg hb.le (Real.sqrt_nonneg ‖z‖)
    dsimp [H] at ht
    nlinarith
  have hE := cepsScaledMarkedEndpoint_seriesApprox dom hW hθ hD hf hη hM N (by omega)
    (by rw [hz]) hb hactual hPoly
  have hDscS := cepsScaledMarkedDiscount_seriesApprox hW hθ hD N z hb.le hDsc
  have hI := cepsScaledTrueCutoffPair_integral_seriesApprox dom hW hθ hD
    hf hη hM N hN hδ hδactual hb hz hInt
  have h := hE.sub (hDscS.mul hI hb.le hb1)
  change SeriesApprox (cepsScaledTrueNormalExpression dom ρW b δ z)
    (cepsScaledNormalSeries dom ρW N z) N b _ at h
  have hE0 : 0 ≤ dom.endpointSeriesBudgetConstant N M := by
    have hR := pairPolynomialScaleBase_pos dom hW hθ hD N M
    unfold CepsCanonDomain.endpointSeriesBudgetConstant
    exact add_nonneg (complexTaylorBudgetConstant_nonneg N (half_pos hR) (by positivity)) (by positivity)
  apply h.mono hb.le
  change dom.endpointSeriesBudgetConstant N M * H ^ (N + 2) +
    3 * ((N : ℝ) + 2) ^ 2 * (_ * H ^ (N + 3)) * (_ * H ^ (N + 5)) ≤ _
  have hp : H ^ (N + 2) ≤ H ^ (2 * N + 8) := pow_le_pow_right₀ hH (by omega)
  have ht := mul_le_mul_of_nonneg_left hp hE0
  unfold CepsCanonDomain.normalSeriesBudgetConstant
  change _ ≤ _ * H ^ (2 * N + 8)
  have hprod : H ^ (N + 3) * H ^ (N + 5) = H ^ (2 * N + 8) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = dom.endpointSeriesBudgetConstant N M * H ^ (N + 2) +
        (3 * ((N : ℝ) + 2) ^ 2 *
          complexTaylorBudgetConstant N (cepsDiscountFrequencyBase D θ)
            (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.pairIntegralSeriesBudgetConstant N M δ) *
              (H ^ (N + 3) * H ^ (N + 5)) := by ring
    _ ≤ dom.endpointSeriesBudgetConstant N M * H ^ (2 * N + 8) +
        (3 * ((N : ℝ) + 2) ^ 2 *
          complexTaylorBudgetConstant N (cepsDiscountFrequencyBase D θ)
            (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.pairIntegralSeriesBudgetConstant N M δ) *
              H ^ (2 * N + 8) := by rw [hprod]; exact add_le_add ht (le_refl _)
    _ = _ := by ring

end PGM
