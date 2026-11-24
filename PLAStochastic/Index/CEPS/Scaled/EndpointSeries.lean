import PLAStochastic.Index.CEPS.Scaled.EndpointPhysicalTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget

/-! # Class-controlled formal series for the actual marked endpoint -/

noncomputable section
open Complex Set Metric MeasureTheory PowerSeries
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.endpointSeriesBudgetConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  complexTaylorBudgetConstant N (dom.pairPolynomialScaleBase N M / 2)
    (2 * |dom.endpointSurrogateConstant N M|) + 2 * |dom.trueEndpointErrorConstant N M|

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_seriesApprox {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hactual : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z))
    (hsmall : b * (1 + Real.sqrt ‖z‖) < dom.pairPolynomialScaleBase N M / 4) :
    SeriesApprox (cepsScaledMarkedEndpoint dom ρW b z)
      (complexTaylorSeries (cepsScaledSurrogateMarkedEndpoint dom ρW N z) 0) N b
      (dom.endpointSeriesBudgetConstant N M * (1 + Real.sqrt ‖z‖) ^ (N + 2)) := by
  let H := 1 + Real.sqrt ‖z‖
  let B := dom.pairPolynomialScaleBase N M
  have hB : 0 < B := pairPolynomialScaleBase_pos dom hW hθ hD N M
  have hH : 1 ≤ H := by dsimp [H]; linarith [Real.sqrt_nonneg ‖z‖]
  have hrad : (B / 2) / H ≤ B / (2 + Real.sqrt ‖z‖) := by
    apply (div_le_div_iff₀ (by dsimp [H]; positivity) (by positivity)).mpr
    dsimp [H]
    nlinarith [Real.sqrt_nonneg ‖z‖]
  have hsub := ball_subset_ball (x := (0 : ℂ)) hrad
  have hd := (cepsScaledSurrogateMarkedEndpoint_differentiableOn dom hW hθ hD
    hf hη hM N (by omega) hz).mono hsub
  have he : Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (entranceBridgePolynomial_constants dom hW hθ hD N M).2.le) (Real.sqrt_nonneg _))
  have hm : ∀ c ∈ ball (0 : ℂ) ((B / 2) / H),
      ‖cepsScaledSurrogateMarkedEndpoint dom ρW N z c‖ ≤
        (2 * |dom.endpointSurrogateConstant N M|) * H ^ 1 := by
    intro c hc
    have ht := cepsScaledSurrogateMarkedEndpoint_budget dom hW hθ hD hf hη hM N (by omega) hz (hsub hc)
    apply ht.trans
    calc _ ≤ |dom.endpointSurrogateConstant N M| * (2 + Real.sqrt ‖z‖) * 1 := by
          gcongr
          exact le_abs_self _
      _ ≤ _ := by dsimp [H]; nlinarith [Real.sqrt_nonneg ‖z‖, abs_nonneg (dom.endpointSurrogateConstant N M)]
  have hbs : (b : ℂ) ∈ ball (0 : ℂ) (((B / 2) / H) / 2) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb,
      show B / 2 / H / 2 = (B / 4) / H by ring]
    exact (lt_div_iff₀ (by dsimp [H]; positivity)).mpr hsmall
  have hs := seriesApprox_of_polynomial_disc (half_pos hB) hH
    (show 0 ≤ 2 * |dom.endpointSurrogateConstant N M| by positivity) 1 N hd hm hb.le hbs
  have hNdisc : (b : ℂ) ∈ ball (0 : ℂ) (B / (2 + Real.sqrt ‖z‖)) :=
    hsub (ball_subset_ball (half_le_self (div_pos (half_pos hB) (zero_lt_one.trans_le hH)).le) hbs)
  have hErr := cepsScaledTrueRegularEndpoint_error_budget dom hW hθ hD hf hη hM N hN hz
    (ball_subset_ball (trueEndpointScaleRadius_le dom M z) hactual) hNdisc
  rw [cepsScaledTrueEndpoint_eq_physical_on_disc dom hW hθ hD M hz hb hactual] at hErr
  rw [abs_of_pos hb] at hErr
  have hp : H ≤ H ^ (N + 2) := by
    calc H = H ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hH (by omega)
  have hclose : ‖cepsScaledMarkedEndpoint dom ρW b z - cepsScaledSurrogateMarkedEndpoint dom ρW N z b‖ ≤
      (2 * |dom.trueEndpointErrorConstant N M| * H ^ (N + 2)) * b ^ (N + 1) := by
    apply hErr.trans
    calc _ ≤ |dom.trueEndpointErrorConstant N M| * (2 + Real.sqrt ‖z‖) * 1 * b ^ (N + 1) := by
          gcongr
          exact le_abs_self _
      _ ≤ _ := by
        have hpoly : 2 + Real.sqrt ‖z‖ ≤ 2 * H ^ (N + 2) := by dsimp [H] at hp; linarith [Real.sqrt_nonneg ‖z‖]
        have ht := mul_le_mul_of_nonneg_left hpoly (abs_nonneg (dom.trueEndpointErrorConstant N M))
        nlinarith [mul_le_mul_of_nonneg_right ht (pow_nonneg hb.le (N + 1))]
  have h := SeriesApprox.of_close hs (show 0 ≤ 2 * |dom.trueEndpointErrorConstant N M| * H ^ (N + 2) by positivity) hclose
  simpa only [show N + 1 + 1 = N + 2 by omega, CepsCanonDomain.endpointSeriesBudgetConstant, add_mul] using h

end PGM
