import PLAStochastic.Index.CEPS.Scaled.EndpointWeightedDecay
import PLAStochastic.Index.CEPS.Scaled.TrueBridgeError

/-! # Actual endpoint decay and real-scale Taylor approximation

The actual scale disc is independent of the approximation order. The
order-dependent surrogate disc enters only the Taylor comparison.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueEndpointConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (M : ℝ) : ℝ :=
  (Real.exp (2 * dom.normalLogBound) * (4 / cepsVarLo D)) * dom.trueSpatialBound M 0 *
    (dom.endpointCarrierConstant * Real.exp (2 / cepsVarLo D))

def CepsCanonDomain.trueEndpointErrorConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  (dom.doubleMarkErrorConstant N M * dom.trueSpatialBound M 0 +
    (Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D)) *
      dom.trueSpatialErrorConstant N M 0) *
        (dom.endpointCarrierConstant * Real.exp (2 / cepsVarLo D))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M 1 z)) :
    ‖cepsScaledTrueRegularEndpoint dom ρW z b‖ ≤ dom.trueEndpointConstant M *
      (2 + Real.sqrt ‖z‖) * Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hT := trueSpatialBound_nonneg dom hW hθ hD hM0 0
  have hV := cepsVarLo_pos hD
  have hP := cepsScaledTrueDoubleMarkPrefactor_budget dom hW hθ hD 0 M 1 hz
    (ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M 1 z) hb)
  have hG := cepsScaledTrueG_root_weighted_budget dom hW hθ hD hf hη hM hm 1 hz hb
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  simp only [ofReal_one, mul_one] at hG
  have hbP := ball_subset_ball (trueDenominatorScaleRadius_le_pair dom M 1 z) hb
  simp only [abs_one, one_add_one_eq_two] at hbP
  have hC := cepsScaledEndpointCarrier_weighted_budget dom hW hθ hD 0 M hz hbP
  rw [cepsScaledTrueRegularEndpoint_eq_factors, norm_mul, norm_mul]
  calc
    _ ≤ (Real.exp (2 * dom.normalLogBound) * (4 / cepsVarLo D)) *
        (dom.trueSpatialBound M 0 *
          Real.exp (-(cepsScaledSignedRoot D θ ρW 1 z 1 b * (1 + (b : ℂ))).re)) *
            ‖cepsScaledEndpointCarrier D θ ρW z b‖ := by gcongr
    _ = ((Real.exp (2 * dom.normalLogBound) * (4 / cepsVarLo D)) * dom.trueSpatialBound M 0) *
        (Real.exp (-(cepsScaledSignedRoot D θ ρW 1 z 1 b * (1 + (b : ℂ))).re) *
          ‖cepsScaledEndpointCarrier D θ ρW z b‖) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hC (by positivity)).trans_eq (by
      unfold CepsCanonDomain.trueEndpointConstant
      ring)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M 1 z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖))) :
    ‖cepsScaledTrueRegularEndpoint dom ρW z b - cepsScaledSurrogateMarkedEndpoint dom ρW N z b‖ ≤
      dom.trueEndpointErrorConstant N M * (2 + Real.sqrt ‖z‖) *
        Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) * |b| ^ (N + 1) := by
  let A := cepsScaledTrueDoubleMarkPrefactor dom ρW 1 z b
  let a := cepsScaledSurrogateDoubleMarkPrefactor dom ρW N 1 z b
  let B := cepsScaledTrueG dom ρW 1 z b (cepsScaledSignedRoot D θ ρW 1 z 1 b)
  let g := cepsScaledSurrogateG dom ρW N 1 z b (cepsScaledSignedRoot D θ ρW 1 z 1 b)
  let p := (cepsScaledSignedRoot D θ ρW 1 z 1 b * (1 + (b : ℂ))).re
  let T := dom.trueSpatialBound M 0
  let P := Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D)
  let E := dom.trueSpatialErrorConstant N M 0
  let C := dom.doubleMarkErrorConstant N M
  let e := |b| ^ (N + 1)
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hT : 0 ≤ T := trueSpatialBound_nonneg dom hW hθ hD hM0 0
  have hP : 0 ≤ P := by have := cepsVarLo_pos hD; dsimp [P]; positivity
  have hE : 0 ≤ E := trueSpatialErrorConstant_nonneg dom hW hθ hD hM0 N 0
  have hC : 0 ≤ C := doubleMarkErrorConstant_nonneg dom hD hM0 N
  have he : 0 ≤ e := pow_nonneg (abs_nonneg _) _
  have hbN' : (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M /
      (1 + |(1 : ℝ)| + Real.sqrt ‖z‖)) := by
    simpa only [abs_one, one_add_one_eq_two] using hbN
  have hbE := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M 1 z).2 hbN'
  have hAA : ‖A - a‖ ≤ C * e := by
    simpa only [mul_one] using
      cepsScaledTrueDoubleMarkPrefactor_error_budget dom hW hθ hD hf hη hM N hN 1 hz hbE
  have ha : ‖a‖ ≤ P := cepsScaledSurrogateDoubleMarkPrefactor_budget dom hW hθ hD hf hη hM
    N (by omega) 1 hz hbE
  have hB : ‖B‖ ≤ T * Real.exp (-p) := by
    simpa only [ofReal_one, mul_one] using
      cepsScaledTrueG_root_weighted_budget dom hW hθ hD hf hη hM (by omega) 1 hz hb
        (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have hBg : ‖B - g‖ ≤ E * Real.exp (-p) * e := by
    simpa only [iteratedDeriv_zero, ofReal_one, mul_one, CepsCanonDomain.trueSpatialErrorConstant] using!
      cepsScaledTrueG_spatial_error_budget dom hW hθ hD hf hη hM N hN 1 hz hbE 0
        (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M 1 hz hbE (by norm_num))
  have hprod : ‖A * B - a * g‖ ≤ (C * T + P * E) * Real.exp (-p) * e := by
    rw [show A * B - a * g = (A - a) * B + a * (B - g) by ring]
    calc
      _ ≤ ‖(A - a) * B‖ + ‖a * (B - g)‖ := norm_add_le _ _
      _ = ‖A - a‖ * ‖B‖ + ‖a‖ * ‖B - g‖ := by rw [norm_mul, norm_mul]
      _ ≤ (C * e) * (T * Real.exp (-p)) + P * (E * Real.exp (-p) * e) := by gcongr
      _ = _ := by ring
  have hw := cepsScaledEndpointCarrier_weighted_budget dom hW hθ hD N M hz hbN
  rw [cepsScaledTrueRegularEndpoint_eq_factors, cepsScaledSurrogateMarkedEndpoint_eq_factors,
    ← sub_mul, norm_mul]
  change ‖A * B - a * g‖ * ‖cepsScaledEndpointCarrier D θ ρW z b‖ ≤ _
  calc
    _ ≤ ((C * T + P * E) * Real.exp (-p) * e) * ‖cepsScaledEndpointCarrier D θ ρW z b‖ :=
      mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
    _ = ((C * T + P * E) * e) *
        (Real.exp (-p) * ‖cepsScaledEndpointCarrier D θ ρW z b‖) := by ring
    _ ≤ _ := (mul_le_mul_of_nonneg_left hw (by positivity)).trans_eq (by
      unfold CepsCanonDomain.trueEndpointErrorConstant
      dsimp only [C, T, P, E, e]
      ring)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M 1 z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) ((dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledTrueRegularEndpoint dom ρW z b -
      complexTaylorSum (cepsScaledSurrogateMarkedEndpoint dom ρW N z) (N + 1) 0 b‖ ≤
        (dom.trueEndpointErrorConstant N M * (2 + Real.sqrt ‖z‖) *
          Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) +
            dom.endpointSurrogateTaylorBound N M (N + 1) z) * |b| ^ (N + 1) := by
  have hbN' := ball_subset_ball (half_le_self (div_nonneg
    (pairPolynomialScaleBase_pos dom hW hθ hD N M).le (by positivity))) hbN
  have he := cepsScaledTrueRegularEndpoint_error_budget dom hW hθ hD hf hη hM N hN hz hb hbN'
  have ht := cepsScaledSurrogateMarkedEndpoint_taylor_le dom hW hθ hD hf hη hM N (by omega) hz (N + 1) hbN
  rw [norm_real, Real.norm_eq_abs] at ht
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add he ht).trans_eq (by ring))

end PGM
