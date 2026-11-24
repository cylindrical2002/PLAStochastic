import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegral
import PLAStochastic.Index.CEPS.Scaled.DiscountFrequencyRadius
import PLAStochastic.Index.CEPS.Scaled.EndpointPhysicalTaylor

/-! # Fixed-cutoff actual normal expression on the mid frequency scale

The endpoint-minus-pair expression retains a fixed physical drift cutoff.
The norm bound uses the total Bochner integral and does not by itself prove
integrability, identification with the actual segment transform, or the
class-independent `Gn` interface.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueNormalExpression {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b δ : ℝ) (z : ℂ) : ℂ :=
  cepsScaledMarkedEndpoint dom ρW b z - cepsScaledMarkedDiscount ρW z b *
    ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam

def CepsCanonDomain.trueTransformFrequencyBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  min (dom.trueDecayScaleBase M / 4)
    (min (dom.trueEndpointScaleBase M / 2) (cepsDiscountFrequencyBase D θ))

def CepsCanonDomain.trueTransformFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  2 * |dom.trueEndpointConstant M| +
    (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.truePairIntegralConstant M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueTransformFrequencyBase_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < dom.trueTransformFrequencyBase M := by
  have hE : 0 < dom.trueEndpointScaleBase M := by
    have hp := trueEndpointScaleRadius_pos dom hW hθ hD hM 0
    simp only [CepsCanonDomain.trueEndpointScaleRadius, norm_zero, Real.sqrt_zero,
      add_zero] at hp
    linarith
  unfold CepsCanonDomain.trueTransformFrequencyBase
  exact lt_min (div_pos (trueDecayScaleBase_pos dom hW hθ hD hM) (by norm_num))
    (lt_min (half_pos hE) (cepsDiscountFrequencyBase_pos hD hθ))

include hθ hD in
theorem trueTransformFrequencyConstant_nonneg (M : ℝ) :
    0 ≤ dom.trueTransformFrequencyConstant M := by
  have hDsc := (cepsMarkedDiscountBound_pos hD hθ).le
  have hI := truePairIntegralConstant_nonneg dom M
  unfold CepsCanonDomain.trueTransformFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_frequency_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueTransformFrequencyBase M) :
    ‖cepsScaledTrueNormalExpression dom ρW b δ z‖ ≤
      dom.trueTransformFrequencyConstant M * (1 + Real.sqrt ‖z‖) ^ 5 *
        Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  let s := Real.sqrt ‖z‖
  let d := cepsMarkedDiscountBound D θ / (θ / 2)
  let e := Real.exp (-dom.entranceBridgeDecayRate * s)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = ‖z‖ := Real.sq_sqrt (norm_nonneg z)
  have hd : 0 ≤ d := div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le
  have hI := truePairIntegralConstant_nonneg dom M
  have hcut : b * (1 + s) < dom.trueDecayScaleBase M / 4 :=
    hbz.trans_le (min_le_left _ _)
  have hEnd : b * (1 + s) < dom.trueEndpointScaleBase M / 2 :=
    hbz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hDsc : b * (1 + s) < cepsDiscountFrequencyBase D θ :=
    hbz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hbE : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z) := by
    rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb]
    unfold CepsCanonDomain.trueEndpointScaleRadius
    apply (lt_div_iff₀ (by positivity : 0 < 2 + Real.sqrt ‖z‖)).mpr
    nlinarith [mul_nonneg hb.le hs]
  have hE := cepsScaledMarkedEndpoint_budget dom hW hθ hD hf hη hM hm (by linarith) hb hbE
  have hP := cepsScaledTrueCutoffPair_integral_budget dom hW hθ hD hf hη hM hm hb hδ hz hcut
  have hD' := cepsScaledMarkedDiscount_frequency_budget hW hθ hD (z := z) (b := (b : ℂ)) (by
    simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hb] using hDsc)
  have hc : dom.positiveBridgeDecayRate / 2 = dom.entranceBridgeDecayRate := by
    unfold CepsCanonDomain.positiveBridgeDecayRate CepsCanonDomain.entranceBridgeDecayRate
    ring
  rw [hc] at hP
  have hx : 1 ≤ 1 + s := by linarith
  have hp : 1 + s ≤ (1 + s) ^ 5 := by
    calc 1 + s = (1 + s) ^ 1 := by ring
      _ ≤ _ := pow_le_pow_right₀ hx (by norm_num : 1 ≤ 5)
  have hzP : ‖z‖ * (1 + s) ^ 3 ≤ (1 + s) ^ 5 := by
    rw [← hs2, show (1 + s) ^ 5 = (1 + s) ^ 2 * (1 + s) ^ 3 by ring]
    gcongr
    nlinarith
  unfold cepsScaledTrueNormalExpression
  calc
    _ ≤ ‖cepsScaledMarkedEndpoint dom ρW b z‖ +
        ‖cepsScaledMarkedDiscount ρW z b‖ * ‖∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam‖ :=
      (norm_sub_le _ _).trans_eq (by rw [norm_mul])
    _ ≤ dom.trueEndpointConstant M * (2 + s) * e +
        (‖z‖ * d) * (dom.truePairIntegralConstant M * (1 + s) ^ 3 * e) := by
      exact add_le_add hE (mul_le_mul hD' hP (norm_nonneg _) (mul_nonneg (norm_nonneg _) hd))
    _ ≤ (2 * |dom.trueEndpointConstant M| + d * dom.truePairIntegralConstant M) *
        (1 + s) ^ 5 * e := by
      have h1 : dom.trueEndpointConstant M * (2 + s) ≤
          2 * |dom.trueEndpointConstant M| * (1 + s) ^ 5 := by
        calc
          _ ≤ |dom.trueEndpointConstant M| * (2 + s) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ |dom.trueEndpointConstant M| * (2 * (1 + s)) := by gcongr; linarith
          _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hp (abs_nonneg (dom.trueEndpointConstant M))]
      have h2 := mul_le_mul_of_nonneg_left hzP (mul_nonneg hd hI)
      have he : 0 ≤ e := (Real.exp_pos _).le
      nlinarith [mul_le_mul_of_nonneg_right h1 he, mul_le_mul_of_nonneg_right h2 he]
    _ = _ := rfl

end PGM
