import PLAStochastic.Index.CEPS.Scaled.EndpointZeroFrequencyTaylor
import PLAStochastic.Index.CEPS.Scaled.CutoffZeroFrequency
import PLAStochastic.Index.CEPS.Scaled.DiscountZeroFrequency
import PLAStochastic.Index.CEPS.Scaled.TrueTransformBudget

/-! # Actual fixed-cutoff normal slope and its genuine local frequency Taylor bound -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueNormalSlope {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (b δ : ℝ) : ℂ :=
  -cepsScaledZeroEndpoint dom ρW b - ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ 0 lam

def CepsCanonDomain.trueNormalZeroTaylorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M δ : ℝ) : ℝ :=
  32 * dom.trueEndpointZeroFrequencyConstant / dom.trueEndpointZeroFrequencyBase ^ 2 +
    (32 * (cepsMarkedDiscountBound D θ / (θ / 2)) / cepsMarkedUnitRadius D θ) *
      dom.truePairIntegralConstant M +
    (cepsMarkedDiscountBound D θ / (θ / 2)) * dom.trueCutoffZeroFrequencyConstant δ

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueNormalZeroTaylorConstant_nonneg (M : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ dom.trueNormalZeroTaylorConstant M δ := by
  have := trueEndpointZeroFrequencyConstant_nonneg dom hW hθ hD
  have := truePairIntegralConstant_nonneg dom M
  have := trueSubtractedPairZeroFrequencyConstant_nonneg dom hW hθ hD
  have := (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le
  have := (cepsMarkedUnitRadius_pos hD hθ).le
  have := (cepsMarkedDiscountBound_pos hD hθ).le
  unfold CepsCanonDomain.trueNormalZeroTaylorConstant CepsCanonDomain.trueCutoffZeroFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueNormalExpression_zero_frequency_taylor {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {b δ : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dom.trueDecayScaleBase M / 4)
    (hbs1 : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M 1 0))
    {z : ℂ} (hz : z.re = 0)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4)
    (hsmall : z ∈ ball 0 (dom.trueEndpointZeroFrequencyBase * b / 2)) :
    ‖cepsScaledTrueNormalExpression dom ρW b δ z - 1 - z * cepsScaledTrueNormalSlope dom ρW b δ‖ ≤
      dom.trueNormalZeroTaylorConstant M δ / b ^ 5 * ‖z‖ ^ 2 := by
  let d := cepsMarkedDiscountBound D θ / (θ / 2)
  let A := 32 * dom.trueEndpointZeroFrequencyConstant / dom.trueEndpointZeroFrequencyBase ^ 2
  let B := (32 * d / cepsMarkedUnitRadius D θ) * dom.truePairIntegralConstant M
  let C := d * dom.trueCutoffZeroFrequencyConstant δ
  let E := cepsScaledMarkedEndpoint dom ρW b z
  let Dm := cepsScaledMarkedDiscount ρW z b
  let Z := cepsScaledZeroEndpoint dom ρW b
  let Iz := ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ z lam
  let I0 := ∫ lam : ℝ, cepsScaledTrueCutoffPair dom ρW b δ 0 lam
  have hd : 0 ≤ d := div_nonneg (cepsMarkedDiscountBound_pos hD hθ).le (half_pos hθ).le
  have hunit : 0 < cepsMarkedUnitRadius D θ := cepsMarkedUnitRadius_pos hD hθ
  have hA : 0 ≤ A := by have := trueEndpointZeroFrequencyConstant_nonneg dom hW hθ hD; dsimp [A]; positivity
  have hB : 0 ≤ B := by
    have := (cepsMarkedUnitRadius_pos hD hθ).le
    have := truePairIntegralConstant_nonneg dom M
    dsimp [B]; positivity
  have hC : 0 ≤ C := by
    have := trueSubtractedPairZeroFrequencyConstant_nonneg dom hW hθ hD
    have := (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le
    dsimp [C, CepsCanonDomain.trueCutoffZeroFrequencyConstant]; positivity
  have hp5 : 0 < b ^ 5 := pow_pos hb 5
  have hp52 : b ^ 5 ≤ b ^ 2 := by
    rw [show b ^ 5 = b ^ 2 * b ^ 3 by ring]
    exact mul_le_of_le_one_right (sq_nonneg b) (pow_le_one₀ hb.le hb1)
  have hp51 : b ^ 5 ≤ 1 := pow_le_one₀ hb.le hb1
  have he := cepsScaledMarkedEndpoint_zero_frequency_taylor dom hW hθ hD M hb hb1 hbs1 hsmall
  have he' : ‖E - 1 + z * Z‖ ≤ A / b ^ 2 * ‖z‖ ^ 2 := he.trans_eq (by dsimp [A]; ring)
  have hzD : z ∈ ball 0 (cepsMarkedUnitRadius D θ / 2) :=
    ball_subset_ball ((div_le_div_of_nonneg_right
      (mul_le_of_le_one_right (trueEndpointZeroFrequencyBase_pos dom hW hθ hD).le hb1) (by norm_num)).trans
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))) hsmall
  have hzP : z ∈ ball 0 (dom.trueHalfZeroFrequencyBase * b / 2) :=
    ball_subset_ball (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hb.le) (by norm_num)) hsmall
  have hDn := (cepsScaledMarkedDiscount_zero_frequency_budget hW hθ hD hb.le hb1).2.1 z
    (ball_subset_ball (half_le_self (cepsMarkedUnitRadius_pos hD hθ).le) hzD)
  have hDr := cepsScaledMarkedDiscount_zero_frequency_taylor hW hθ hD hb.le hb1 hzD
  have hb0 : b * (1 + Real.sqrt ‖(0 : ℂ)‖) < dom.trueDecayScaleBase M / 4 := by
    simp only [norm_zero, Real.sqrt_zero, add_zero, mul_one]
    nlinarith [Real.sqrt_nonneg ‖z‖]
  have hI0 : ‖I0‖ ≤ dom.truePairIntegralConstant M := by
    simpa only [norm_zero, Real.sqrt_zero, add_zero, zero_mul, mul_zero, Real.exp_zero,
      one_pow, mul_one, I0] using cepsScaledTrueCutoffPair_integral_budget dom hW hθ hD
        hf hη hM hm hb hδ (by simp) hb0
  have hIr := cepsScaledTrueCutoffPair_zero_frequency_integral_sub_le dom hW hθ hD
    hf hη hM hm hb hb1 hδ0 hδ hz hbz hzP
  have heq : cepsScaledTrueNormalExpression dom ρW b δ z - 1 - z * cepsScaledTrueNormalSlope dom ρW b δ =
      (E - 1 + z * Z) - (Dm - z) * I0 - Dm * (Iz - I0) := by
    unfold cepsScaledTrueNormalExpression cepsScaledTrueNormalSlope
    dsimp [E, Dm, Z, I0, Iz]
    ring
  rw [heq]
  calc
    _ ≤ ‖E - 1 + z * Z‖ + ‖Dm - z‖ * ‖I0‖ + ‖Dm‖ * ‖Iz - I0‖ := by
      have h1 := norm_sub_le (E - 1 + z * Z) ((Dm - z) * I0)
      have h2 := norm_sub_le ((E - 1 + z * Z) - (Dm - z) * I0) (Dm * (Iz - I0))
      rw [norm_mul] at h1 h2
      linarith
    _ ≤ A / b ^ 2 * ‖z‖ ^ 2 + (32 * d / cepsMarkedUnitRadius D θ * ‖z‖ ^ 2) *
        dom.truePairIntegralConstant M + (d * ‖z‖) *
          (dom.trueCutoffZeroFrequencyConstant δ / b ^ 5 * ‖z‖) := by gcongr
    _ = (A / b ^ 2 + B + C / b ^ 5) * ‖z‖ ^ 2 := by dsimp [B, C]; ring
    _ ≤ (A / b ^ 5 + B / b ^ 5 + C / b ^ 5) * ‖z‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖z‖)
      exact add_le_add (add_le_add (div_le_div_of_nonneg_left hA hp5 hp52)
        ((le_div_iff₀ hp5).mpr (mul_le_of_le_one_right hB hp51))) le_rfl
    _ = _ := by unfold CepsCanonDomain.trueNormalZeroTaylorConstant; dsimp [A, B, C, d]; ring

end PGM
