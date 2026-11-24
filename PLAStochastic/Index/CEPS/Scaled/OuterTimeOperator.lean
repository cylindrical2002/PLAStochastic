import PLAStochastic.Index.CEPS.Scaled.OuterBridgeFrequency
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeSquareBudget

/-! # Weighted complete time-operator budgets on complex scale discs

Both the fixed-discount derivative and the width term are retained. The
outer-frequency constants are uniform over the input law, including zero scale.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogateBridge cepsScaledSurrogateBridgeCorrection

def cepsComplexScaledTimeOperator (lam : ℝ) (b : ℂ) (U : ℂ → ℂ) (z : ℂ) : ℂ :=
  -(1 / (1 + b * lam)) * deriv U z - b * U z

theorem cepsComplexScaled_width_bounds (lam : ℝ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖b‖ ≤ 1 ∧ 1 + b * (lam : ℂ) ≠ 0 ∧ ‖(1 + b * (lam : ℂ))⁻¹‖ ≤ 2 := by
  have hsmall := (lt_div_iff₀ (by positivity : 0 < 2 * (1 + |lam|))).mp
    (mem_ball_zero_iff.mp hb)
  have hn := norm_nonneg b
  have hl := abs_nonneg lam
  have hbl : ‖b * (lam : ℂ)‖ < 1 / 2 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    nlinarith
  have hwlo : 1 / 2 ≤ ‖1 + b * (lam : ℂ)‖ := by
    have ht := norm_sub_norm_le (1 : ℂ) (1 + b * lam)
    rw [norm_one, show (1 : ℂ) - (1 + b * lam) = -(b * lam) by ring, norm_neg] at ht
    linarith
  have hwp : 0 < ‖1 + b * (lam : ℂ)‖ := lt_of_lt_of_le (by norm_num) hwlo
  refine ⟨by nlinarith, norm_pos_iff.mp hwp, ?_⟩
  rw [norm_inv]
  exact ((inv_le_inv₀ hwp (by norm_num : (0 : ℝ) < 1 / 2)).mpr hwlo).trans_eq (by norm_num)

theorem cepsComplexScaledTimeOperator_weighted_le {lam : ℝ} {b z : ℂ} {U : ℂ → ℂ}
    {A B X p : ℝ} (hB : 0 ≤ B) (hX : 1 ≤ X)
    (hb : ‖b‖ ≤ 1) (hw : ‖(1 + b * (lam : ℂ))⁻¹‖ ≤ 2)
    (hD : ‖deriv U z‖ ≤ A * X ^ 2 * Real.exp p)
    (hU : ‖U z‖ ≤ B * X * Real.exp p) :
    ‖cepsComplexScaledTimeOperator lam b U z‖ ≤ (2 * A + B) * X ^ 2 * Real.exp p := by
  unfold cepsComplexScaledTimeOperator
  apply (norm_sub_le _ _).trans
  rw [norm_mul, norm_mul, norm_neg, one_div]
  have h1 := mul_le_mul hw hD (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul hb hU (norm_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
  have hp : X ≤ X ^ 2 := by nlinarith
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hB) (Real.exp_pos p).le
  nlinarith

def CepsCanonDomain.outerTimeOperatorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  2 * dom.outerBridgeFrequencyConstant N M + dom.surrogateBridgeWeightedConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerTimeOperatorConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.outerTimeOperatorConstant N M := by
  have := outerBridgeFrequencyConstant_pos dom hW hθ hD N M
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  unfold CepsCanonDomain.outerTimeOperatorConstant CepsCanonDomain.surrogateBridgeWeightedConstant
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateBridge_outer_timeOperator_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖cepsComplexScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z‖ ≤
      dom.outerTimeOperatorConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) := by
  obtain ⟨hb1, -, hw⟩ := cepsComplexScaled_width_bounds lam hbWidth
  have hB : 0 ≤ dom.surrogateBridgeWeightedConstant N M := by
    unfold CepsCanonDomain.surrogateBridgeWeightedConstant
    have := (surrogateSlopePolynomialConstant_pos dom hW hθ hD N M).le
    positivity
  exact cepsComplexScaledTimeOperator_weighted_le
    hB
    (by linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]) hb1 hw
    (cepsScaledSurrogateBridge_outer_frequency_budget dom hW hθ hD hf hη hM N hN lam hz houter hb)
    (cepsScaledSurrogateBridge_weighted_budget dom hW hθ hD hf hη hM N hN lam hz
      (ball_subset_ball (min_le_left _ _) hb))

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_outer_timeOperator_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖cepsComplexScaledTimeOperator lam b
      (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z‖ ≤
      dom.outerTimeOperatorConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp (-((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
          cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re) := by
  obtain ⟨hb1, -, hw⟩ := cepsComplexScaled_width_bounds lam hbWidth
  have hB : 0 ≤ dom.surrogateBridgeWeightedConstant N M := by
    unfold CepsCanonDomain.surrogateBridgeWeightedConstant
    have := (surrogateSlopePolynomialConstant_pos dom hW hθ hD N M).le
    positivity
  have hD' := cepsScaledSurrogateBridgeCorrection_outer_frequency_budget dom hW hθ hD
    hf hη hM N hN lam hz houter hb
  have he : -(2 * cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re +
      (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re =
      -((2 * cepsScaledSignedRoot D θ ρW lam z 1 b -
        cepsScaledSignedRoot D θ ρW lam z (-1) b) * (1 + b * lam)).re := by
    rw [sub_mul, sub_re]; ring
  rw [he] at hD'
  exact cepsComplexScaledTimeOperator_weighted_le
    hB
    (by linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]) hb1 hw hD'
    (cepsScaledSurrogateBridgeCorrection_weighted_budget dom hW hθ hD hf hη hM N hN lam hz
      (ball_subset_ball (min_le_left _ _) hb))

end PGM
