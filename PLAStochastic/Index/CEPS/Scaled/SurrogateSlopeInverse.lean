import PLAStochastic.Index.CEPS.Scaled.CoordinateBudgets
import PLAStochastic.Index.CEPS.Scaled.SurrogateDividedDenominator

/-! # Inverse spatial slopes retain the lower-root exponential weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.surrogateSlopePolynomialConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  (dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) *
    (4 / cepsVarLo D) + 8 / cepsVarLo D) *
      Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem surrogateSlopePolynomialConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.surrogateSlopePolynomialConstant N M := by
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  have hvl := cepsVarLo_pos hD
  unfold CepsCanonDomain.surrogateSlopePolynomialConstant
  positivity

include hW hθ hD in
theorem cepsCanonSurrogateWeight_inverse_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) (hq : ‖q‖ ≤ dom.q₀ / 2) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖(cepsCanonSurrogateWeight dom ρW N μ q ζ)⁻¹‖ ≤
      (4 / cepsVarLo D) * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
  have hlo := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ hq hζ).1
  have hL : 0 < cepsVarLo D / 4 * Real.exp (-2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) := by
    have := cepsVarLo_pos hD
    positivity
  rw [norm_inv]
  apply ((inv_le_inv₀ (hL.trans_le hlo) hL).mpr hlo).trans_eq
  rw [mul_inv, show -2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8) =
    -(2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) by ring, Real.exp_neg, inv_inv]
  ring

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_inverse_weighted_bound {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.surrogateRegularScaleRadius N M lam z)) :
    ‖(cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹‖ ≤
      dom.surrogateSlopePolynomialConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  let B := dom.canonDriftTaylorBound N M (dom.μ₀ / 8)
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hbS := ball_subset_ball (min_le_left _ _) hb
  have hbC : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_left _ _).trans (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)) hbS
  have hvl := cepsVarLo_pos hD
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  by_cases hne : 0 < lam ^ 2 + ‖z‖
  · let a := cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
    let Gm := cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b)
    let S := cepsScaledSurrogateDenominator dom ρW N lam z b
    let Δ := cepsScaledSurrogateDelta dom ρW N lam z b
    have hid : Δ * Gm = -a * S := cepsScaledSurrogateDelta_mul_rootG dom hW hθ hD hf hη hM N hN lam hz hbC
    have ha0 : a ≠ 0 := cepsScaledRootGap_ne_zero dom hW hθ hD N M lam hz hne hbS
    have hS0 : S ≠ 0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz hb
    have hΔ0 : Δ ≠ 0 := by
      intro he
      rw [he, zero_mul] at hid
      exact mul_ne_zero (neg_ne_zero.mpr ha0) hS0 hid.symm
    have hGm0 : Gm ≠ 0 := by
      intro he
      rw [he, mul_zero] at hid
      exact mul_ne_zero (neg_ne_zero.mpr ha0) hS0 hid.symm
    have he : S⁻¹ = -a * Δ⁻¹ * Gm⁻¹ := by
      field_simp
      linear_combination hid
    obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := -1) (by norm_num) hbC
    have hF := cepsCanonSurrogateWeight_inverse_bound dom hW hθ hD hf hη hM N hN hμ.le hq.le hζ.le
    have hm : ‖Gm⁻¹‖ ≤ (4 / cepsVarLo D * Real.exp (2 * B)) *
        Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
      dsimp only [Gm, cepsScaledSurrogateG]
      rw [mul_inv, norm_mul, norm_inv, norm_exp, neg_mul, neg_re, Real.exp_neg, inv_inv]
      calc
        _ ≤ Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) *
            (4 / cepsVarLo D * Real.exp (2 * B)) :=
          mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le
        _ = _ := by ring
    have hbRad := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbC)
    have hgap : ‖a‖ ≤ dom.scaledGapBound * dom.scaledRootCoordinateBound lam z :=
      (cepsScaledRootGap_norm_le dom hW hθ hD lam hz hbC).trans
        (mul_le_mul_of_nonneg_left ((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad) hK)
    have hInv := (cepsScaledSurrogateDelta_inverse_budget dom hW hθ hD hf hη hM N hN lam hz hne).2 b hbS
    have hInvΔ : ‖Δ⁻¹‖ ≤ dom.surrogateDeltaInverseBound lam z := hInv
    have hSI := scaledCoordinateBound_mul_deltaInverse_le dom hW hθ hD lam hne
    change ‖S⁻¹‖ ≤ _
    rw [he, norm_mul, norm_mul, norm_neg]
    apply (mul_le_mul (mul_le_mul hgap hInvΔ (norm_nonneg (Δ⁻¹)) ((norm_nonneg a).trans hgap)) hm
      (norm_nonneg (Gm⁻¹)) (mul_nonneg ((norm_nonneg a).trans hgap)
        ((norm_nonneg (Δ⁻¹)).trans hInvΔ))).trans
    have hprod := mul_le_mul_of_nonneg_left hSI
      (mul_nonneg hK (div_nonneg (by norm_num : (0 : ℝ) ≤ 4) hvl.le))
    have hX : 0 ≤ X := by dsimp [X]; positivity
    have hExtra := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hvl.le) hX
    unfold CepsCanonDomain.surrogateSlopePolynomialConstant
    have hE : 0 ≤ Real.exp (2 * B) * Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by positivity
    have hh := mul_le_mul_of_nonneg_right (show
      dom.scaledGapBound * dom.scaledRootCoordinateBound lam z * dom.surrogateDeltaInverseBound lam z * (4 / cepsVarLo D) ≤
        (dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * (4 / cepsVarLo D) + 8 / cepsVarLo D) * X by nlinarith) hE
    convert hh using 1 <;> ring
  · have hl : lam = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
    have hz0 : z = 0 := norm_eq_zero.mp (by nlinarith [sq_nonneg lam, norm_nonneg z])
    subst lam
    subst z
    have hlo := cepsScaledSurrogateDenominator_origin_bound dom hW hθ hD hf hη hM N hN hb
    have hL : 0 < cepsVarLo D / 8 * Real.exp (-2 * B) := by positivity
    have hinv := (inv_le_inv₀ (hL.trans_le hlo) hL).mpr hlo
    rw [norm_inv]
    apply hinv.trans
    rw [cepsScaledSignedRoot_joint_origin hW hθ hD, zero_mul]
    simp only [zero_re, Real.exp_zero, abs_zero, norm_zero, Real.sqrt_zero, add_zero, mul_one]
    unfold CepsCanonDomain.surrogateSlopePolynomialConstant
    rw [mul_inv, show -2 * B = -(2 * B) by ring, Real.exp_neg, inv_inv]
    have hp : 0 ≤ dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * (4 / cepsVarLo D) := by positivity
    have hh := mul_nonneg hp (Real.exp_pos (2 * B)).le
    change (cepsVarLo D / 8)⁻¹ * Real.exp (2 * B) ≤
      (dom.scaledGapBound * (4 * dom.scaledCoordinateRatioBound / dom.scaledComplexSector) * (4 / cepsVarLo D) + 8 / cepsVarLo D) * Real.exp (2 * B)
    have hi : (cepsVarLo D / 8)⁻¹ = 8 / cepsVarLo D := by ring
    rw [hi]
    nlinarith

end PGM
