import PLAStochastic.Index.CEPS.Scaled.TrueSpatialBudget
import PLAStochastic.Index.CEPS.Scaled.TrueInverseError
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeWeighted
import PLAStochastic.Index.CEPS.Scaled.WeightedProductError

/-! # Weighted actual bridge budgets and surrogate errors

The actual denominator budget uses its order-independent disc. The
surrogate disc is a separate approximation domain for the requested order.
Every estimate preserves the positive-root weight and all root collisions.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueBridge {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  -cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b) *
    cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z (-1) b) /
      cepsScaledTrueDenominator dom ρW lam z b

def CepsCanonDomain.trueBridgeWeightedConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  (dom.trueSpatialBound M 0) ^ 2 * (2 * dom.surrogateSlopePolynomialConstant 0 M)

def CepsCanonDomain.trueBridgeErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  (dom.trueSpatialErrorConstant N M 0 *
    (dom.trueSpatialBound M 0 + v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) +
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) ^ 2 *
        dom.trueDenominatorRelativeConstant N M) * (2 * dom.surrogateSlopePolynomialConstant 0 M)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueG_root_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z))
    {sign : ℂ} (hsign : ‖sign‖ ≤ 1) :
    ‖cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤
      dom.trueSpatialBound M 0 *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) := by
  simpa only [iteratedDeriv_zero] using!
    cepsScaledTrueG_spatial_budget dom hW hθ hD hf hη hM hm lam hz hb 0
      (entranceScaleCurve_root_norm_le_half dom hW hθ hD 0 M lam hz
        (ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb) hsign)

include hW hθ hD in
theorem cepsScaledTrueBridge_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueBridge dom ρW lam z b‖ ≤ dom.trueBridgeWeightedConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) := by
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hT := trueSpatialBound_nonneg dom hW hθ hD hM0 0
  have hK := (surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M).le
  have hp := cepsScaledTrueG_root_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have hm' := cepsScaledTrueG_root_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)
  have hs := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
  have hn := cepsNorm_weighted_three_product_le hT hT
    (show 0 ≤ 2 * dom.surrogateSlopePolynomialConstant 0 M * (1 + |lam| + Real.sqrt ‖z‖) by positivity)
    hp hm' hs
  unfold cepsScaledTrueBridge
  rw [neg_mul, div_eq_mul_inv, neg_mul, norm_neg]
  exact hn.trans_eq (by unfold CepsCanonDomain.trueBridgeWeightedConstant; ring)

include hW hθ hD in
theorem cepsScaledTrueBridge_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueBridge dom ρW lam z b - cepsScaledSurrogateBridge dom ρW N lam z b‖ ≤
      dom.trueBridgeErrorConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + (b : ℂ) * lam)).re) *
          |b * lam| ^ (N + 1) := by
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  let w : ℂ := 1 + (b : ℂ) * lam
  let A := cepsScaledTrueG dom ρW lam z b
  let G := cepsScaledSurrogateG dom ρW N lam z (b : ℂ)
  let I := (cepsScaledTrueDenominator dom ρW lam z b)⁻¹
  let J := (cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let e := |b * lam| ^ (N + 1)
  let T := dom.trueSpatialBound M 0
  let B := v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  let E := dom.trueSpatialErrorConstant N M 0
  let C := dom.trueDenominatorRelativeConstant N M
  let K := 2 * dom.surrogateSlopePolynomialConstant 0 M
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hT : 0 ≤ T := trueSpatialBound_nonneg dom hW hθ hD hM0 0
  have hB : 0 ≤ B := mul_nonneg (CepsCanonDomain.v_pos hW hθ hD).le (Real.exp_pos _).le
  have hE : 0 ≤ E := trueSpatialErrorConstant_nonneg dom hW hθ hD hM0 N 0
  have hC : 0 ≤ C := trueDenominatorRelativeConstant_nonneg dom hW hθ hD hM0 N
  have hK : 0 ≤ K := by dsimp [K]; have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have he : 0 ≤ e := pow_nonneg (abs_nonneg _) _
  have hbC : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_right _ _).trans
      (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbN
  have htrue : ∀ sign : ℂ, ‖sign‖ ≤ 1 →
      ‖A (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤ T *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * w).re) :=
    fun _ hsign => cepsScaledTrueG_root_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hb hsign
  have hsur : ∀ sign : ℂ, ‖sign‖ ≤ 1 →
      ‖G (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤ B *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * w).re) :=
    fun _ hsign => cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N (by omega) lam hz hsign hbC
  have herr : ∀ sign : ℂ, ‖sign‖ ≤ 1 →
      ‖A (cepsScaledSignedRoot D θ ρW lam z sign b) - G (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤
        (E * e) * Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * w).re) := by
    intro sign hsign
    have h := cepsScaledTrueG_spatial_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN 0
      (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hbN hsign)
    simpa only [iteratedDeriv_zero, CepsCanonDomain.trueSpatialErrorConstant, mul_assoc,
      mul_comm (Real.exp _) (|b * lam| ^ (N + 1))] using! h
  have hI : ‖I‖ ≤ (K * X) * Real.exp ((a * w).re) :=
    cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hb
  have hIJ : ‖I - J‖ ≤ (C * K * X * e) * Real.exp ((a * w).re) := by
    have h := cepsScaledTrueDenominator_inverse_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbN
    apply h.trans_eq
    dsimp [C, K, X, e]
    ring
  have h1 := cepsNorm_weighted_three_product_le (mul_nonneg hE he) hT (mul_nonneg hK hX)
    (herr 1 (by norm_num)) (htrue (-1) (by norm_num)) hI
  have h2 := cepsNorm_weighted_three_product_le hB (mul_nonneg hE he) (mul_nonneg hK hX)
    (hsur 1 (by norm_num)) (herr (-1) (by norm_num)) hI
  have h3 := cepsNorm_weighted_three_product_le hB hB (by positivity : 0 ≤ C * K * X * e)
    (hsur 1 (by norm_num)) (hsur (-1) (by norm_num)) hIJ
  have h := (cepsNorm_three_factor_error_le (A p) (A a) I (G p) (G a) J).trans
    (add_le_add (add_le_add h1 h2) h3)
  unfold cepsScaledTrueBridge cepsScaledSurrogateBridge
  simp only [div_eq_mul_inv, neg_mul]
  change ‖-(A p * A a * I) - -(G p * G a * J)‖ ≤ _
  rw [show -(A p * A a * I) - -(G p * G a * J) = -(A p * A a * I - G p * G a * J) by ring,
    norm_neg]
  apply h.trans_eq
  unfold CepsCanonDomain.trueBridgeErrorConstant
  dsimp [E, T, B, C, K, X, e, p, w]
  ring

end PGM
