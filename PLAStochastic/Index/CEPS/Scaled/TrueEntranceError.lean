import PLAStochastic.Index.CEPS.Scaled.TrueMarkPrefactor
import PLAStochastic.Index.CEPS.Scaled.WeightedEntranceProduct

/-! # Actual scaled entrance norms and full real-drift surrogate errors -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledTrueEntrance {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (lam : ℝ) (z : ℂ) (b : ℝ) : ℂ :=
  -cepsScaledTrueMarkPrefactor dom ρW lam z b * cepsScaledTrueEntranceNumerator dom ρW lam z b /
    cepsScaledTrueDenominator dom ρW lam z b

def CepsCanonDomain.trueEntranceWeightedConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  (Real.exp dom.normalLogBound * (4 / cepsVarLo D)) * dom.trueSpatialBound M 2 *
    (2 * dom.surrogateSlopePolynomialConstant 0 M)

def CepsCanonDomain.trueEntranceErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  (dom.trueMarkPrefactorErrorConstant N M * dom.trueSpatialBound M 2 +
    (Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D)) *
      dom.trueSpatialErrorConstant N M 2 +
    (Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D)) *
      dom.surrogateSpatialSecondBound N M * dom.trueDenominatorRelativeConstant N M) *
        (2 * dom.surrogateSlopePolynomialConstant 0 M)

theorem cepsScaledSurrogateEntrance_eq_prefactor {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsScaledSurrogateEntrance dom ρW N lam z b =
      -cepsScaledSurrogateMarkPrefactor dom ρW N lam z b *
        dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
          (cepsScaledSignedRoot D θ ρW lam z (-1) b))
          (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z) /
            cepsScaledSurrogateDenominator dom ρW N lam z b := by
  unfold cepsScaledSurrogateEntrance cepsScaledSurrogateMarkPrefactor
  simp only [div_eq_mul_inv, mul_inv]
  ring

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueEntrance_weighted_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z)) :
    ‖cepsScaledTrueEntrance dom ρW lam z b‖ ≤ dom.trueEntranceWeightedConstant M *
      (1 + |lam| + Real.sqrt ‖z‖) *
        (1 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
          cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) +
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
              (1 + (b : ℂ) * lam)).re)) := by
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hb
  have hP := cepsScaledTrueMarkPrefactor_budget dom hW hθ hD 0 M lam hz hbE
  have hE := cepsScaledTrueEntranceNumerator_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
  have hI := cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM hm lam hz hb
  have hC := trueSpatialBound_nonneg dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) 2
  have hK := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M
  have hvl := cepsVarLo_pos hD
  have h := cepsNorm_weighted_entrance_product_le (by positivity) hC (by positivity) hP hE hI
  unfold cepsScaledTrueEntrance
  rw [neg_mul, div_eq_mul_inv, neg_mul, norm_neg]
  apply h.trans_eq
  unfold CepsCanonDomain.trueEntranceWeightedConstant
  ring

include hW hθ hD in
theorem cepsScaledTrueEntrance_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledTrueEntrance dom ρW lam z b - cepsScaledSurrogateEntrance dom ρW N lam z b‖ ≤
      dom.trueEntranceErrorConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
        (1 + Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b -
          cepsScaledSignedRoot D θ ρW lam z 1 b) * (1 + (b : ℂ) * lam)).re) +
            Real.exp (((cepsScaledSignedRoot D θ ρW lam z (-1) b - (b : ℂ) * z) *
              (1 + (b : ℂ) * lam)).re)) * |b * lam| ^ (N + 1) := by
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let t := (b : ℂ) * z
  let w : ℂ := 1 + (b : ℂ) * lam
  let P := cepsScaledTrueMarkPrefactor dom ρW lam z b
  let Q := cepsScaledSurrogateMarkPrefactor dom ρW N lam z (b : ℂ)
  let A := cepsScaledTrueEntranceNumerator dom ρW lam z b
  let B := dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b) a) p t
  let I := (cepsScaledTrueDenominator dom ρW lam z b)⁻¹
  let J := (cepsScaledSurrogateDenominator dom ρW N lam z b)⁻¹
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let e := |b * lam| ^ (N + 1)
  let CP := dom.trueMarkPrefactorErrorConstant N M
  let CQ := Real.exp (dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D)
  let CA := dom.trueSpatialBound M 2
  let CB := dom.surrogateSpatialSecondBound N M
  let CE := dom.trueSpatialErrorConstant N M 2
  let CS := dom.trueDenominatorRelativeConstant N M
  let K := 2 * dom.surrogateSlopePolynomialConstant 0 M
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hCP : 0 ≤ CP := trueMarkPrefactorErrorConstant_nonneg dom hD hM0 N
  have hCQ : 0 ≤ CQ := by dsimp [CQ]; have := cepsVarLo_pos hD; positivity
  have hCA : 0 ≤ CA := trueSpatialBound_nonneg dom hW hθ hD hM0 2
  have hCB : 0 ≤ CB := by dsimp [CB, CepsCanonDomain.surrogateSpatialSecondBound]; have := CepsCanonDomain.v_pos hW hθ hD; positivity
  have hCE : 0 ≤ CE := trueSpatialErrorConstant_nonneg dom hW hθ hD hM0 N 2
  have hCS : 0 ≤ CS := trueDenominatorRelativeConstant_nonneg dom hW hθ hD hM0 N
  have hK : 0 ≤ K := by dsimp [K]; have := surrogateSlopePolynomialConstant_pos dom hW hθ hD 0 M; positivity
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have he : 0 ≤ e := pow_nonneg (abs_nonneg _) _
  have hP := cepsScaledTrueMarkPrefactor_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN
  have hQ := cepsScaledSurrogateMarkPrefactor_budget dom hW hθ hD hf hη hM N (by omega) lam hz hbN
  have hA := cepsScaledTrueEntranceNumerator_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hb
  have hB := cepsScaledSurrogateG_second_dslope_weighted_budget dom hW hθ hD hf hη hM N (by omega) lam hz hbN
  have hE := cepsScaledTrueEntranceNumerator_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN
  have hI : ‖I‖ ≤ (K * X) * Real.exp ((a * w).re) :=
    cepsScaledTrueDenominator_inverse_weighted_budget dom hW hθ hD hf hη hM (by omega) lam hz hb
  have hIJ : ‖I - J‖ ≤ (CS * K * X * e) * Real.exp ((a * w).re) := by
    apply (cepsScaledTrueDenominator_inverse_error_budget dom hW hθ hD hf hη hM N hN lam hz hb hbN).trans_eq
    dsimp [CS, K, X, e]
    ring
  have h1 := cepsNorm_weighted_entrance_product_le (mul_nonneg hCP he) hCA (mul_nonneg hK hX) hP hA hI
  have h2 := cepsNorm_weighted_entrance_product_le hCQ (mul_nonneg hCE he) (mul_nonneg hK hX) hQ hE hI
  have h3 := cepsNorm_weighted_entrance_product_le hCQ hCB (by positivity : 0 ≤ CS * K * X * e) hQ hB hIJ
  have h := (cepsNorm_three_factor_error_le P A I Q B J).trans (add_le_add (add_le_add h1 h2) h3)
  rw [cepsScaledSurrogateEntrance_eq_prefactor]
  unfold cepsScaledTrueEntrance
  simp only [div_eq_mul_inv, neg_mul]
  change ‖-(P * A * I) - -(Q * B * J)‖ ≤ _
  rw [show -(P * A * I) - -(Q * B * J) = -(P * A * I - Q * B * J) by ring, norm_neg]
  apply h.trans_eq
  unfold CepsCanonDomain.trueEntranceErrorConstant
  dsimp [CP, CQ, CA, CB, CE, CS, K, X, e, a, p, t, w]
  ring

end PGM
