import PLAStochastic.Index.CEPS.Scaled.EndpointRegular
import PLAStochastic.Index.CEPS.Scaled.DoubleMarkPrefactor

/-! # Weighted factors of the true and surrogate endpoint -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsScaledEndpointCarrier (D θ : ℝ) (ρW : Measure ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b)) *
    (cepsScaledSignedRoot D θ ρW 1 z 1 b - cepsScaledSignedRoot D θ ρW 1 z (-1) b) /
      (b * z - cepsScaledSignedRoot D θ ρW 1 z (-1) b)

def CepsCanonDomain.endpointCarrierConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.scaledGapBound * dom.scaledCoordinateRatioBound / dom.positiveMarkerGapLower

theorem cepsScaledTrueRegularEndpoint_eq_factors {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (z : ℂ) (b : ℝ) :
    cepsScaledTrueRegularEndpoint dom ρW z b = cepsScaledTrueDoubleMarkPrefactor dom ρW 1 z b *
      cepsScaledTrueG dom ρW 1 z b (cepsScaledSignedRoot D θ ρW 1 z 1 b) *
        cepsScaledEndpointCarrier D θ ρW z b := by
  unfold cepsScaledTrueRegularEndpoint cepsScaledTrueDoubleMarkPrefactor cepsScaledTrueMarkPrefactor
    cepsScaledEndpointCarrier
  simp only [ofReal_one, mul_one]
  rw [show (2 : ℂ) * dom.canonL ρW b (cepsComplexScaledDiscount 1 z b) ((b : ℂ) ^ 2 * z) =
    dom.canonL ρW b (cepsComplexScaledDiscount 1 z b) ((b : ℂ) ^ 2 * z) +
      dom.canonL ρW b (cepsComplexScaledDiscount 1 z b) ((b : ℂ) ^ 2 * z) by ring, exp_add]
  ring

theorem cepsScaledSurrogateMarkedEndpoint_eq_factors {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (N : ℕ) (z b : ℂ) :
    cepsScaledSurrogateMarkedEndpoint dom ρW N z b = cepsScaledSurrogateDoubleMarkPrefactor dom ρW N 1 z b *
      cepsScaledSurrogateG dom ρW N 1 z b (cepsScaledSignedRoot D θ ρW 1 z 1 b) *
        cepsScaledEndpointCarrier D θ ρW z b := by
  rw [cepsScaledSurrogateMarkedEndpoint_eq_product]
  unfold cepsScaledSurrogateDoubleMarkPrefactor cepsScaledSurrogateMarkPrefactor cepsScaledEndpointCarrier
  simp only [ofReal_one, mul_one]
  rw [show (2 : ℂ) * cepsCanonDriftTaylor dom ρW N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z) =
    cepsCanonDriftTaylor dom ρW N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z) +
      cepsCanonDriftTaylor dom ρW N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z) by ring, exp_add]
  ring

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem endpointCarrierConstant_nonneg : 0 ≤ dom.endpointCarrierConstant := by
  have := (cepsScaledSurrogate_constants dom hW hθ hD 0 0).1.le
  have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  have := (positiveMarkerGapLower_pos dom hW hθ hD).le
  unfold CepsCanonDomain.endpointCarrierConstant
  positivity

theorem trueDenominatorScaleRadius_le_pair (M lam : ℝ) (z : ℂ) :
    dom.trueDenominatorScaleRadius M lam z ≤
      dom.pairPolynomialScaleBase 0 M / (1 + |lam| + Real.sqrt ‖z‖) :=
  div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)

include hW hθ hD in
theorem cepsScaledRootGap_polynomial_bound (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z)) :
    ‖cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤
      (dom.scaledGapBound * dom.scaledCoordinateRatioBound) * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hbRad := ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb)
  have hK := (cepsScaledSurrogate_constants dom hW hθ hD 0 0).1.le
  have hgap := cepsScaledRootGap_norm_le dom hW hθ hD lam hz hb
  have hroot := ((cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b hbRad).trans
    (scaledRootCoordinateBound_le_polynomial dom hW hθ hD lam z)
  exact (hgap.trans (mul_le_mul_of_nonneg_left hroot hK)).trans_eq (by
    unfold CepsCanonDomain.scaledGapBound
    ring)

include hW hθ hD in
theorem cepsScaledEndpointCarrier_budget (N : ℕ) (M : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖))) :
    ‖cepsScaledEndpointCarrier D θ ρW z b‖ ≤ dom.endpointCarrierConstant * (2 + Real.sqrt ‖z‖) *
      Real.exp (((b * z) * (1 + b)).re) := by
  have hb' : b ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase N M / (1 + |(1 : ℝ)| + Real.sqrt ‖z‖)) := by
    simpa only [abs_one, one_add_one_eq_two] using hb
  have hbE := ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M 1 z).2 hb'
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD 1 z).le (by norm_num))) hbE
  have hgap := cepsScaledRootGap_polynomial_bound dom hW hθ hD 1 hz hbC
  simp only [abs_one, one_add_one_eq_two] at hgap
  have hmark := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD N M 1 le_rfl hz hb'
  have hP := positiveMarkerGapLower_pos dom hW hθ hD
  have hinv : ‖(b * z - cepsScaledSignedRoot D θ ρW 1 z (-1) b)⁻¹‖ ≤ dom.positiveMarkerGapLower⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hP.trans_le hmark) hP).mpr hmark
  unfold cepsScaledEndpointCarrier
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_exp]
  exact (mul_le_mul (mul_le_mul_of_nonneg_left hgap (Real.exp_pos _).le) hinv (norm_nonneg _)
    (by have := (cepsScaledSurrogate_constants dom hW hθ hD 0 0).1.le
        have hA : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
        positivity)).trans_eq (by unfold CepsCanonDomain.endpointCarrierConstant; ring)

include hW hθ hD in
theorem cepsScaledSurrogateDoubleMarkPrefactor_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖cepsScaledSurrogateDoubleMarkPrefactor dom ρW N lam z b‖ ≤
      Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8)) * (4 / cepsVarLo D) := by
  have hE := cepsScaledSurrogateMarkExp_budget dom hW hθ hD hf hη hM N hN lam hz hb
  have hP := cepsScaledSurrogateMarkPrefactor_budget dom hW hθ hD hf hη hM N hN lam hz hb
  have he : cepsScaledSurrogateDoubleMarkPrefactor dom ρW N lam z b =
      exp (cepsCanonDriftTaylor dom ρW N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) *
        cepsScaledSurrogateMarkPrefactor dom ρW N lam z b := by
    unfold cepsScaledSurrogateDoubleMarkPrefactor cepsScaledSurrogateMarkPrefactor
    rw [show (2 : ℂ) * _ = _ + _ by ring, exp_add]
    ring
  rw [he, norm_mul]
  exact (mul_le_mul hE hP (norm_nonneg _) (Real.exp_pos _).le).trans_eq (by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring)

end PGM
