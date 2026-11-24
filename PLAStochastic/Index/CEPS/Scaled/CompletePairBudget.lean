import PLAStochastic.Index.CEPS.Scaled.OuterPairTaylor
import PLAStochastic.Index.CEPS.Scaled.CentralPairTaylor

/-! # Class-uniform complete-pair scale budget over all real drifts and right-half-plane frequencies

The joint origin uses even descent on the central rectangle. Outside it,
the complete positive-tail subtraction and outer joint charts are used.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.completePairScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.centralPairScaleRadius N M) (dom.outerPairPolynomialScaleBase N M)

def CepsCanonDomain.completePairConstant {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (N : ℕ) (M : ℝ) : ℝ :=
  |dom.centralPairBound N M| * Real.exp (dom.positiveEntranceBridgeDecayRate *
    (dom.centralFrequencyDriftRadius N M + Real.sqrt (dom.centralFrequencyRadius N M))) +
      dom.outerSubtractedPairConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem completePairScaleBase_pos (N : ℕ) (M : ℝ) :
    0 < dom.completePairScaleBase N M :=
  lt_min (centralPairScaleRadius_pos dom hW hθ hD N M)
    (outerPairPolynomialScaleBase_pos dom hW hθ hD N M)

theorem completePairConstant_nonneg (N : ℕ) (M : ℝ) : 0 ≤ dom.completePairConstant N M := by
  unfold CepsCanonDomain.completePairConstant CepsCanonDomain.outerSubtractedPairConstant
  positivity

include hW hθ hD in
theorem centralFrequencyDriftRadius_lt_one (N : ℕ) (M : ℝ) :
    dom.centralFrequencyDriftRadius N M < 1 := by
  have hR := centralCoordinateRadius_pos dom hW hθ hD N M
  have hR1 : dom.centralCoordinateRadius N M ≤ 1 := min_le_left _ _
  have hRsq : dom.centralCoordinateRadius N M ^ 2 ≤ 1 := by nlinarith
  have hU : 0 ≤ dom.morseMinUnitBound := by unfold CepsCanonDomain.morseMinUnitBound; positivity
  apply lt_of_le_of_lt (min_le_right _ _)
  rw [div_lt_iff₀ (by positivity : 0 < 64 * (1 + dom.morseMinUnitBound))]
  nlinarith

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_complete_differentiableOn {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableOn ℂ (cepsScaledSurrogateSubtractedPair dom ρW N lam z)
      (ball 0 (dom.completePairScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hC := (centralPairScaleRadius_pos dom hW hθ hD N M).le
  have hsubC : ball (0 : ℂ) (dom.completePairScaleBase N M / X) ⊆
      ball 0 (dom.centralPairScaleRadius N M) := ball_subset_ball
    ((div_le_div_of_nonneg_right (min_le_left _ _) (by linarith : 0 ≤ X)).trans
      (div_le_self hC hX))
  by_cases hc : |lam| ≤ dom.centralFrequencyDriftRadius N M ∧ ‖z‖ < dom.centralFrequencyRadius N M
  · have hl : ¬1 ≤ lam := not_le.mpr ((le_abs_self lam).trans hc.1 |>.trans_lt
      (centralFrequencyDriftRadius_lt_one dom hW hθ hD N M))
    unfold cepsScaledSurrogateSubtractedPair
    simp only [hl, ite_false]
    exact (cepsScaledSurrogatePair_central_differentiableOn dom hW hθ hD hf hη hM N hN lam hc.1 hz hc.2).mono hsubC
  · have ho : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖ := by
      push Not at hc
      exact lt_or_ge (dom.centralFrequencyDriftRadius N M) |lam| |>.imp_right hc
    have hsubO : ball (0 : ℂ) (dom.completePairScaleBase N M / X) ⊆
        ball 0 (dom.outerPairScaleRadius N M lam z) := ball_subset_ball
      ((div_le_div_of_nonneg_right (min_le_right _ _) (by linarith : 0 ≤ X)).trans
        (outerPairPolynomialScaleRadius_le dom hW hθ hD N M lam z))
    exact (cepsScaledSurrogateSubtractedPair_outer_differentiableOn dom hW hθ hD hf hη hM N hN lam hz
      (outerFrequency_ne_origin dom hW hθ hD N M lam z ho)).mono hsubO

include hW hθ hD in
theorem cepsScaledSurrogateSubtractedPair_complete_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.completePairScaleBase N M / (1 + |lam| + Real.sqrt ‖z‖))) :
    ‖cepsScaledSurrogateSubtractedPair dom ρW N lam z b‖ ≤
      dom.completePairConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 4 *
        Real.exp (-dom.positiveEntranceBridgeDecayRate * (|lam| + Real.sqrt ‖z‖)) := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let F := |lam| + Real.sqrt ‖z‖
  let F₀ := dom.centralFrequencyDriftRadius N M + Real.sqrt (dom.centralFrequencyRadius N M)
  let c := dom.positiveEntranceBridgeDecayRate
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hc0 := (positiveEntranceBridge_constants dom hW hθ hD N M).2.le
  by_cases hc : |lam| ≤ dom.centralFrequencyDriftRadius N M ∧ ‖z‖ < dom.centralFrequencyRadius N M
  · have hl : ¬1 ≤ lam := not_le.mpr ((le_abs_self lam).trans hc.1 |>.trans_lt
      (centralFrequencyDriftRadius_lt_one dom hW hθ hD N M))
    have hbC : b ∈ ball (0 : ℂ) (dom.centralPairScaleRadius N M) := ball_subset_ball
      ((div_le_div_of_nonneg_right (min_le_left _ _) (by linarith : 0 ≤ X)).trans
        (div_le_self (centralPairScaleRadius_pos dom hW hθ hD N M).le hX)) hb
    have hF : F ≤ F₀ := add_le_add hc.1 (Real.sqrt_le_sqrt hc.2.le)
    have he : 1 ≤ Real.exp (c * F₀) * Real.exp (-c * F) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by nlinarith)
    have hp : 1 ≤ X ^ 4 := one_le_pow₀ hX
    have hK : |dom.centralPairBound N M| * Real.exp (c * F₀) ≤ dom.completePairConstant N M := by
      exact le_add_of_nonneg_right (by unfold CepsCanonDomain.outerSubtractedPairConstant; positivity)
    have hbound := cepsScaledSurrogatePair_central_bound dom hW hθ hD hf hη hM N hN lam hc.1 hz hc.2 hbC
    unfold cepsScaledSurrogateSubtractedPair
    rw [if_neg hl]
    calc
      _ ≤ |dom.centralPairBound N M| := hbound.trans (le_abs_self _)
      _ ≤ |dom.centralPairBound N M| * (X ^ 4 * (Real.exp (c * F₀) * Real.exp (-c * F))) :=
        le_mul_of_one_le_right (abs_nonneg _) (one_le_mul_of_one_le_of_one_le hp he)
      _ = (|dom.centralPairBound N M| * Real.exp (c * F₀)) * X ^ 4 * Real.exp (-c * F) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (Real.exp_pos _).le
  · have ho : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖ := by
      push Not at hc
      exact lt_or_ge (dom.centralFrequencyDriftRadius N M) |lam| |>.imp_right hc
    have hbO : b ∈ ball (0 : ℂ) (dom.outerPairScaleRadius N M lam z) := ball_subset_ball
      ((div_le_div_of_nonneg_right (min_le_right _ _) (by linarith : 0 ≤ X)).trans
        (outerPairPolynomialScaleRadius_le dom hW hθ hD N M lam z)) hb
    have hK : dom.outerSubtractedPairConstant N M ≤ dom.completePairConstant N M :=
      le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    exact (cepsScaledSurrogateSubtractedPair_outer_budget dom hW hθ hD hf hη hM N hN lam hz ho hbO).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (Real.exp_pos _).le)

end PGM
