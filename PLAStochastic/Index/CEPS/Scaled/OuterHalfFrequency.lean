import PLAStochastic.Index.CEPS.Scaled.OuterTimeOperator

/-! # Half-line frequency and time-operator budgets on complex scale discs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

attribute [local irreducible] cepsScaledSurrogateG

def CepsCanonDomain.outerHalfFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  2 * dom.outerRootFrequencyConstant N M *
    (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) +
      dom.scaledGapBound * dom.scaledCoordinateRatioBound * dom.outerRootValueFrequencyConstant N M

def CepsCanonDomain.outerHalfTimeOperatorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  2 * dom.outerHalfFrequencyConstant N M + dom.surrogateHalfBridgeWeightedConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerHalfFrequency_constants (N : ℕ) (M : ℝ) :
    0 < dom.outerHalfFrequencyConstant N M ∧ 0 < dom.outerHalfTimeOperatorConstant N M := by
  have := (outerFrequency_constants dom hW hθ hD N M).2.1
  have := outerRootValueFrequencyConstant_pos dom hW hθ hD N M
  have := (cepsScaledSurrogate_constants dom hW hθ hD N M).1
  have := CepsCanonDomain.v_pos hW hθ hD
  have hC : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
  have hH : 0 < dom.outerHalfFrequencyConstant N M := by
    unfold CepsCanonDomain.outerHalfFrequencyConstant
    positivity
  refine ⟨hH, ?_⟩
  unfold CepsCanonDomain.outerHalfTimeOperatorConstant CepsCanonDomain.surrogateHalfBridgeWeightedConstant
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_outer_frequency_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z ∧
      ‖deriv (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z‖ ≤
        dom.outerHalfFrequencyConstant N M * (1 + |lam| + Real.sqrt ‖z‖) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) := by
  let p := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ 1 b
  let m := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ (-1) b
  let G := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (p ζ)
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let W := v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  let E := Real.exp (-(p z * (1 + b * lam)).re)
  have hne := outerFrequency_ne_origin dom hW hθ hD N M lam z houter
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hp := (cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz hne
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC).differentiableAt
  have hm := (cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz hne
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbC).differentiableAt
  have hG := cepsScaledSurrogateG_complex_frequency_differentiableAt dom hW hθ hD hf hη N hN lam hz hne
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb
  have hpB := cepsScaledSignedRoot_outer_frequency_budget dom hW hθ hD N M lam hz houter
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb
  have hmB := cepsScaledSignedRoot_outer_frequency_budget dom hW hθ hD N M lam hz houter
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hb
  have hgapD : ‖deriv (fun ζ => p ζ - m ζ) z‖ ≤ 2 * dom.outerRootFrequencyConstant N M := by
    change ‖deriv (p - m) z‖ ≤ _
    rw [deriv_sub (f := p) (g := m) hp hm]
    exact ((norm_sub_le _ _).trans (add_le_add hpB hmB)).trans_eq (by ring)
  have hgap : ‖p z - m z‖ ≤ dom.scaledGapBound * dom.scaledCoordinateRatioBound * X := by
    have hr := (cepsScaledRootCoordinate_budget dom hW hθ hD lam hz).2 b
      (ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hbC))
    have hK := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
    exact ((cepsScaledRootGap_norm_le dom hW hθ hD lam hz hbC).trans
      (mul_le_mul_of_nonneg_left (hr.trans (scaledRootCoordinateBound_le_polynomial dom hW hθ hD lam z)) hK)).trans_eq
        (by unfold CepsCanonDomain.scaledGapBound; ring)
  have hGv : ‖G z‖ ≤ W * E := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC
  have hGd : ‖deriv G z‖ ≤ dom.outerRootValueFrequencyConstant N M * E :=
    cepsScaledSurrogateG_outer_frequency_budget dom hW hθ hD hf hη hM N hN lam hz houter
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb
  have hW0 : 0 ≤ W := by have := CepsCanonDomain.v_pos hW hθ hD; dsimp [W]; positivity
  have hR0 := (outerFrequency_constants dom hW hθ hD N M).2.1.le
  have hV0 := (outerRootValueFrequencyConstant_pos dom hW hθ hD N M).le
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hgap0 : 0 ≤ dom.scaledGapBound * dom.scaledCoordinateRatioBound * X :=
    (norm_nonneg _).trans hgap
  refine ⟨(hp.sub hm).mul hG, ?_⟩
  change ‖deriv ((p - m) * G) z‖ ≤ _
  rw [deriv_mul (c := p - m) (d := G) (hp.sub hm) hG]
  simp only [Pi.sub_apply]
  apply ((norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])).trans
  have h1 := mul_le_mul hgapD hGv (norm_nonneg _) (by positivity : 0 ≤ 2 * dom.outerRootFrequencyConstant N M)
  have h2 := mul_le_mul hgap hGd (norm_nonneg _) hgap0
  have h3 := le_mul_of_one_le_right (by positivity : 0 ≤ 2 * dom.outerRootFrequencyConstant N M * W * E) hX
  change _ ≤ dom.outerHalfFrequencyConstant N M * X * E
  unfold CepsCanonDomain.outerHalfFrequencyConstant
  refine (add_le_add h1 h2).trans ?_
  calc
    _ = (2 * dom.outerRootFrequencyConstant N M * W * E) +
      (dom.scaledGapBound * dom.scaledCoordinateRatioBound * X) *
        (dom.outerRootValueFrequencyConstant N M * E) := by ring
    _ ≤ (2 * dom.outerRootFrequencyConstant N M * W * E) * X +
      (dom.scaledGapBound * dom.scaledCoordinateRatioBound * X) *
        (dom.outerRootValueFrequencyConstant N M * E) := add_le_add h3 le_rfl
    _ = _ := by dsimp only [W]; ring

include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_outer_timeOperator_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z))
    (hbWidth : b ∈ ball (0 : ℂ) (1 / (2 * (1 + |lam|)))) :
    ‖cepsComplexScaledTimeOperator lam b (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N lam ζ b) z‖ ≤
      dom.outerHalfTimeOperatorConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) := by
  obtain ⟨hb1, -, hw⟩ := cepsComplexScaled_width_bounds lam hbWidth
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hX : 1 ≤ 1 + |lam| + Real.sqrt ‖z‖ := by linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hD' := (cepsScaledSurrogateHalfBridge_outer_frequency_profile dom hW hθ hD hf hη hM N hN lam hz houter hb).2
  have hA := (outerHalfFrequency_constants dom hW hθ hD N M).1.le
  have hB : 0 ≤ dom.surrogateHalfBridgeWeightedConstant N M := by
    unfold CepsCanonDomain.surrogateHalfBridgeWeightedConstant
    have := (cepsScaledSurrogate_constants dom hW hθ hD N M).1.le
    have := (CepsCanonDomain.v_pos hW hθ hD).le
    have hC : 0 ≤ dom.scaledCoordinateRatioBound := Real.sqrt_nonneg _
    positivity
  have hD2 := hD'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by nlinarith [hX] : (1 + |lam| + Real.sqrt ‖z‖) ≤
      (1 + |lam| + Real.sqrt ‖z‖) ^ 2) hA) (Real.exp_pos _).le)
  exact cepsComplexScaledTimeOperator_weighted_le hB hX hb1 hw hD2
    (cepsScaledSurrogateHalfBridge_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hbC)

end PGM
