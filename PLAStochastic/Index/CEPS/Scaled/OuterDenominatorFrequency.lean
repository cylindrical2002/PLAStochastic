import PLAStochastic.Index.CEPS.Scaled.OuterRootValueFrequency
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeWeighted
import PLAStochastic.ForMathlib.Analysis.Complex.MovingDSlopeDerivative

/-! # Weighted divided-denominator frequency budgets outside the central region -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerDenominatorValueConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  2 * (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
    dom.outerRootGapInverseConstant N M

def CepsCanonDomain.outerDenominatorFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  (2 * dom.outerRootValueFrequencyConstant N M +
    dom.outerDenominatorValueConstant N M * (2 * dom.outerRootFrequencyConstant N M)) *
      dom.outerRootGapInverseConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerDenominator_constants (N : ℕ) (M : ℝ) :
    0 < dom.outerDenominatorValueConstant N M ∧ 0 < dom.outerDenominatorFrequencyConstant N M := by
  have hs := outerFrequency_constants dom hW hθ hD N M
  have hR := hs.2.1
  have hK := hs.2.2
  have hV := outerRootValueFrequencyConstant_pos dom hW hθ hD N M
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hS : 0 < dom.outerDenominatorValueConstant N M := by
    unfold CepsCanonDomain.outerDenominatorValueConstant
    positivity
  exact ⟨hS, by unfold CepsCanonDomain.outerDenominatorFrequencyConstant; positivity⟩

include hW hθ hD in
theorem cepsScaledRootWeights_complex_order (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.surrogateScaleRadius N M lam z)) :
    Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) ≤
      Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  have hs := cepsScaledEffectiveGap_sector dom hW hθ hD N M lam hz hb
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1.le
  have he := (mul_nonneg hc (norm_nonneg _)).trans hs
  simp only [cepsScaledEffectiveGap, sub_mul, sub_re] at he
  exact Real.exp_le_exp.mpr (by linarith)

include hW hθ hD in
theorem cepsScaledSurrogateDenominator_outer_frequency_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateDenominator dom ρW N lam ζ b) z ∧
      ‖cepsScaledSurrogateDenominator dom ρW N lam z b‖ ≤
        dom.outerDenominatorValueConstant N M *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) ∧
      ‖deriv (fun ζ => cepsScaledSurrogateDenominator dom ρW N lam ζ b) z‖ ≤
        dom.outerDenominatorFrequencyConstant N M *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  let p : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ 1 b
  let a : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ (-1) b
  let G : ℂ → ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b
  let E := Real.exp (-(a z * (1 + b * lam)).re)
  let W := v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  let V := dom.outerRootValueFrequencyConstant N M
  let K := dom.outerRootGapInverseConstant N M
  let R := dom.outerRootFrequencyConstant N M
  have hW0 : 0 ≤ W := by have := CepsCanonDomain.v_pos hW hθ hD; dsimp [W]; positivity
  have hV0 : 0 ≤ V := (outerRootValueFrequencyConstant_pos dom hW hθ hD N M).le
  have hK0 : 0 ≤ K := (outerFrequency_constants dom hW hθ hD N M).2.2.le
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hne := outerFrequency_ne_origin dom hW hθ hD N M lam z houter
  have hp := cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz hne
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC
  have ha := cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz hne
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbC
  have hpG : DifferentiableAt ℂ (fun ζ => G ζ (p ζ)) z :=
    cepsScaledSurrogateG_complex_frequency_differentiableAt dom hW hθ hD hf hη N hN lam hz hne (by norm_num) hb
  have haG : DifferentiableAt ℂ (fun ζ => G ζ (a ζ)) z :=
    cepsScaledSurrogateG_complex_frequency_differentiableAt dom hW hθ hD hf hη N hN lam hz hne (by norm_num) hb
  obtain ⟨hgap0, hgap⟩ := cepsScaledRootGap_outer_inverse_budget dom hW hθ hD N M lam hz houter hb
  have hord := cepsScaledRootWeights_complex_order dom hW hθ hD N M lam hz
    (ball_subset_ball (min_le_left _ _) (ball_subset_ball (min_le_left _ _) hb))
  have hGp : ‖G z (p z)‖ ≤ W * E :=
    (cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hbC).trans (mul_le_mul_of_nonneg_left hord hW0)
  have hGa : ‖G z (a z)‖ ≤ W * E :=
    cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz (by norm_num) hbC
  have hS : ‖dslope (G z) (a z) (p z)‖ ≤ dom.outerDenominatorValueConstant N M * E := by
    rw [dslope_of_ne _ hgap0, slope_def_field, div_eq_mul_inv, norm_mul]
    apply (mul_le_mul ((norm_sub_le _ _).trans (add_le_add hGp hGa)) hgap
      (norm_nonneg _) (by positivity : 0 ≤ W * E + W * E)).trans_eq
    unfold CepsCanonDomain.outerDenominatorValueConstant
    dsimp only [W, K]
    ring
  have hDp : ‖deriv (fun ζ => G ζ (p ζ)) z‖ ≤ V * E :=
    (cepsScaledSurrogateG_outer_frequency_budget dom hW hθ hD hf hη hM N hN lam hz houter
      (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb).trans (mul_le_mul_of_nonneg_left hord hV0)
  have hDa : ‖deriv (fun ζ => G ζ (a ζ)) z‖ ≤ V * E :=
    cepsScaledSurrogateG_outer_frequency_budget dom hW hθ hD hf hη hM N hN lam hz houter (by norm_num) hb
  have hR : ‖deriv p z - deriv a z‖ ≤ 2 * R :=
    (norm_sub_le _ _).trans ((add_le_add
      (cepsScaledSignedRoot_outer_frequency_budget dom hW hθ hD N M lam hz houter (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb)
      (cepsScaledSignedRoot_outer_frequency_budget dom hW hθ hD N M lam hz houter (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hb)).trans_eq (by ring))
  have hd := hasDerivAt_moving_dslope_of_ne (G := G) (a := a) (p := p)
    ha.differentiableAt.hasDerivAt hp.differentiableAt.hasDerivAt haG.hasDerivAt hpG.hasDerivAt hgap0
  have hbudget := norm_deriv_moving_dslope_mul_sq_le (G := G) (a := a) (p := p)
    ha.differentiableAt.hasDerivAt hp.differentiableAt.hasDerivAt haG.hasDerivAt hpG.hasDerivAt hgap0
    (L := 1) (by norm_num) (by simpa using hgap) (by simpa using hDa) (by simpa using hDp)
    hS (by simpa using hR)
  refine ⟨hd.differentiableAt, hS, ?_⟩
  simp only [one_pow, mul_one] at hbudget
  apply hbudget.trans_eq
  unfold CepsCanonDomain.outerDenominatorFrequencyConstant
  dsimp only [V, K, R, E, a]
  ring

end PGM
