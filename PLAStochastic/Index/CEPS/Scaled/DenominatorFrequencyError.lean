import PLAStochastic.Index.CEPS.Scaled.RootEvaluationDifferential
import PLAStochastic.Index.CEPS.Scaled.RootFrequencyGapBudget
import PLAStochastic.ForMathlib.Analysis.Complex.MovingDSlopeDerivative

/-! # Drift-weighted frequency derivative error of the divided denominator -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.denominatorFrequencyErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.rootFrequencyGapInverseConstant *
    (2 * dom.rootEvaluationFrequencyErrorConstant N M +
      4 * dom.trueSpatialErrorConstant N M 1 * dom.rootFrequencyConstant)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueDenominator_frequency_deriv_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueDenominator dom ρW lam ζ b -
      cepsScaledSurrogateDenominator dom ρW N lam ζ b) z‖ * |lam| ^ 2 ≤
        dom.denominatorFrequencyErrorConstant N M * (1 + |lam|) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) *
            |b * lam| ^ (N + 1) := by
  by_cases hl : lam = 0
  · subst lam
    simp
  let p : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ 1 b
  let a : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ (-1) b
  let G : ℂ → ℂ → ℂ := fun ζ ξ => cepsScaledTrueG dom ρW lam ζ b ξ -
    cepsScaledSurrogateG dom ρW N lam ζ b ξ
  let w : ℂ := 1 + (b : ℂ) * lam
  let e := |b * lam| ^ (N + 1)
  let E := Real.exp (-(a z * w).re)
  let C := dom.rootEvaluationFrequencyErrorConstant N M
  let S := dom.trueSpatialErrorConstant N M 1
  let R := dom.rootFrequencyConstant
  let K := dom.rootFrequencyGapInverseConstant
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hS : 0 ≤ S := trueSpatialErrorConstant_nonneg dom hW hθ hD hM0 N 1
  have hR : 0 ≤ R := by
    have := cepsChartK_pos hD
    unfold R CepsCanonDomain.rootFrequencyConstant
    positivity
  have hK : 0 ≤ K := by unfold K CepsCanonDomain.rootFrequencyGapInverseConstant; positivity
  have hC : 0 ≤ C := by
    have hqpos := dom.q₀_pos
    have hcpos := dom.c₀_pos
    have := CepsCanonDomain.v_pos hW hθ hD
    have := dom.jetC_nonneg hD N
    unfold C CepsCanonDomain.rootEvaluationFrequencyErrorConstant CepsCanonDomain.canonWeightErrorBound
      CepsCanonDomain.canonDriftCoeffBound
    change 0 ≤ _ * (2 * R + R / (dom.c₀ / 8) + 2 / (dom.q₀ / 8))
    positivity
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hp := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hl) hb hbs
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have ha := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hl) hb hbs
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)
  obtain ⟨hpA, hpB⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N
    (by omega) M lam hz (Or.inl hl) hb hbs (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨haA, haB⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N
    (by omega) M lam hz (Or.inl hl) hb hbs (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  have hpG : DifferentiableAt ℂ (fun ζ => G ζ (p ζ)) z := hpA.sub hpB
  have haG : DifferentiableAt ℂ (fun ζ => G ζ (a ζ)) z := haA.sub haB
  obtain ⟨hne, hgap⟩ := cepsScaledRootGap_frequency_inverse_budget dom hW hθ hD M lam hl hz hbs
  have hord := cepsScaledRootWeights_frequency_order dom hW hθ hD M lam hz hb hbs
  have hGp : ‖deriv (fun ζ => G ζ (p ζ)) z‖ * |lam| ≤ (C * (1 + |lam|) * E * e) := by
    have h := cepsScaledRootEvaluation_frequency_deriv_error_budget dom hW hθ hD hf hη hM N hN
      lam hz hb hbs (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hord (by positivity : 0 ≤ C * (1 + |lam|))) he)
  have hGa : ‖deriv (fun ζ => G ζ (a ζ)) z‖ * |lam| ≤ (C * (1 + |lam|) * E * e) :=
    cepsScaledRootEvaluation_frequency_deriv_error_budget dom hW hθ hD hf hη hM N hN
      lam hz hb hbs (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  have hslope : dslope (G z) (a z) (p z) =
      cepsScaledTrueDenominator dom ρW lam z b - cepsScaledSurrogateDenominator dom ρW N lam z b :=
    dslope_sub_complex_of_ne _ _ hne
  have hSG : ‖dslope (G z) (a z) (p z)‖ ≤ 2 * S * E * e := by
    rw [hslope]
    have h := cepsScaledTrueDenominator_error_budget dom hW hθ hD hf hη hM N hN lam hz hbN
    apply h.trans
    calc
      _ ≤ S * e * (E + E) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hord) (mul_nonneg hS he)
      _ = _ := by ring
  have hgapD : ‖deriv p z - deriv a z‖ * |lam| ≤ 2 * R := by
    apply (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (abs_nonneg lam)).trans
    rw [add_mul]
    exact (add_le_add
      (cepsScaledSignedRoot_frequency_deriv_drift_budget dom hW hθ hD M lam hz (Or.inl hl) hb hbs (by norm_num : ‖(1 : ℂ)‖ ≤ 1))
      (cepsScaledSignedRoot_frequency_deriv_drift_budget dom hW hθ hD M lam hz (Or.inl hl) hb hbs (by norm_num : ‖(-1 : ℂ)‖ ≤ 1))).trans_eq
        (by dsimp only [R, CepsCanonDomain.rootFrequencyConstant]; ring)
  have hd := norm_deriv_moving_dslope_mul_sq_le (G := G) (a := a) (p := p)
    ha.differentiableAt.hasDerivAt hp.differentiableAt.hasDerivAt haG.hasDerivAt hpG.hasDerivAt hne
    (abs_nonneg lam) hgap hGa hGp hSG hgapD
  have hev : ∀ᶠ ζ in 𝓝 z, p ζ ≠ a ζ := by
    have h := (hp.continuousAt.sub ha.continuousAt).eventually_ne (sub_ne_zero.mpr hne)
    exact h.mono fun ζ hζ => sub_ne_zero.mp hζ
  have heq : (fun ζ => dslope (G ζ) (a ζ) (p ζ)) =ᶠ[𝓝 z]
      (fun ζ => cepsScaledTrueDenominator dom ρW lam ζ b - cepsScaledSurrogateDenominator dom ρW N lam ζ b) := by
    filter_upwards [hev] with ζ hζ
    exact dslope_sub_complex_of_ne _ _ hζ
  rw [heq.deriv_eq] at hd
  apply hd.trans
  calc
    _ = K * (2 * C * (1 + |lam|) + 4 * S * R) * E * e := by ring
    _ ≤ K * ((2 * C + 4 * S * R) * (1 + |lam|)) * E * e := by
      gcongr
      nlinarith [mul_nonneg (mul_nonneg hS hR) (abs_nonneg lam)]
    _ = _ := by unfold CepsCanonDomain.denominatorFrequencyErrorConstant; dsimp only [K, C, S, R, E, e, a, w]; ring

end PGM
