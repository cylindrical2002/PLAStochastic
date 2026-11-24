import PLAStochastic.Index.CEPS.Scaled.DenominatorFrequencyError

/-! # Actual divided-denominator frequency derivative budgets -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueDenominatorFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M : ℝ) : ℝ :=
  dom.rootFrequencyGapInverseConstant *
    (2 * (v * Real.exp (2 * dom.normalLogBound)) * dom.rootFrequencyChainConstant +
      4 * dom.trueSpatialBound M 1 * dom.rootFrequencyConstant)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledDenominators_frequency_differentiableAt {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    (M lam : ℝ) (hlam : lam ≠ 0) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    DifferentiableAt ℂ (fun ζ => cepsScaledTrueDenominator dom ρW lam ζ b) z ∧
      DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateDenominator dom ρW N lam ζ b) z := by
  have hp := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hlam) hb hbs
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have ha := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hlam) hb hbs
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)
  obtain ⟨hpA, hpB⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N
    hN M lam hz (Or.inl hlam) hb hbs (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
  obtain ⟨haA, haB⟩ := cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη N
    hN M lam hz (Or.inl hlam) hb hbs (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  have hne := (cepsScaledRootGap_frequency_inverse_budget dom hW hθ hD M lam hlam hz hbs).1
  exact ⟨(hasDerivAt_moving_dslope_of_ne ha hp haA.hasDerivAt hpA.hasDerivAt hne).differentiableAt,
    (hasDerivAt_moving_dslope_of_ne ha hp haB.hasDerivAt hpB.hasDerivAt hne).differentiableAt⟩

include hW hθ hD in
theorem cepsScaledTrueDenominator_frequency_deriv_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) (lam : ℝ) (hlam : lam ≠ 0)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    ‖deriv (fun ζ => cepsScaledTrueDenominator dom ρW lam ζ b) z‖ * |lam| ^ 2 ≤
      dom.trueDenominatorFrequencyConstant M * (1 + |lam|) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + (b : ℂ) * lam)).re) := by
  let p : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ 1 b
  let a : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ (-1) b
  let G : ℂ → ℂ → ℂ := fun ζ => cepsScaledTrueG dom ρW lam ζ b
  let w : ℂ := 1 + (b : ℂ) * lam
  let E := Real.exp (-(a z * w).re)
  let C := (v * Real.exp (2 * dom.normalLogBound)) * dom.rootFrequencyChainConstant
  let S := dom.trueSpatialBound M 1
  let R := dom.rootFrequencyConstant
  let K := dom.rootFrequencyGapInverseConstant
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hS : 0 ≤ S := trueSpatialBound_nonneg dom hW hθ hD hM0 1
  have hR : 0 ≤ R := by have := cepsChartK_pos hD; unfold R CepsCanonDomain.rootFrequencyConstant; positivity
  have hK : 0 ≤ K := by unfold K CepsCanonDomain.rootFrequencyGapInverseConstant; positivity
  have hC : 0 ≤ C := by
    have := dom.q₀_pos
    have := dom.c₀_pos
    have := CepsCanonDomain.v_pos hW hθ hD
    unfold C CepsCanonDomain.rootFrequencyChainConstant
    change 0 ≤ _ * (2 * R + R / (dom.c₀ / 8) + 2 / (dom.q₀ / 8))
    positivity
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hbD := ball_subset_ball (truePairScaleRadius_le dom M lam z)
    (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs)
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z) hbD
  have hp := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hlam) hb hbs
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1)
  have ha := cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hlam) hb hbs
    (by norm_num : ‖(-1 : ℂ)‖ ≤ 1)
  have hpG := (cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη 0
    (by omega) M lam hz (Or.inl hlam) hb hbs (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)).1
  have haG := (cepsScaledG_root_frequency_differentiableAt dom hW hθ hD hf hη 0
    (by omega) M lam hz (Or.inl hlam) hb hbs (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)).1
  obtain ⟨hne, hgap⟩ := cepsScaledRootGap_frequency_inverse_budget dom hW hθ hD M lam hlam hz hbs
  have hord := cepsScaledRootWeights_frequency_order dom hW hθ hD M lam hz hb hbs
  have hGp : ‖deriv (fun ζ => G ζ (p ζ)) z‖ * |lam| ≤ C * (1 + |lam|) * E := by
    have h := cepsScaledTrueG_root_frequency_deriv_budget dom hW hθ hD hf (by omega) hη M lam hz
      (Or.inl hlam) hb hbs (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1)
    exact h.trans (mul_le_mul_of_nonneg_left hord (by positivity : 0 ≤ C * (1 + |lam|)))
  have hGa : ‖deriv (fun ζ => G ζ (a ζ)) z‖ * |lam| ≤ C * (1 + |lam|) * E :=
    cepsScaledTrueG_root_frequency_deriv_budget dom hW hθ hD hf (by omega) hη M lam hz
      (Or.inl hlam) hb hbs (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1)
  have hSG : ‖dslope (G z) (a z) (p z)‖ ≤ 2 * S * E := by
    have hds : ‖dslope (G z) (a z) (p z)‖ ≤ S *
        (Real.exp (-(a z * w).re) + Real.exp (-(p z * w).re)) := by
      apply cepsNormal_norm_dslope_le_weighted (entranceScale_constants dom hW hθ hD 0 M lam z).2
        hS (cepsScaledTrueG_spatial_differentiableOn dom hW hθ hD 0 M lam hz hbE) _
        (entranceScaleCurve_root_norm_le_half dom hW hθ hD 0 M lam hz hbE (by norm_num))
        (entranceScaleCurve_root_norm_le_half dom hW hθ hD 0 M lam hz hbE (by norm_num))
      intro ξ hξ
      simpa only [iteratedDeriv_one] using cepsScaledTrueG_spatial_budget dom hW hθ hD hf hη hM hm lam hz hbD 1 hξ
    exact hds.trans ((mul_le_mul_of_nonneg_left (add_le_add le_rfl hord) hS).trans_eq (by ring))
  have hgapD : ‖deriv p z - deriv a z‖ * |lam| ≤ 2 * R := by
    apply (mul_le_mul_of_nonneg_right (norm_sub_le _ _) (abs_nonneg lam)).trans
    rw [add_mul]
    exact (add_le_add
      (cepsScaledSignedRoot_frequency_deriv_drift_budget dom hW hθ hD M lam hz (Or.inl hlam) hb hbs (by norm_num : ‖(1 : ℂ)‖ ≤ 1))
      (cepsScaledSignedRoot_frequency_deriv_drift_budget dom hW hθ hD M lam hz (Or.inl hlam) hb hbs (by norm_num : ‖(-1 : ℂ)‖ ≤ 1))).trans_eq
        (by dsimp only [R, CepsCanonDomain.rootFrequencyConstant]; ring)
  have hd := norm_deriv_moving_dslope_mul_sq_le (G := G) (a := a) (p := p)
    ha.differentiableAt.hasDerivAt hp.differentiableAt.hasDerivAt haG.hasDerivAt hpG.hasDerivAt hne
    (abs_nonneg lam) hgap hGa hGp hSG hgapD
  apply hd.trans
  calc
    _ = K * (2 * C * (1 + |lam|) + 4 * S * R) * E := by ring
    _ ≤ K * ((2 * C + 4 * S * R) * (1 + |lam|)) * E := by
      gcongr
      nlinarith [mul_nonneg (mul_nonneg hS hR) (abs_nonneg lam)]
    _ = _ := by unfold CepsCanonDomain.trueDenominatorFrequencyConstant; dsimp only [K, C, S, R, E, a, w]; ring

end PGM
