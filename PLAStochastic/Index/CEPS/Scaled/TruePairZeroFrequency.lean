import PLAStochastic.Index.CEPS.Scaled.TrueHalfZeroFrequency
import PLAStochastic.Index.CEPS.Scaled.TimePairFrequencyBound
import PLAStochastic.Index.CEPS.Scaled.TrueSubtractedPair

/-! # Actual complete kernels on a quantitative zero-frequency disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.truePairZeroFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp (2 * dom.trueHalfZeroFrequencyBase) * (9 * dom.normalNegativeEntranceBound) ^ 2 *
    (8 * dom.trueFrequencyBridgeConstant / dom.scaledFrequencyRadius + dom.trueFrequencyBridgeConstant)

def CepsCanonDomain.trueHalfPairZeroFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp (2 * dom.trueHalfZeroFrequencyBase) * (2 * dom.trueHalfEntranceConstant) ^ 2 *
    (8 * dom.trueHalfFrequencyConstant / dom.positiveFrequencyRadius + dom.trueHalfFrequencyConstant)

def CepsCanonDomain.trueSubtractedPairZeroFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.truePairZeroFrequencyConstant + dom.trueHalfPairZeroFrequencyConstant

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueHalfZeroFrequency_le_half_positive {b : ℝ} (hb1 : b ≤ 1) :
    dom.trueHalfZeroFrequencyBase * b ≤ dom.positiveFrequencyRadius / 2 :=
  (mul_le_of_le_one_right (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le hb1).trans
    ((min_le_right _ _).trans (min_le_left _ _))

include hW hθ hD in
theorem trueSubtractedPairZeroFrequencyConstant_nonneg :
    0 ≤ dom.trueSubtractedPairZeroFrequencyConstant := by
  have := (trueFrequencyBridgeConstant_pos dom hW hθ hD).le
  have := (trueHalfFrequencyConstant_pos dom hW hθ hD).le
  have := (scaledFrequencyRadius_pos dom hD).le
  have := (positiveFrequencyRadius_pos dom hW hθ hD).le
  unfold CepsCanonDomain.trueSubtractedPairZeroFrequencyConstant
    CepsCanonDomain.truePairZeroFrequencyConstant CepsCanonDomain.trueHalfPairZeroFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledTruePair_zero_frequency_budget (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTruePair dom ρW lam ζ b)
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) ∧
    ∀ ζ ∈ ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b),
      ‖cepsScaledTruePair dom ρW lam ζ b‖ ≤ dom.truePairZeroFrequencyConstant / b ^ 2 * (1 + |lam|) := by
  have hE := trueHalfZeroFrequency_disc_subset_entrance dom hW hθ hD hb1
  have hhalf := (trueHalfZeroFrequency_le_half_positive dom hW hθ hD hb1).trans
    (div_le_div_of_nonneg_right (positiveFrequencyRadius_le dom) (by norm_num))
  have hR : ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b) ⊆ ball 0 dom.scaledFrequencyRadius :=
    ball_subset_ball (hhalf.trans (half_le_self (scaledFrequencyRadius_pos dom hD).le))
  have hH := (cepsScaledTrueEntrance_differentiableOn_zero_frequency_disc dom hW hθ hD M lam hb hb1 hbs).mono hE
  have hU := cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M lam (by simp) hb hbs
  have hdE : DifferentiableOn ℂ (fun ζ : ℂ => exp (((b : ℂ) * ζ) * (1 + (b : ℂ) * lam)))
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) := by fun_prop
  have hdO := ((hU.deriv isOpen_ball).mono hR).const_mul (-(1 / (1 + (b : ℂ) * lam)))
  refine ⟨hdE.mul (hH.pow 2) |>.mul (hdO.sub ((hU.mono hR).const_mul (b : ℂ))), ?_⟩
  intro ζ hζ
  have hHn := cepsScaledTrueEntrance_zero_frequency_bound dom hW hθ hD M lam hb hb1 hbs (hE hζ)
  have hUn : ‖cepsScaledTrueBridge dom ρW lam ζ b‖ ≤ dom.trueFrequencyBridgeConstant * (1 + |lam|) := by
    simpa only [norm_zero, Real.sqrt_zero, add_zero] using
      cepsScaledTrueBridge_frequency_disc_budget dom hW hθ hD M lam (by simp) hb hbs (hR hζ)
  have hUd : ‖deriv (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) ζ‖ ≤
      (4 * dom.trueFrequencyBridgeConstant / dom.scaledFrequencyRadius) * (1 + |lam|) := by
    have ht := norm_deriv_le_of_ball_half (scaledFrequencyRadius_pos dom hD) hU
      (fun ζ hζ => cepsScaledTrueBridge_frequency_disc_budget dom hW hθ hD M lam (by simp) hb hbs hζ)
      (ball_subset_ball hhalf hζ)
    simp only [norm_zero, Real.sqrt_zero, add_zero] at ht
    exact ht.trans_eq (by ring)
  obtain ⟨_, _, _, _, hwlo, hwhi, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs
  have hzR : ‖ζ‖ ≤ dom.trueHalfZeroFrequencyBase :=
    (mem_ball_zero_iff.mp hζ).le.trans (mul_le_of_le_one_right (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le hb1)
  simpa only [cepsScaledTruePair, CepsCanonDomain.truePairZeroFrequencyConstant,
    show 2 * (4 * dom.trueFrequencyBridgeConstant / dom.scaledFrequencyRadius) + dom.trueFrequencyBridgeConstant =
      8 * dom.trueFrequencyBridgeConstant / dom.scaledFrequencyRadius + dom.trueFrequencyBridgeConstant by ring] using
    cepsNorm_completeTimePair_frequency_bound hb hb1 hwlo hwhi hzR hHn hUn hUd

include hW hθ hD in
theorem cepsScaledTrueHalfPair_zero_frequency_budget (M lam : ℝ) (hlam : 1 ≤ lam) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueHalfPair dom ρW lam ζ b)
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) ∧
    ∀ ζ ∈ ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b),
      ‖cepsScaledTrueHalfPair dom ρW lam ζ b‖ ≤ dom.trueHalfPairZeroFrequencyConstant / b ^ 2 * (1 + |lam|) := by
  have hhalf := trueHalfZeroFrequency_le_half_positive dom hW hθ hD hb1
  have hR := trueHalfZeroFrequency_disc_subset_positive dom hW hθ hD hb1
  obtain ⟨hH, hHb⟩ := cepsScaledTrueHalfEntrance_zero_frequency_budget dom hW hθ hD M lam hlam hb hb1 hbs
  have hU := cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M lam hlam (by simp) hb hbs
  have hdE : DifferentiableOn ℂ (fun ζ : ℂ => exp (((b : ℂ) * ζ) * (1 + (b : ℂ) * lam)))
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) := by fun_prop
  have hdO := ((hU.deriv isOpen_ball).mono hR).const_mul (-(1 / (1 + (b : ℂ) * lam)))
  refine ⟨hdE.mul (hH.pow 2) |>.mul (hdO.sub ((hU.mono hR).const_mul (b : ℂ))), ?_⟩
  intro ζ hζ
  have hHn : ‖cepsScaledTrueHalfEntrance dom ρW lam ζ b‖ ≤ (2 * dom.trueHalfEntranceConstant) / b :=
    (hHb ζ hζ).trans ((le_div_iff₀ hb).mpr
      (mul_le_of_le_one_right (by have := trueHalfEntranceConstant_pos dom hW hθ hD; positivity) hb1))
  have hUn : ‖cepsScaledTrueHalfBridge dom ρW lam ζ b‖ ≤ dom.trueHalfFrequencyConstant * (1 + |lam|) := by
    simpa only [norm_zero, Real.sqrt_zero, add_zero] using
      cepsScaledTrueHalfBridge_frequency_budget dom hW hθ hD M lam (by simp) hb hbs
        (ball_subset_ball (positiveFrequencyRadius_le dom) (hR hζ))
  have hUd : ‖deriv (fun ζ => cepsScaledTrueHalfBridge dom ρW lam ζ b) ζ‖ ≤
      (4 * dom.trueHalfFrequencyConstant / dom.positiveFrequencyRadius) * (1 + |lam|) := by
    have ht := norm_deriv_le_of_ball_half (positiveFrequencyRadius_pos dom hW hθ hD) hU
      (fun ζ hζ => cepsScaledTrueHalfBridge_frequency_budget dom hW hθ hD M lam (by simp) hb hbs
        (ball_subset_ball (positiveFrequencyRadius_le dom) hζ)) (ball_subset_ball hhalf hζ)
    simp only [norm_zero, Real.sqrt_zero, add_zero] at ht
    exact ht.trans_eq (by ring)
  obtain ⟨_, _, _, _, hwlo, hwhi, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam (by simp) hb hbs
  have hzR : ‖ζ‖ ≤ dom.trueHalfZeroFrequencyBase :=
    (mem_ball_zero_iff.mp hζ).le.trans (mul_le_of_le_one_right (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le hb1)
  simpa only [cepsScaledTrueHalfPair, cepsScaledTimeOperator, CepsCanonDomain.trueHalfPairZeroFrequencyConstant,
    show 2 * (4 * dom.trueHalfFrequencyConstant / dom.positiveFrequencyRadius) + dom.trueHalfFrequencyConstant =
      8 * dom.trueHalfFrequencyConstant / dom.positiveFrequencyRadius + dom.trueHalfFrequencyConstant by ring] using
    cepsNorm_completeTimePair_frequency_bound hb hb1 hwlo hwhi hzR hHn hUn hUd

include hW hθ hD in
theorem cepsScaledTrueSubtractedPair_zero_frequency_budget (M lam : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueSubtractedPair dom ρW lam ζ b)
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) ∧
    ∀ ζ ∈ ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b),
      ‖cepsScaledTrueSubtractedPair dom ρW lam ζ b‖ ≤
        dom.trueSubtractedPairZeroFrequencyConstant / b ^ 2 * (1 + |lam|) := by
  obtain ⟨hF, hFb⟩ := cepsScaledTruePair_zero_frequency_budget dom hW hθ hD M lam hb hb1 hbs
  by_cases hlam : 1 ≤ lam
  · obtain ⟨hH, hHb⟩ := cepsScaledTrueHalfPair_zero_frequency_budget dom hW hθ hD M lam hlam hb hb1 hbs
    simp only [cepsScaledTrueSubtractedPair, if_pos hlam]
    refine ⟨hF.sub hH, fun ζ hζ => ?_⟩
    exact (norm_sub_le _ _).trans ((add_le_add (hFb ζ hζ) (hHb ζ hζ)).trans_eq (by
      unfold CepsCanonDomain.trueSubtractedPairZeroFrequencyConstant
      ring))
  · simp only [cepsScaledTrueSubtractedPair, if_neg hlam]
    refine ⟨hF, fun ζ hζ => (hFb ζ hζ).trans ?_⟩
    have hK : 0 ≤ dom.trueHalfPairZeroFrequencyConstant := by
      have := (trueHalfFrequencyConstant_pos dom hW hθ hD).le
      have := (positiveFrequencyRadius_pos dom hW hθ hD).le
      unfold CepsCanonDomain.trueHalfPairZeroFrequencyConstant
      positivity
    unfold CepsCanonDomain.trueSubtractedPairZeroFrequencyConstant
    gcongr
    exact le_add_of_nonneg_right hK

end PGM
