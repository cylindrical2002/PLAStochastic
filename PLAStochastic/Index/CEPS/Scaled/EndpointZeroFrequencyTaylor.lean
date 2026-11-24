import PLAStochastic.Index.CEPS.Scaled.TrueHalfZeroFrequency
import PLAStochastic.Index.CEPS.Scaled.EndpointZeroDerivative

/-! # Genuine actual marked-endpoint Taylor bounds at zero frequency -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueEndpointZeroFrequencyBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.trueHalfZeroFrequencyBase (cepsMarkedUnitRadius D θ)

def CepsCanonDomain.trueEndpointZeroFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp (2 * dom.trueHalfZeroFrequencyBase) * Real.exp dom.normalLogBound *
    (2 * dom.trueHalfEntranceConstant) * (2 * dom.trueHalfFrequencyConstant)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueEndpointZeroFrequencyBase_pos : 0 < dom.trueEndpointZeroFrequencyBase :=
  lt_min (trueHalfZeroFrequencyBase_pos dom hW hθ hD) (cepsMarkedUnitRadius_pos hD hθ)

include hW hθ hD in
theorem trueEndpointZeroFrequencyConstant_nonneg : 0 ≤ dom.trueEndpointZeroFrequencyConstant := by
  have := (trueHalfEntranceConstant_pos dom hW hθ hD).le
  have := (trueHalfFrequencyConstant_pos dom hW hθ hD).le
  unfold CepsCanonDomain.trueEndpointZeroFrequencyConstant
  positivity

theorem cepsScaledTrueRegularEndpoint_eq_half_product (z : ℂ) (b : ℝ) :
    cepsScaledTrueRegularEndpoint dom ρW z b =
      exp (((b : ℂ) * z) * (1 + (b : ℂ))) *
        exp (dom.canonL ρW b (cepsComplexScaledDiscount 1 z b) ((b : ℂ) ^ 2 * z)) *
          cepsScaledTrueHalfEntrance dom ρW 1 z b * cepsScaledTrueHalfBridge dom ρW 1 z b := by
  unfold cepsScaledTrueRegularEndpoint cepsScaledTrueHalfEntrance cepsScaledTrueHalfBridge
  ring

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_zero_frequency_budget (M : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M 1 0)) :
    DifferentiableOn ℂ (fun ζ => cepsScaledTrueRegularEndpoint dom ρW ζ b)
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) ∧
    ∀ ζ ∈ ball (0 : ℂ) (dom.trueHalfZeroFrequencyBase * b),
      ‖cepsScaledTrueRegularEndpoint dom ρW ζ b‖ ≤ dom.trueEndpointZeroFrequencyConstant := by
  have hE := trueHalfZeroFrequency_disc_subset_entrance dom hW hθ hD hb1
  have hP := trueHalfZeroFrequency_disc_subset_positive dom hW hθ hD hb1
  obtain ⟨hL, hLb⟩ := cepsScaledTrueMarkLog_zero_frequency_budget dom hW hθ hD M 1 hb hb1 hbs
  obtain ⟨hH, hHb⟩ := cepsScaledTrueHalfEntrance_zero_frequency_budget dom hW hθ hD M 1 le_rfl hb hb1 hbs
  have hU := (cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M 1 le_rfl
    (by simp) hb hbs).mono hP
  have hdE : DifferentiableOn ℂ (fun ζ : ℂ => exp (((b : ℂ) * ζ) * (1 + (b : ℂ))))
      (ball 0 (dom.trueHalfZeroFrequencyBase * b)) := by fun_prop
  refine ⟨?_, ?_⟩
  · apply ((hdE.mul ((hL.mono hE).cexp)).mul hH |>.mul hU).congr
    intro ζ _
    simpa only [mul_one, ofReal_one, Pi.mul_apply] using cepsScaledTrueRegularEndpoint_eq_half_product dom ζ b
  · intro ζ hζ
    have hz : ‖ζ‖ ≤ dom.trueHalfZeroFrequencyBase := (mem_ball_zero_iff.mp hζ).le.trans
      (mul_le_of_le_one_right (trueHalfZeroFrequencyBase_pos dom hW hθ hD).le hb1)
    have he : ‖exp (((b : ℂ) * ζ) * (1 + (b : ℂ)))‖ ≤ Real.exp (2 * dom.trueHalfZeroFrequencyBase) := by
      rw [norm_exp]
      apply Real.exp_le_exp.mpr
      apply (re_le_norm _).trans
      rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb,
        ← ofReal_one, ← ofReal_add, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 1 + b)]
      calc
        _ ≤ 1 * ‖ζ‖ * 2 := by gcongr; linarith
        _ ≤ _ := by linarith
    have hLn : ‖exp (dom.canonL ρW b (cepsComplexScaledDiscount 1 ζ b) ((b : ℂ) ^ 2 * ζ))‖ ≤
        Real.exp dom.normalLogBound := by
      rw [norm_exp]
      apply Real.exp_le_exp.mpr
      simpa only [mul_one, ofReal_one] using (re_le_norm _).trans (hLb ζ (hE hζ))
    have hUn : ‖cepsScaledTrueHalfBridge dom ρW 1 ζ b‖ ≤ 2 * dom.trueHalfFrequencyConstant := by
      have ht := cepsScaledTrueHalfBridge_frequency_budget dom hW hθ hD M 1 (by simp) hb hbs
        (ball_subset_ball (positiveFrequencyRadius_le dom) (hP hζ))
      simp only [norm_zero, Real.sqrt_zero, add_zero, abs_one] at ht
      exact ht.trans_eq (by ring)
    rw [cepsScaledTrueRegularEndpoint_eq_half_product, norm_mul, norm_mul, norm_mul]
    exact (mul_le_mul (mul_le_mul (mul_le_mul he hLn (norm_nonneg _) (Real.exp_pos _).le)
      (hHb ζ hζ) (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) hUn
      (norm_nonneg _) (by have := trueHalfEntranceConstant_pos dom hW hθ hD; positivity))

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_zero_frequency_taylor (M : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M 1 0)) {z : ℂ}
    (hz : z ∈ ball 0 (dom.trueEndpointZeroFrequencyBase * b / 2)) :
    ‖cepsScaledMarkedEndpoint dom ρW b z - 1 + z * cepsScaledZeroEndpoint dom ρW b‖ ≤
      (32 * dom.trueEndpointZeroFrequencyConstant / (dom.trueEndpointZeroFrequencyBase * b) ^ 2) * ‖z‖ ^ 2 := by
  have hbase := trueEndpointZeroFrequencyBase_pos dom hW hθ hD
  have hsub : ball (0 : ℂ) (dom.trueEndpointZeroFrequencyBase * b) ⊆
      ball 0 (dom.trueHalfZeroFrequencyBase * b) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right (min_le_left _ _) hb.le)
  obtain ⟨hd, hbound⟩ := cepsScaledTrueRegularEndpoint_zero_frequency_budget dom hW hθ hD M hb hb1 hbs
  have ht := norm_sub_sub_deriv_le_of_ball (mul_pos hbase hb) (hd.mono hsub)
    (fun ζ hζ => hbound ζ (hsub hζ)) hz
  have hμ : |b| ≤ dom.μ₀ := by
    simpa only [mul_one] using (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M 1 (by simp) hb hbs).1
  have hq := (cepsScaledTrueFrequency_discount_disc dom hW hθ hD M 1 (by simp) hb hbs
    (ball_subset_ball (trueEntranceFrequencyRadius_le dom)
      ((trueHalfZeroFrequency_disc_subset_entrance dom hW hθ hD hb1)
        (hsub (ball_subset_ball (half_le_self (mul_pos hbase hb).le) hz))))).1.le
  have hmark : (b : ℂ) ^ 2 * z ∈ ball 0 (cepsMarkedUnitRadius D θ) := by
    rw [mem_ball_zero_iff, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hb]
    have hb2 : b ^ 2 ≤ 1 := by nlinarith
    have hn := mem_ball_zero_iff.mp hz
    have hbR : dom.trueEndpointZeroFrequencyBase * b / 2 ≤ cepsMarkedUnitRadius D θ :=
      (half_le_self (mul_pos hbase hb).le).trans
        ((mul_le_of_le_one_right hbase.le hb1).trans (min_le_right _ _))
    exact (mul_le_mul_of_nonneg_right hb2 (norm_nonneg z)).trans_lt (by simpa using hn.trans_le hbR)
  rw [cepsScaledTrueRegularEndpoint_eq_filled_all_marks dom hW hθ hD hb hμ hq hmark,
    cepsScaledTrueRegularEndpoint_zero_mark dom hW hθ hD hb hμ,
    (cepsScaledTrueRegularEndpoint_hasDerivAt_mark_zero dom hW hθ hD hb hμ).deriv] at ht
  simpa only [sub_zero, neg_mul, mul_neg, sub_neg_eq_add, mul_comm] using ht

include hW hθ hD in
theorem cepsScaledZeroEndpoint_zero_frequency_bound (M : ℝ) {b : ℝ}
    (hb : 0 < b) (hb1 : b ≤ 1)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M 1 0)) :
    ‖cepsScaledZeroEndpoint dom ρW b‖ ≤
      2 * dom.trueEndpointZeroFrequencyConstant / (dom.trueHalfZeroFrequencyBase * b) := by
  obtain ⟨hd, hbound⟩ := cepsScaledTrueRegularEndpoint_zero_frequency_budget dom hW hθ hD M hb hb1 hbs
  have ht := norm_iteratedDeriv_le_of_ball 1
    (mul_pos (trueHalfZeroFrequencyBase_pos dom hW hθ hD) hb) hd hbound
  have hμ : |b| ≤ dom.μ₀ := by
    simpa only [mul_one] using (cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M 1 (by simp) hb hbs).1
  rw [iteratedDeriv_one, (cepsScaledTrueRegularEndpoint_hasDerivAt_mark_zero dom hW hθ hD hb hμ).deriv,
    norm_neg] at ht
  exact ht.trans_eq (by simp only [Nat.factorial_one, Nat.cast_one, one_mul, pow_one]; ring)

end PGM
