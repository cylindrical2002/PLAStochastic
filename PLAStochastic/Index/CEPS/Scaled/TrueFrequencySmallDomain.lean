import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyDisc

/-! # Interior canonical discount and root budgets on the fixed actual disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueFrequency_small_canonical_domain (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) :
    |b * lam| ≤ dom.μ₀ / 8 ∧ ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ / 4 ∧
      b ≤ 1 ∧ ‖(1 + (b : ℂ) * lam : ℂ)‖ ≤ 2 ∧
      ‖(b : ℂ) * cepsScaledSignedRoot D θ ρW lam z 1 b‖ ≤ dom.c₀ / 4 ∧
      ‖(b : ℂ) * cepsScaledSignedRoot D θ ρW lam z (-1) b‖ ≤ dom.c₀ / 4 := by
  obtain ⟨hμ, hq, _, _, hwlo, hwhi, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hbE := ball_subset_ball (trueDenominatorScaleRadius_le dom hW hθ hD M lam z)
    (ball_subset_ball (truePairScaleRadius_le dom M lam z)
      (ball_subset_ball (trueFrequencyScaleRadius_le dom M lam z) hbs))
  have hbC := ball_subset_ball ((min_le_right _ _).trans
    (div_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le (by norm_num))) hbE
  have hμs := (canonScaleCurve_bounds dom hW hθ hD lam hz (sign := 1) (by norm_num) hbC).1
  have hμsmall : |b * lam| ≤ dom.μ₀ / 8 := by
    simpa only [← ofReal_mul, norm_real, Real.norm_eq_abs] using hμs.le
  have hp := entranceScaleCurve_product_bound dom hD 0 M lam hbE
  rw [norm_real, Real.norm_eq_abs, abs_of_pos hb] at hp
  have hC : 0 ≤ dom.actualScaledRootBound lam z := by
    unfold CepsCanonDomain.actualScaledRootBound
    have := cepsVarLo_pos hD
    have := cepsChartK_pos hD
    have : 0 ≤ dom.scaledRootCoordinateBound lam z := Real.sqrt_nonneg _
    positivity
  have hA1 : dom.canonScaleBase ≤ 1 := min_le_left _ _
  have hAq : dom.canonScaleBase ≤ dom.q₀ / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hb1 : b ≤ 1 := by nlinarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hX : b * Real.sqrt ‖z‖ ≤ dom.canonScaleBase / 8 := by
    nlinarith [abs_nonneg lam]
  have hX0 : 0 ≤ b * Real.sqrt ‖z‖ := mul_nonneg hb.le (Real.sqrt_nonneg _)
  have hX1 : b * Real.sqrt ‖z‖ ≤ 1 := by linarith
  have hbz : b ^ 2 * ‖z‖ ≤ dom.canonScaleBase / 8 := by
    nlinarith [Real.sq_sqrt (norm_nonneg z), mul_nonneg hX0 (by linarith : 0 ≤ 1 - b * Real.sqrt ‖z‖)]
  have hw : ‖(1 + (b : ℂ) * lam : ℂ)‖ ≤ 2 := by
    rw [show (1 + (b : ℂ) * lam : ℂ) = ((1 + b * lam : ℝ) : ℂ) by simp [ofReal_mul],
      norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 + b * lam)]
    exact hwhi
  have hqsmall : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ / 4 := by
    rw [cepsComplexScaledDiscount, norm_mul, norm_mul, norm_pow, norm_real,
      Real.norm_eq_abs, abs_of_pos hb]
    calc
      _ ≤ (dom.canonScaleBase / 8) * 2 := mul_le_mul hbz hw (norm_nonneg _) (by linarith)
      _ ≤ dom.q₀ / 4 := by linarith [dom.q₀_pos]
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hμc := dom.μ_lt_chart hμn
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hpactual : (b : ℂ) * cepsScaledSignedRoot D θ ρW lam z 1 b =
      cepsRootPlus D θ ρW (b * lam : ℝ) (cepsComplexScaledDiscount lam z b) := by
    rw [cepsScaledSignedRoot_plus_actual hW hθ hD hb hμc, mul_div_cancel₀ _ hb0]
    simp only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  have hmactual : (b : ℂ) * cepsScaledSignedRoot D θ ρW lam z (-1) b =
      cepsRootMinus D θ ρW (b * lam : ℝ) (cepsComplexScaledDiscount lam z b) := by
    rw [cepsScaledSignedRoot_minus_actual hW hθ hD hb hμc, mul_div_cancel₀ _ hb0]
    simp only [cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  refine ⟨hμsmall, hqsmall, hb1, hw, ?_, ?_⟩
  · rw [hpactual]
    exact dom.norm_rootPlus_le hW hθ hD hμn (hq.trans (half_le_self dom.q₀_pos.le))
  · rw [hmactual]
    exact dom.norm_rootMinus_le hW hθ hD hμn (hq.trans (half_le_self dom.q₀_pos.le))

end PGM
