import PLAStochastic.Index.CEPS.Scaled.ComplexRootFrequencyDerivative
import PLAStochastic.Index.CEPS.Scaled.EntranceScaleCurve

/-! # Small canonical arguments for complex-scale frequency curves -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem complexFrequencyCurve_canon_mem (N : ℕ) (M lam : ℝ) {z b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    b ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z / 2) :=
  ball_subset_ball ((min_le_right _ _).trans
    (by have := (canonScaleRadius_pos dom hW hθ hD lam z).le; linarith)) hb

include hW hθ hD in
theorem complexFrequencyCurve_small (N : ℕ) (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖b * (lam : ℂ)‖ ≤ dom.μ₀ / 8 ∧
      ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ / 4 ∧
      ‖b * cepsScaledSignedRoot D θ ρW lam z sign b‖ ≤ dom.c₀ / 4 ∧
      ‖b‖ ≤ 1 ∧ ‖1 + b * (lam : ℂ)‖ ≤ 2 := by
  let C := dom.actualScaledRootBound lam z
  let A := dom.canonScaleBase
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hroot := (cepsScaledSignedRoot_budget dom hW hθ hD lam hz hsign).2 b
    (ball_subset_ball (min_le_left _ _) hbC)
  have hC : 0 ≤ C := (norm_nonneg _).trans hroot
  have ht := entranceScaleCurve_product_bound dom hD N M lam hb
  have hA1 : A ≤ 1 := min_le_left _ _
  have hAm : A ≤ dom.μ₀ / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hAq : A ≤ dom.q₀ / 8 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hAc : A ≤ dom.c₀ / 4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hA0 : 0 ≤ A := by
    have := dom.μ₀_pos
    have := dom.q₀_pos
    have := dom.c₀_pos
    unfold A CepsCanonDomain.canonScaleBase
    positivity
  have hb1 : ‖b‖ ≤ 1 := by nlinarith [norm_nonneg b, abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hbl : ‖b‖ * |lam| ≤ A := by
    nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hC,
      mul_nonneg (norm_nonneg b) (Real.sqrt_nonneg ‖z‖)]
  have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ A := by
    nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) hC,
      mul_nonneg (norm_nonneg b) (abs_nonneg lam)]
  have hbR : ‖b‖ * C ≤ A := by
    nlinarith [norm_nonneg b, mul_nonneg (norm_nonneg b) (Real.sqrt_nonneg ‖z‖),
      mul_nonneg (norm_nonneg b) (abs_nonneg lam)]
  have hw : ‖1 + b * (lam : ℂ)‖ ≤ 2 := by
    have hn := norm_add_le (1 : ℂ) (b * lam)
    rw [norm_one, norm_mul, norm_real, Real.norm_eq_abs] at hn
    linarith
  have hbz : ‖b‖ ^ 2 * ‖z‖ ≤ A := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖b‖ * Real.sqrt ‖z‖) hbs 2
    rw [mul_pow, Real.sq_sqrt (norm_nonneg z)] at hs
    exact hs.trans (by nlinarith)
  refine ⟨by simpa only [norm_mul, norm_real, Real.norm_eq_abs] using hbl.trans hAm,
    ?_, ?_, hb1, hw⟩
  · rw [cepsComplexScaledDiscount, norm_mul, norm_mul, norm_pow]
    exact (mul_le_mul hbz hw (norm_nonneg _) hA0).trans (by linarith)
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left hroot (norm_nonneg b)).trans (hbR.trans hAc)

end PGM
