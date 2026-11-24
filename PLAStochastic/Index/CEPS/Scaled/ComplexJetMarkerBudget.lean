import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetPolynomialBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetDependence

/-! # Uniform finite-coordinate marked canonical exponential budgets -/

noncomputable section
open Complex
namespace PGM

/-- These are actual marked arguments. No root chart or probability realization is used. -/
theorem cepsComplexKernelMarker_arguments {lam : ℝ} {z b : ℂ}
    (hb : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ (1 / 2 : ℝ)) :
    ‖b * (lam : ℂ)‖ ≤ 1 ∧ ‖cepsComplexScaledDiscount lam z b‖ ≤ 1 ∧ ‖b ^ 2 * z‖ ≤ 1 := by
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hlX : |lam| ≤ X := by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖]
  have hsX : Real.sqrt ‖z‖ ≤ X := by dsimp [X]; linarith [abs_nonneg lam]
  have hbl : ‖b‖ * |lam| ≤ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hlX (norm_nonneg b)).trans hb
  have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ (1 / 2 : ℝ) :=
    (mul_le_mul_of_nonneg_left hsX (norm_nonneg b)).trans hb
  have hμ : ‖b * (lam : ℂ)‖ ≤ 1 := by rw [norm_mul, norm_real, Real.norm_eq_abs]; linarith
  have hζ : ‖b ^ 2 * z‖ ≤ (1 / 2 : ℝ) := by
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖b‖ * Real.sqrt ‖z‖) hbs 2
    rw [mul_pow, Real.sq_sqrt (norm_nonneg z)] at hs
    rw [norm_mul, norm_pow]
    linarith
  have hw : ‖1 + b * (lam : ℂ)‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  refine ⟨hμ, ?_, by linarith⟩
  rw [cepsComplexScaledDiscount, norm_mul]
  exact (mul_le_mul hζ hw (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem cepsComplexKernelMarker_exp_uniform_budget (d N : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (p : Fin d → ℂ) (hp : ‖p‖ ≤ M) (lam : ℝ) (z b : ℂ)
    (hb : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ (1 / 2 : ℝ)) :
    ‖exp (cepsCanonComplexJetPolynomial (cepsComplexJetPad d p) N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))‖ ≤ Real.exp (((N : ℝ) + 1) ^ 3 * M) := by
  obtain ⟨hμ, hq, hζ⟩ := cepsComplexKernelMarker_arguments hb
  have hL := cepsCanonComplexJetPolynomial_norm_le N hM
    (fun j _ m _ n _ => cepsComplexJetPad_norm_le hM hp (cepsJetCode (.inr (j, m, n)))) hμ hq hζ
  rw [norm_exp]
  exact Real.exp_le_exp.mpr ((re_le_norm _).trans hL)

end PGM
