import PLAStochastic.Index.CEPS.Scaled.ComplexJetRoots
import PLAStochastic.ForMathlib.Analysis.Complex.SqrtScale

/-! # Exact positive-real drift-frequency homogeneity of finite Newton roots -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexCumulantRootBase_quadratic_equation (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ)
    (hv : p (cepsJetCode (.inl 0)) ≠ 0) (hsign : sign ^ 2 = 1) :
    cepsComplexCumulantRootBase p lam z sign ^ 2 * (p (cepsJetCode (.inl 0)) / 2) +
      (lam : ℂ) * cepsComplexCumulantRootBase p lam z sign = z := by
  let v := p (cepsJetCode (.inl 0))
  have hv' : v ≠ 0 := hv
  let t := sign * sqrt (2 / v) * sqrt (z + (lam : ℂ) ^ 2 / (2 * v))
  have ht : t ^ 2 = 2 * z / v + (lam : ℂ) ^ 2 / v ^ 2 := by
    dsimp [t]
    rw [mul_pow, mul_pow, sqrt_sq_eq, sqrt_sq_eq, hsign]
    field_simp [hv']
  change (-(lam : ℂ) / v + t) ^ 2 * (v / 2) +
    (lam : ℂ) * (-(lam : ℂ) / v + t) = z
  calc
    _ = v / 2 * t ^ 2 - (lam : ℂ) ^ 2 / (2 * v) := by
      field_simp [hv']
      ring
    _ = z := by
      rw [ht]
      field_simp [hv']
      ring

theorem cepsComplexCumulantRootBase_homogeneous (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ)
    {X : ℝ} (hX : 0 < X) :
    cepsComplexCumulantRootBase p (X * lam) ((X : ℂ) ^ 2 * z) sign =
      (X : ℂ) * cepsComplexCumulantRootBase p lam z sign := by
  have hr : (X : ℂ) ^ 2 * z + ((X * lam : ℝ) : ℂ) ^ 2 /
      (2 * p (cepsJetCode (.inl 0))) = (X : ℂ) ^ 2 *
        (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))) := by
    push_cast
    ring
  dsimp only [cepsComplexCumulantRootBase]
  rw [hr, complex_sqrt_sq_real_mul hX]
  push_cast
  ring

theorem cepsComplexCumulantRootGap_homogeneous (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ)
    {X : ℝ} (hX : 0 < X) :
    cepsComplexCumulantRootGap p (X * lam) ((X : ℂ) ^ 2 * z) sign =
      (X : ℂ) * cepsComplexCumulantRootGap p lam z sign := by
  unfold cepsComplexCumulantRootGap
  rw [cepsComplexCumulantRootBase_homogeneous p lam z sign hX]
  push_cast
  ring

/-- Rescaling the drift and frequency is exactly offset by rescaling the small parameter.
This equality holds for every finite Newton iteration, not only through a finite jet. -/
theorem cepsComplexCumulantRootModel_homogeneous (p : ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z sign : ℂ) {X : ℝ} (hX : 0 < X) (k : ℕ) (b : ℂ) :
    cepsComplexCumulantRootModel p N (X * lam) ((X : ℂ) ^ 2 * z) sign k b =
      (X : ℂ) * cepsComplexCumulantRootModel p N lam z sign k ((X : ℂ) * b) := by
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  induction k with
  | zero => exact cepsComplexCumulantRootBase_homogeneous p lam z sign hX
  | succ k ih =>
    simp only [cepsComplexCumulantRootModel, quadraticNewtonStep, ih,
      cepsComplexCumulantRootGap_homogeneous p lam z sign hX, ofReal_mul]
    rw [show b * ((X : ℂ) * cepsComplexCumulantRootModel p N lam z sign k ((X : ℂ) * b)) =
      ((X : ℂ) * b) * cepsComplexCumulantRootModel p N lam z sign k ((X : ℂ) * b) by ring]
    by_cases hg : cepsComplexCumulantRootGap p lam z sign = 0
    · simp only [hg, mul_zero, div_zero, sub_zero]
    · field_simp [hg, hXc]

end PGM
