import PLAStochastic.Index.CEPS.Scaled.KernelFactorsFrequency

/-! # Exact zero-scale finite-kernel factors for arbitrary positive-variance jet inputs -/

noncomputable section
open Complex Set Metric Filter Topology Finset
namespace PGM

theorem cepsCanonJetPolynomial_origin (p : ℕ → ℝ) (N : ℕ) :
    cepsCanonJetPolynomial p N 0 0 0 = (p (cepsJetCode (.inr (0, 0, 0))) : ℂ) := by
  simp [cepsCanonJetPolynomial, sum_range_succ']

theorem cepsKernelGJetModel_zero (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z ξ : ℂ) :
    cepsKernelGJetModel p N lam z 0 ξ =
      ((p (cepsJetCode (.inl 0)) : ℂ) / 2 *
        exp (-2 * (p (cepsJetCode (.inr (0, 0, 0))) : ℂ))) * exp (-ξ) := by
  simp only [cepsKernelGJetModel, zero_mul, add_zero, mul_one,
    cepsComplexScaledDiscount, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    cepsCumulantJetQuotient_zero, cepsCanonJetPolynomial_origin]
  ring

/-- All fixed-derivative Newton iterates have the same genuine quadratic zero-scale root. -/
theorem cepsCumulantRootModel_zero (p : ℕ → ℝ)
    (hp : p (cepsJetCode (.inl 0)) ≠ 0) (N : ℕ) (lam : ℝ) (z sign : ℂ)
    (hsign : sign ^ 2 = 1) (k : ℕ) :
    cepsCumulantRootModel p N lam z sign k 0 = cepsCumulantRootBase p lam z sign := by
  let V : ℂ := p (cepsJetCode (.inl 0))
  have hV : V ≠ 0 := by dsimp [V]; exact_mod_cast hp
  let s : ℂ := sign * sqrt (2 / V) * sqrt (z + (lam : ℂ) ^ 2 / (2 * V))
  have hs : s ^ 2 = 2 / V * (z + (lam : ℂ) ^ 2 / (2 * V)) := by
    simp only [s, mul_pow, hsign, one_mul, sqrt_sq_eq]
  have he : cepsCumulantRootBase p lam z sign ^ 2 * (V / 2) +
      (lam : ℂ) * cepsCumulantRootBase p lam z sign - z = 0 := by
    change (-(lam : ℂ) / V + s) ^ 2 * (V / 2) + (lam : ℂ) * (-(lam : ℂ) / V + s) - z = 0
    rw [add_sq, hs]
    field_simp
    ring
  have hP : cepsCgfJetPolynomial p N 0 = V / 2 := by
    simp [cepsCgfJetPolynomial, sum_range_succ', V]
    ring
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [cepsCumulantRootModel, quadraticNewtonStep, ih, zero_mul, hP,
      add_zero, mul_one, he, zero_div, sub_zero]

end PGM
