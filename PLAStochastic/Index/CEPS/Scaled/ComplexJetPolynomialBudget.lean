import PLAStochastic.Index.CEPS.Scaled.ComplexJetPolynomial

/-! # Explicit coefficient-only budgets for complex finite jet polynomials -/

noncomputable section
open Complex Finset
namespace PGM

theorem norm_complex_factorial_inv_le_one (n : ℕ) : ‖(n.factorial : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, norm_natCast]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast Nat.factorial_pos n)

theorem cepsCgfComplexJetPolynomial_sub_variance (p : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    cepsCgfComplexJetPolynomial p N s - p (cepsJetCode (.inl 0)) / 2 =
      ∑ j ∈ range N, ((j + 3).factorial : ℂ)⁻¹ * s ^ (j + 1) * p (cepsJetCode (.inl (j + 1))) := by
  unfold cepsCgfComplexJetPolynomial
  rw [sum_range_succ']
  norm_num
  ring

/-- Higher finite cumulant coordinates give a uniform linear perturbation of the
quadratic variance coefficient throughout the unit spatial disc. -/
theorem cepsCgfComplexJetPolynomial_sub_variance_norm_le {p : ℕ → ℂ} (N : ℕ)
    {M : ℝ} (_hM : 0 ≤ M) (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ 1) :
    ‖cepsCgfComplexJetPolynomial p N s - p (cepsJetCode (.inl 0)) / 2‖ ≤
      (N : ℝ) * M * ‖s‖ := by
  rw [cepsCgfComplexJetPolynomial_sub_variance]
  calc
    _ ≤ ∑ j ∈ range N, ‖((j + 3).factorial : ℂ)⁻¹ * s ^ (j + 1) *
        p (cepsJetCode (.inl (j + 1)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range N, M * ‖s‖ := by
      apply sum_le_sum
      intro j hj
      have hjN : j + 1 ≤ N := by have := mem_range.mp hj; omega
      have hpow : ‖s‖ ^ (j + 1) ≤ ‖s‖ := by
        rw [pow_succ]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hs)
      rw [norm_mul, norm_mul, norm_pow]
      calc
        _ ≤ 1 * ‖s‖ * M := by
          exact mul_le_mul
            (mul_le_mul (norm_complex_factorial_inv_le_one _) hpow (by positivity) zero_le_one)
            (hp _ hjN) (norm_nonneg _) (by positivity)
        _ = M * ‖s‖ := by ring
    _ = _ := by simp; ring

theorem cepsCgfComplexJetPolynomial_norm_le {p : ℕ → ℂ} (N : ℕ)
    {M : ℝ} (hM : 0 ≤ M) (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    {s : ℂ} (hs : ‖s‖ ≤ 1) :
    ‖cepsCgfComplexJetPolynomial p N s‖ ≤ ((N : ℝ) + 1) * M := by
  have hd := cepsCgfComplexJetPolynomial_sub_variance_norm_le N hM hp hs
  have h0 : ‖p (cepsJetCode (.inl 0)) / 2‖ ≤ M := by
    rw [norm_div]
    norm_num
    exact (div_le_self (norm_nonneg _) (by norm_num)).trans (hp 0 (Nat.zero_le N))
  have ht := norm_add_le (cepsCgfComplexJetPolynomial p N s - p (cepsJetCode (.inl 0)) / 2)
    (p (cepsJetCode (.inl 0)) / 2)
  rw [sub_add_cancel] at ht
  have hmono : (N : ℝ) * M * ‖s‖ ≤ (N : ℝ) * M := mul_le_of_le_one_right (by positivity) hs
  exact ht.trans ((add_le_add (hd.trans hmono) h0).trans_eq (by ring))

/-- The complete rectangular canonical polynomial is bounded by the finite coordinate
budget alone when its three arguments lie in the closed unit discs. -/
theorem cepsCanonComplexJetPolynomial_norm_le {p : ℕ → ℂ} (N : ℕ)
    {M : ℝ} (_hM : 0 ≤ M)
    (hp : ∀ j ≤ N, ∀ m ≤ N, ∀ n ≤ N, ‖p (cepsJetCode (.inr (j, m, n)))‖ ≤ M)
    {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ 1) (hq : ‖q‖ ≤ 1) (hζ : ‖ζ‖ ≤ 1) :
    ‖cepsCanonComplexJetPolynomial p N μ q ζ‖ ≤ ((N : ℝ) + 1) ^ 3 * M := by
  have hterm (n : ℕ) (s : ℂ) (hs : ‖s‖ ≤ 1) :
      ‖(n.factorial : ℂ)⁻¹ * s ^ n‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (norm_complex_factorial_inv_le_one n) (by positivity)
      (pow_le_one₀ (norm_nonneg _) hs)
  unfold cepsCanonComplexJetPolynomial
  calc
    _ ≤ ∑ j ∈ range (N + 1), ‖(j.factorial : ℂ)⁻¹ * μ ^ j *
        ∑ m ∈ range (N + 1), (m.factorial : ℂ)⁻¹ * ζ ^ m *
          ∑ n ∈ range (N + 1), (n.factorial : ℂ)⁻¹ * q ^ n *
            p (cepsJetCode (.inr (j, m, n)))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ range (N + 1), ((N : ℝ) + 1) ^ 2 * M := by
      apply sum_le_sum
      intro j hj
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans
      have hm : ∑ m ∈ range (N + 1), ‖(m.factorial : ℂ)⁻¹ * ζ ^ m *
          ∑ n ∈ range (N + 1), (n.factorial : ℂ)⁻¹ * q ^ n *
            p (cepsJetCode (.inr (j, m, n)))‖ ≤ ((N : ℝ) + 1) ^ 2 * M := by
        calc
          _ ≤ ∑ _m ∈ range (N + 1), ((N : ℝ) + 1) * M := by
            apply sum_le_sum
            intro m hm
            rw [norm_mul]
            apply (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans
            have hn : ∑ n ∈ range (N + 1), ‖(n.factorial : ℂ)⁻¹ * q ^ n *
                p (cepsJetCode (.inr (j, m, n)))‖ ≤ ((N : ℝ) + 1) * M := by
              calc
                _ ≤ ∑ _n ∈ range (N + 1), M := by
                  apply sum_le_sum
                  intro n hn
                  rw [norm_mul]
                  exact (mul_le_mul (hterm n q hq)
                    (hp j (by have := mem_range.mp hj; omega)
                      m (by have := mem_range.mp hm; omega)
                      n (by have := mem_range.mp hn; omega)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
                _ = _ := by simp
            exact (mul_le_mul (hterm m ζ hζ) hn (by positivity) zero_le_one).trans_eq (one_mul _)
          _ = _ := by simp; ring
      exact (mul_le_mul (hterm j μ hμ) hm (by positivity) zero_le_one).trans_eq (by ring)
    _ = _ := by simp; ring

end PGM
