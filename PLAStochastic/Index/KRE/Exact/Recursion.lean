import PLAStochastic.Index.KRE.Uniform.LayerPhases

/-!
# Exact length of a halving phase

A bounded additive error in a halving recursion selects an exact integer
stopping time when the initial value is separated from the two thresholds.
-/

namespace PGM
noncomputable section

/-- Deterministic exact stopping time for the actual rank hierarchy. -/
theorem kre_exact_halving {eps : ℝ} {p : ℕ → ℝ} {n P J : ℕ}
    {V : ℕ → ℝ} {A ρ : ℝ} (he : 1 ≤ eps) (hn : 1 ≤ n)
    (hA : 0 ≤ A) (hρ : 0 < ρ) (hJ : 1 ≤ J)
    (hP : 2 ≤ reSize eps p n P)
    (hl : ρ + 3 * A ≤ V 0 / (2 : ℝ) ^ (J - 1))
    (hu : V 0 / (2 : ℝ) ^ J ≤ ρ - 3 * A)
    (hstep : ∀ k < J, 2 ≤ reSize eps p n (P + k) → ρ + A ≤ V k →
      2 ≤ reSize eps p n (P + (k + 1)) ∧ |V (k + 1) - V k / 2| ≤ A)
    (hstop : 2 ≤ reSize eps p n (P + J) → V J ≤ ρ - A →
      reSize eps p n (P + J + 1) = 1) :
    reHeight eps p n = P + J + 1 := by
  have hv0 : 0 ≤ V 0 := by
    have hp : (0 : ℝ) < 2 ^ (J - 1) := by positivity
    have : 0 ≤ V 0 / (2 : ℝ) ^ (J - 1) := by linarith
    have hmul := mul_nonneg this hp.le
    simpa only [div_mul_cancel₀ _ hp.ne'] using hmul
  have hall : ∀ k ≤ J, 2 ≤ reSize eps p n (P + k) ∧
      |V k - V 0 / (2 : ℝ) ^ k| ≤ 2 * A := by
    intro k hk
    induction k with
    | zero => simpa using And.intro hP (show (0 : ℝ) ≤ 2 * A by linarith)
    | succ k ih =>
      obtain ⟨hN, hE⟩ := ih (by omega)
      have hbase : ρ + 3 * A ≤ V 0 / (2 : ℝ) ^ k := by
        apply hl.trans
        exact div_le_div_of_nonneg_left hv0 (by positivity)
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : k ≤ J - 1))
      have hlarge : ρ + A ≤ V k := by
        have := (abs_le.mp hE).1
        linarith
      obtain ⟨hN', hE'⟩ := hstep k (by omega) hN hlarge
      refine ⟨hN', ?_⟩
      have heq : V 0 / (2 : ℝ) ^ (k + 1) = (V 0 / (2 : ℝ) ^ k) / 2 := by
        rw [pow_succ, div_mul_eq_div_div]
      rw [heq]
      obtain ⟨hlo, hup⟩ := abs_le.mp hE
      obtain ⟨hlo', hup'⟩ := abs_le.mp hE'
      apply abs_le.mpr
      constructor <;> linarith
  obtain ⟨hNJ, hEJ⟩ := hall J le_rfl
  have hsmall : V J ≤ ρ - A := by
    have := (abs_le.mp hEJ).2
    linarith
  have hterm := hstop hNJ hsmall
  have hupper : reHeight eps p n ≤ P + J + 1 := reHeight_le (by omega) hterm
  have hlower : P + J < reHeight eps p n := by
    by_contra h
    have := reSize_eq_one_of_reHeight_le he hn (le_of_not_gt h)
    omega
  omega

end
end PGM
