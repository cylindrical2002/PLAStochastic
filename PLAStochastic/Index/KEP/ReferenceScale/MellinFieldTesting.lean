import PLAStochastic.Index.KEP.ReferenceScale.PatternTestBound

/-!
# All physical weak Mellin fields paid by the genuine insertion patterns

Finite single, diagonal and ordered double insertions give exact expansions
of the complete radial fields. A common signed-test budget pays their full
cardinality without scores or omitted coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset

theorem kepProductMellinFirst_eq_patterns {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) :
    kepProductMellinFirst f x =
      ∑ i, kepMellinPatternProduct f (Function.update (fun _ => 0) i 1) x := by
  unfold kepProductMellinFirst kepFiniteProductFirst
  apply sum_congr rfl
  intro i _
  rw [kepMellinPatternProduct_single]
  simp only [Function.iterate_one]

theorem kepProductMellinSecond_eq_patterns {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) :
    kepProductMellinSecond f x =
      (∑ i, kepMellinPatternProduct f (Function.update (fun _ => 0) i 2) x) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        kepMellinPatternProduct f (Function.update (Function.update (fun _ => 0) i 1) j 1) x := by
  unfold kepProductMellinSecond kepFiniteProductSecond
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [kepMellinPatternProduct_single, mul_sum]
  simp only [Function.iterate_succ_apply']
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [kepMellinPatternProduct_double f i j (mem_erase.mp hj).1]

theorem kep_mellin_fields_test_budget {n : ℕ} {f : ℝ → ℝ} {T : (Fin n → ℝ) → ℝ}
    {Q : ℝ} (_hQ : 0 ≤ Q)
    (hbudget : ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
      Integrable (fun x => T x * kepMellinPatternProduct f r x) volume ∧
        |∫ x, T x * kepMellinPatternProduct f r x| ≤ Q) :
    Integrable (fun x => T x * kepProductDensity f x) volume ∧
      Integrable (fun x => T x * kepProductMellinFirst f x) volume ∧
      Integrable (fun x => T x * kepProductMellinSecond f x) volume ∧
      |∫ x, T x * kepProductDensity f x| ≤ Q ∧
      |∫ x, T x * kepProductMellinFirst f x| ≤ (n : ℝ) * Q ∧
      |∫ x, T x * kepProductMellinSecond f x| ≤ (n : ℝ) ^ 2 * Q := by
  classical
  have h0 := hbudget (fun _ => 0) (by simp only [sum_const_zero]; norm_num)
  simp only [kepMellinPatternProduct_zero] at h0
  have hsingle (i : Fin n) := hbudget (Function.update (fun _ => 0) i 1)
    (kep_single_insertion_order i (by norm_num))
  have hdiag (i : Fin n) := hbudget (Function.update (fun _ => 0) i 2)
    (kep_single_insertion_order i le_rfl)
  have hdouble (i j : Fin n) (hij : j ≠ i) :=
    hbudget (Function.update (Function.update (fun _ => 0) i 1) j 1) (kep_double_insertion_order i j hij)
  have he1 (x : Fin n → ℝ) : T x * kepProductMellinFirst f x =
      ∑ i, T x * kepMellinPatternProduct f (Function.update (fun _ => 0) i 1) x := by
    rw [kepProductMellinFirst_eq_patterns, mul_sum]
  have he2 (x : Fin n → ℝ) : T x * kepProductMellinSecond f x =
      (∑ i, T x * kepMellinPatternProduct f (Function.update (fun _ => 0) i 2) x) +
      ∑ i, ∑ j ∈ Finset.univ.erase i,
        T x * kepMellinPatternProduct f (Function.update (Function.update (fun _ => 0) i 1) j 1) x := by
    rw [kepProductMellinSecond_eq_patterns, mul_add, mul_sum]
    simp_rw [mul_sum]
  have hi1 : Integrable (fun x => T x * kepProductMellinFirst f x) volume := by
    simp_rw [he1]
    exact integrable_finsetSum Finset.univ (fun i _ => (hsingle i).1)
  have hid : Integrable (fun x => ∑ i, T x *
      kepMellinPatternProduct f (Function.update (fun _ => 0) i 2) x) volume :=
    integrable_finsetSum Finset.univ (fun i _ => (hdiag i).1)
  have hic : Integrable (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i, T x *
      kepMellinPatternProduct f (Function.update (Function.update (fun _ => 0) i 1) j 1) x) volume :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum _
      (fun j hj => (hdouble i j (mem_erase.mp hj).1).1))
  have hi2 : Integrable (fun x => T x * kepProductMellinSecond f x) volume := by
    simp_rw [he2]
    convert hid.add hic using 1 <;> rfl
  refine ⟨h0.1, hi1, hi2, h0.2, ?_, ?_⟩
  · simp_rw [he1]
    rw [integral_finsetSum Finset.univ (fun i _ => (hsingle i).1)]
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _i : Fin n, Q := sum_le_sum fun i _ => (hsingle i).2
      _ = _ := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  · simp_rw [he2]
    rw [integral_add hid hic, integral_finsetSum Finset.univ (fun i _ => (hdiag i).1),
      integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum _
        (fun j hj => (hdouble i j (mem_erase.mp hj).1).1))]
    simp_rw [integral_finsetSum _ (fun j hj => (hdouble _ j (mem_erase.mp hj).1).1)]
    apply (abs_add_le _ _).trans
    apply (add_le_add (abs_sum_le_sum_abs _ _) (abs_sum_le_sum_abs _ _)).trans
    apply (add_le_add (sum_le_sum fun i _ => (hdiag i).2)
      (sum_le_sum fun i _ => (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun j hj => (hdouble i j (mem_erase.mp hj).1).2))).trans
    have hcard (i : Fin n) : (Finset.univ.erase i).card = n - 1 := by
      rw [card_erase_of_mem (Finset.mem_univ i), card_univ, Fintype.card_fin]
    simp only [sum_const, card_univ, Fintype.card_fin, hcard, nsmul_eq_mul]
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      rw [Nat.cast_sub hn1]
      norm_num only [Nat.cast_one]
      apply le_of_eq
      ring

end

end PGM
