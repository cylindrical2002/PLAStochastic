import PLAStochastic.Index.KEP.ReferenceScale.MellinFieldTesting

/-!
# The exact polynomial cost of all three rare radial fields

The complete physical combination has `n² + 5n + 6` insertion cost. Constants
come from the exact coefficients `1, -3, 2` and the two product-rule fields.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset

theorem kep_abs_second_mellin_combination (a b c : ℝ) :
    |a - 3 * b + 2 * c| ≤ |a| + 3 * |b| + 2 * |c| := by
  apply (abs_add_le _ _).trans
  have h : |a - 3 * b| ≤ |a| + 3 * |b| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using abs_add_le a (-(3 * b))
  simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using add_le_add h (le_refl |2 * c|)

theorem kep_abs_first_mellin_combination (a b : ℝ) :
    |2 * a - 3 * b| ≤ 2 * |a| + 3 * |b| := by
  simpa only [sub_eq_add_neg, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using abs_add_le (2 * a) (-(3 * b))

theorem kep_weighted_mellin_fields_test_budget {n : ℕ} {f : ℝ → ℝ}
    {T0 T1 T2 : (Fin n → ℝ) → ℝ} {Q : ℝ} (hQ : 0 ≤ Q)
    (hbudget : ∀ T, (T = T0 ∨ T = T1 ∨ T = T2) →
      ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
        Integrable (fun x => T x * kepMellinPatternProduct f r x) volume ∧
          |∫ x, T x * kepMellinPatternProduct f r x| ≤ Q) :
    let F := fun x => T0 x *
      (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
      T1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + T2 x * kepProductDensity f x
    Integrable F volume ∧ |∫ x, F x| ≤ ((n : ℝ) ^ 2 + 5 * n + 6) * Q := by
  classical
  dsimp only
  have h0 := kep_mellin_fields_test_budget hQ (hbudget T0 (Or.inl rfl))
  have h1 := kep_mellin_fields_test_budget hQ (hbudget T1 (Or.inr (Or.inl rfl)))
  have h2 := kep_mellin_fields_test_budget hQ (hbudget T2 (Or.inr (Or.inr rfl)))
  let F0 := fun x : Fin n → ℝ => T0 x * kepProductMellinSecond f x -
    3 * (T0 x * kepProductMellinFirst f x) + 2 * (T0 x * kepProductDensity f x)
  let F1 := fun x : Fin n → ℝ => 2 * (T1 x * kepProductMellinFirst f x) -
    3 * (T1 x * kepProductDensity f x)
  let F2 := fun x : Fin n → ℝ => T2 x * kepProductDensity f x
  have hi0 : Integrable F0 volume :=
    (h0.2.2.1.sub (h0.2.1.const_mul 3)).add (h0.1.const_mul 2)
  have hi1 : Integrable F1 volume := (h1.2.1.const_mul 2).sub (h1.1.const_mul 3)
  have hi2 : Integrable F2 volume := h2.1
  have he (x : Fin n → ℝ) : T0 x *
      (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
      T1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + T2 x * kepProductDensity f x =
      F0 x + F1 x + F2 x := by dsimp [F0, F1, F2]; ring
  have hb0 : |∫ x, F0 x| ≤ ((n : ℝ) ^ 2 + 3 * n + 2) * Q := by
    have he0 : (∫ x, F0 x) = (∫ x, T0 x * kepProductMellinSecond f x) -
        3 * (∫ x, T0 x * kepProductMellinFirst f x) + 2 * (∫ x, T0 x * kepProductDensity f x) := by
      calc
        _ = (∫ x, T0 x * kepProductMellinSecond f x - 3 * (T0 x * kepProductMellinFirst f x)) +
            (∫ x, 2 * (T0 x * kepProductDensity f x)) := by
          convert integral_add (h0.2.2.1.sub (h0.2.1.const_mul 3)) (h0.1.const_mul 2) using 1 <;> rfl
        _ = _ := by
          have hs := integral_sub h0.2.2.1 (h0.2.1.const_mul 3)
          change (∫ x, T0 x * kepProductMellinSecond f x - 3 * (T0 x * kepProductMellinFirst f x)) = _ at hs
          rw [hs, integral_const_mul, integral_const_mul]
    rw [he0]
    apply (kep_abs_second_mellin_combination _ _ _).trans
    have hbP2 := h0.2.2.2.2.2
    have hbP1 := h0.2.2.2.2.1
    have hbP0 := h0.2.2.2.1
    nlinarith only [hbP2, hbP1, hbP0]
  have hb1 : |∫ x, F1 x| ≤ (2 * (n : ℝ) + 3) * Q := by
    have he1 : (∫ x, F1 x) = 2 * (∫ x, T1 x * kepProductMellinFirst f x) -
        3 * (∫ x, T1 x * kepProductDensity f x) := by
      have hs := integral_sub (h1.2.1.const_mul 2) (h1.1.const_mul 3)
      change (∫ x, F1 x) = _ at hs
      rw [hs, integral_const_mul, integral_const_mul]
    rw [he1]
    apply (kep_abs_first_mellin_combination _ _).trans
    have hbP1 := h1.2.2.2.2.1
    have hbP0 := h1.2.2.2.1
    nlinarith only [hbP1, hbP0]
  have hb2 : |∫ x, F2 x| ≤ Q := h2.2.2.2.1
  refine ⟨?_, ?_⟩
  · simp_rw [he]
    convert (hi0.add hi1).add hi2 using 1 <;> rfl
  · simp_rw [he]
    have ha := integral_add (hi0.add hi1) hi2
    change (∫ x, F0 x + F1 x + F2 x) = _ at ha
    have hb := integral_add hi0 hi1
    change (∫ x, F0 x + F1 x) = _ at hb
    rw [ha]
    change |(∫ x, F0 x + F1 x) + ∫ x, F2 x| ≤ _
    rw [hb]
    apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
    have hh := add_le_add (add_le_add hb0 hb1) hb2
    exact hh.trans_eq (by ring)

end

end PGM
