import PLAStochastic.Index.KEP.ReferenceScale.ProductInsertionIdentification

/-!
# Physical weak-test bounds from actual absolute insertion measures

Absolute product densities, rather than scores, pay every weak-test term.
The event inverse-square budget gives both integrability of the signed term
and its integral bound, including density zeros and diagonal insertions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset Set

theorem kep_mellin_pattern_test_bound {n : ℕ} {f : ℝ → ℝ} (hf : Measurable f)
    (r : Fin n → ℕ) [∀ i, IsFiniteMeasure (kepAbsDensityMeasure ((mellinOp^[r i]) f))]
    {S : (Fin n → ℝ) → ℝ} (hS : Measurable S)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    {psi : (Fin n → ℝ) → ℝ} (hpsi : Measurable psi) {B u : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ x ∈ E, |psi x| ≤ B * Real.exp (u * S x))
    (hi : Integrable (E.indicator (fun x => ((S x) ^ 2)⁻¹ * Real.exp (u * S x)))
      (Measure.pi (fun i => kepAbsDensityMeasure ((mellinOp^[r i]) f)))) :
    Integrable (E.indicator (fun x => psi x / (S x) ^ 2 * kepMellinPatternProduct f r x)) volume ∧
      |∫ x in E, psi x / (S x) ^ 2 * kepMellinPatternProduct f r x| ≤
        B * ∫ x in E, ((S x) ^ 2)⁻¹ * Real.exp (u * S x)
          ∂Measure.pi (fun i => kepAbsDensityMeasure ((mellinOp^[r i]) f)) := by
  let F := fun i : Fin n => (mellinOp^[r i]) f
  let G := E.indicator (fun x => ((S x) ^ 2)⁻¹ * Real.exp (u * S x))
  let T := E.indicator (fun x => psi x / (S x) ^ 2 * kepMellinPatternProduct f r x)
  have hF (i : Fin n) : Measurable (F i) := measurable_mellinOp_iterate hf (r i)
  have hiG : Integrable (fun x => G x * |kepMellinPatternProduct f r x|) volume :=
    (kep_abs_product_integrable_iff F hF G).mp hi
  have hdom := hiG.const_mul B
  have hP : Measurable (kepMellinPatternProduct f r) :=
    Finset.measurable_prod Finset.univ (fun i _ => (hF i).comp (measurable_pi_apply i))
  have hT : Measurable T := (hpsi.div (hS.pow_const 2)).mul hP |>.indicator hE
  have hpt (x : Fin n → ℝ) : ‖T x‖ ≤ B * (G x * |kepMellinPatternProduct f r x|) := by
    by_cases hx : x ∈ E
    · dsimp only [T, G]
      rw [indicator_of_mem hx, indicator_of_mem hx, Real.norm_eq_abs, abs_mul, abs_div,
        abs_of_nonneg (sq_nonneg (S x)), div_eq_mul_inv]
      have hh := mul_le_mul_of_nonneg_right (hbound x hx)
        (mul_nonneg (inv_nonneg.mpr (sq_nonneg (S x))) (abs_nonneg (kepMellinPatternProduct f r x)))
      convert hh using 1 <;> first | rfl | ring
    · simp only [T, G, indicator_of_notMem hx, norm_zero, zero_mul, mul_zero, le_refl]
  have hiT : Integrable T volume := hdom.mono' hT.aestronglyMeasurable (ae_of_all _ hpt)
  refine ⟨hiT, ?_⟩
  have hh := (norm_integral_le_integral_norm T).trans (integral_mono hiT.norm hdom hpt)
  rw [integral_const_mul] at hh
  change ‖∫ x, T x‖ ≤ B * ∫ x, G x * |∏ i, F i (x i)| at hh
  rw [← kep_abs_product_measure_integral F hF G] at hh
  simpa only [T, G, Real.norm_eq_abs, integral_indicator hE] using hh

theorem kep_single_insertion_order {n : ℕ} (i : Fin n) {q : ℕ} (hq : q ≤ 2) :
    (∑ l, Function.update (fun _ : Fin n => 0) i q l) ≤ 2 := by
  classical
  simpa only [sum_update_of_mem (Finset.mem_univ i), sum_const_zero, add_zero] using hq

theorem kep_double_insertion_order {n : ℕ} (i j : Fin n) (hij : j ≠ i) :
    (∑ l, Function.update (Function.update (fun _ : Fin n => 0) i 1) j 1 l) ≤ 2 := by
  classical
  rw [sum_update_of_mem (Finset.mem_univ j), sdiff_singleton_eq_erase, sum_update_of_mem
    (mem_erase.mpr ⟨hij.symm, Finset.mem_univ i⟩), sum_const_zero]
  norm_num

end

end PGM
