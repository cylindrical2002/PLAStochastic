import PLAStochastic.Index.KEP.ReferenceScale.MellinFieldTesting
import PLAStochastic.Index.KEP.ReferenceScale.StoppedNegativeBudget

/-!
# Actual inverse-square integrability of every full Mellin field

The inverse moment is paid on the full original coordinate product. In
particular the complete physical origin causes no integrability premise in
shifted weak tests. All diagonal and ordered cross insertions are retained.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kep_mellin_fields_integrable_of_patterns {n : ℕ} {f : ℝ → ℝ}
    {T : (Fin n → ℝ) → ℝ}
    (hpatterns : ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
      Integrable (fun x => T x * kepMellinPatternProduct f r x) volume) :
    Integrable (fun x => T x * kepProductDensity f x) volume ∧
      Integrable (fun x => T x * kepProductMellinFirst f x) volume ∧
      Integrable (fun x => T x * kepProductMellinSecond f x) volume := by
  classical
  have h0 := hpatterns (fun _ => 0) (by simp only [sum_const_zero]; norm_num)
  simp only [kepMellinPatternProduct_zero] at h0
  have hsingle (i : Fin n) := hpatterns (Function.update (fun _ => 0) i 1)
    (kep_single_insertion_order i (by norm_num))
  have hdiag (i : Fin n) := hpatterns (Function.update (fun _ => 0) i 2)
    (kep_single_insertion_order i le_rfl)
  have hdouble (i j : Fin n) (hij : j ≠ i) :=
    hpatterns (Function.update (Function.update (fun _ => 0) i 1) j 1) (kep_double_insertion_order i j hij)
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
    exact integrable_finsetSum Finset.univ (fun i _ => hsingle i)
  have hid : Integrable (fun x => ∑ i, T x *
      kepMellinPatternProduct f (Function.update (fun _ => 0) i 2) x) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hdiag i)
  have hic : Integrable (fun x => ∑ i, ∑ j ∈ Finset.univ.erase i, T x *
      kepMellinPatternProduct f (Function.update (Function.update (fun _ => 0) i 1) j 1) x) volume :=
    integrable_finsetSum Finset.univ (fun i _ => integrable_finsetSum _
      (fun j hj => hdouble i j (mem_erase.mp hj).1))
  have hi2 : Integrable (fun x => T x * kepProductMellinSecond f x) volume := by
    simp_rw [he2]
    convert hid.add hic using 1 <;> rfl
  exact ⟨h0, hi1, hi2⟩

theorem kepReference_inverse_second_mellin_fields_integrable :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 18 ≤ n →
          let f := (kepReferenceDensity heps hj).density
          Integrable (fun x : Fin n → ℝ => ((∑ i, x i) ^ 2)⁻¹ * kepProductDensity f x) volume ∧
            Integrable (fun x : Fin n → ℝ => ((∑ i, x i) ^ 2)⁻¹ * kepProductMellinFirst f x) volume ∧
            Integrable (fun x : Fin n → ℝ => ((∑ i, x i) ^ 2)⁻¹ * kepProductMellinSecond f x) volume := by
  obtain ⟨tn, en, htn, hen, hnegative⟩ := kepReference_insertion_fourth_negative_budget
  obtain ⟨ti, ei, hti, hei, hmeasures⟩ := kepReference_insertion_measure_budgets
  let theta := min tn ti / 2
  have ht : 0 < theta := div_pos (lt_min htn hti) (by norm_num)
  obtain ⟨Kn, hKn, hnb⟩ := hnegative theta ht (by dsimp [theta]; linarith [min_le_left tn ti])
  obtain ⟨_Ki, _, hmb⟩ := hmeasures theta ht (by dsimp [theta]; linarith [min_le_right tn ti])
  refine ⟨max en ei, hen.trans (le_max_left _ _), ?_⟩
  intro eps he heps j hj n hn18
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let S := fun x : Fin n → ℝ => ∑ i, x i
  have hS : Measurable S := Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  apply kep_mellin_fields_integrable_of_patterns
  intro r hr
  have hmu (i : Fin n) := hmb eps ((le_max_right _ _).trans he) heps j hj (r i)
    ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (kepAbsDensityMeasure ((mellinOp^[r i]) f)) := fun i => (hmu i).1
  let mu := Measure.pi (fun i : Fin n => kepAbsDensityMeasure ((mellinOp^[r i]) f))
  have hneg := hnb eps ((le_max_left _ _).trans he) heps j hj n hn18 r hr
  have hJ := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hexp : Integrable (fun x : Fin n → ℝ => Real.exp ((2 * 0) * S x)) mu := by
    simpa only [mul_zero, zero_mul, Real.exp_zero] using (integrable_const (1 : ℝ) : Integrable (fun _ => (1 : ℝ)) mu)
  have hh := kep_inverse_square_event_cauchy hS MeasurableSet.univ
    (by positivity : 0 ≤ Kn * (1 + kepReferenceWeightedSecondNorm theta eps j) / (n : ℝ) ^ 4)
    (integral_nonneg (fun _ => (Real.exp_pos _).le)) hneg hexp
    (by simp only [setIntegral_univ]; exact le_rfl)
  have hi : Integrable (fun x => ((S x) ^ 2)⁻¹) mu := by
    have hh' := hh.1
    simp only [indicator_univ, zero_mul, Real.exp_zero, mul_one] at hh'
    convert hh' using 1
    rfl
  have htest := kep_mellin_pattern_test_bound (psi := fun _ => (1 : ℝ))
    (u := 0) (B := 1) (kepReferenceDensity heps hj).measurable r hS MeasurableSet.univ
    measurable_const (by norm_num) (by intro x _; simp) (by simpa only [zero_mul, Real.exp_zero, mul_one, indicator_univ] using hi)
  have ht := htest.1
  simp only [indicator_univ, one_div] at ht
  exact ht

theorem kep_inverse_first_integrable_of_second {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {S P : alpha → ℝ} (hS : Measurable S)
    (hP : Integrable P mu) (hP2 : Integrable (fun x => ((S x) ^ 2)⁻¹ * P x) mu) :
    Integrable (fun x => (S x)⁻¹ * P x) mu := by
  have hdom := hP.abs.add hP2.abs
  apply hdom.mono' (hS.inv.aestronglyMeasurable.mul hP.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  have hi : |(S x)⁻¹| ≤ 1 + ((S x) ^ 2)⁻¹ := by
    have he : |(S x)⁻¹| ^ 2 = ((S x) ^ 2)⁻¹ := by rw [sq_abs]; exact inv_pow _ 2
    nlinarith only [sq_nonneg (|(S x)⁻¹| - 1), he, abs_nonneg ((S x)⁻¹)]
  change ‖(S x)⁻¹ * P x‖ ≤ |P x| + |((S x) ^ 2)⁻¹ * P x|
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |(S x)⁻¹| * |P x| ≤ (1 + ((S x) ^ 2)⁻¹) * |P x| := mul_le_mul_of_nonneg_right hi (abs_nonneg _)
    _ = |P x| + |((S x) ^ 2)⁻¹ * P x| := by
      rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg (S x)))]
      ring

end

end PGM
