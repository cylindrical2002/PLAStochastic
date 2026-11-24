import PLAStochastic.Index.KEP.ReferenceScale.ActualConeTransfer

/-!
# Exact absolute product density of every actual Mellin insertion pattern

No score division is used. Product factors retain the original coordinate
set, including zeros of the reference density and diagonal second insertions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

def kepMellinPatternProduct {n : ℕ} (f : ℝ → ℝ) (r : Fin n → ℕ) (x : Fin n → ℝ) : ℝ :=
  ∏ i, (mellinOp^[r i]) f (x i)

theorem kep_abs_product_measure_eq_withDensity {n : ℕ} (F : Fin n → ℝ → ℝ)
    (hF : ∀ i, Measurable (F i)) [∀ i, IsFiniteMeasure (kepAbsDensityMeasure (F i))] :
    Measure.pi (fun i => kepAbsDensityMeasure (F i)) =
      volume.withDensity (fun x : Fin n → ℝ => ENNReal.ofReal (|∏ i, F i (x i)|)) := by
  simp only [kepAbsDensityMeasure]
  rw [pi_withDensity_fin volume (fun i x => ENNReal.ofReal (|F i x|))
    (fun i => (hF i).abs.ennreal_ofReal)]
  have he (x : Fin n → ℝ) : (∏ i, ENNReal.ofReal (|F i (x i)|)) =
      ENNReal.ofReal (|∏ i, F i (x i)|) := by
    rw [abs_prod]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg _)).symm
  simp_rw [he]
  rfl

theorem kep_abs_product_integrable_iff {n : ℕ} (F : Fin n → ℝ → ℝ)
    (hF : ∀ i, Measurable (F i)) [∀ i, IsFiniteMeasure (kepAbsDensityMeasure (F i))]
    (G : (Fin n → ℝ) → ℝ) :
    Integrable G (Measure.pi (fun i => kepAbsDensityMeasure (F i))) ↔
      Integrable (fun x => G x * |∏ i, F i (x i)|) volume := by
  rw [kep_abs_product_measure_eq_withDensity F hF]
  have hm : Measurable (fun x : Fin n → ℝ => |∏ i, F i (x i)|) :=
    (Finset.measurable_prod Finset.univ (fun i _ => (hF i).comp (measurable_pi_apply i))).abs
  rw [integrable_withDensity_iff_integrable_smul' hm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul, mul_comm]

theorem kep_abs_product_measure_integral {n : ℕ} (F : Fin n → ℝ → ℝ)
    (hF : ∀ i, Measurable (F i)) [∀ i, IsFiniteMeasure (kepAbsDensityMeasure (F i))]
    (G : (Fin n → ℝ) → ℝ) :
    (∫ x, G x ∂Measure.pi (fun i => kepAbsDensityMeasure (F i))) =
      ∫ x, G x * |∏ i, F i (x i)| := by
  simp only [kepAbsDensityMeasure]
  rw [pi_withDensity_fin volume
    (fun i x => ENNReal.ofReal (|F i x|)) (fun i => (hF i).abs.ennreal_ofReal)]
  have he (x : Fin n → ℝ) : (∏ i, ENNReal.ofReal (|F i (x i)|)) =
      ENNReal.ofReal (|∏ i, F i (x i)|) := by
    rw [abs_prod]
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => abs_nonneg _)).symm
  simp_rw [he]
  have hm : Measurable (fun x : Fin n → ℝ => |∏ i, F i (x i)|) :=
    (Finset.measurable_prod Finset.univ (fun i _ => (hF i).comp (measurable_pi_apply i))).abs
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
  convert integral_congr_ae (μ := (volume : Measure (Fin n → ℝ)))
    (ae_of_all _ fun x => mul_comm |∏ i, F i (x i)| (G x)) using 1
  rfl

theorem kepReference_inserted_integral_eq_absolute_product :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∀ i, r i ≤ 2) →
          ∀ G : (Fin n → ℝ) → ℝ,
          (∫ x, G x ∂Measure.pi (fun i => kepReferenceInsertionMeasure heps hj (r i))) =
            ∫ x, G x * |kepMellinPatternProduct (kepReferenceDensity heps hj).density r x| := by
  obtain ⟨tm, ei, htm, hei, hi⟩ := kepReference_insertion_measure_budgets
  obtain ⟨_K, _, hib⟩ := hi (tm / 2) (by positivity) (by linarith)
  refine ⟨ei, hei, ?_⟩
  intro eps he heps j hj n r hr G
  let f := (kepReferenceDensity heps hj).density
  have hm (i : Fin n) : Measurable ((mellinOp^[r i]) f) :=
    measurable_mellinOp_iterate (kepReferenceDensity heps hj).measurable (r i)
  have : ∀ i : Fin n, IsFiniteMeasure (kepAbsDensityMeasure ((mellinOp^[r i]) f)) :=
    fun i => (hib eps he heps j hj (r i) (hr i)).1
  exact kep_abs_product_measure_integral (fun i => (mellinOp^[r i]) f) hm G

theorem kepMellinPatternProduct_zero {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) :
    kepMellinPatternProduct f (fun _ => 0) x = kepProductDensity f x := by
  simp only [kepMellinPatternProduct, Function.iterate_zero_apply, kepProductDensity]

theorem kepMellinPatternProduct_single {n : ℕ} (f : ℝ → ℝ) (i : Fin n) (r : ℕ)
    (x : Fin n → ℝ) :
    kepMellinPatternProduct f (Function.update (fun _ => 0) i r) x =
      (mellinOp^[r]) f (x i) * ∏ l ∈ Finset.univ.erase i, f (x l) := by
  classical
  have he : (fun l : Fin n => (mellinOp^[Function.update (fun _ => 0) i r l]) f (x l)) =
      Function.update (fun l => f (x l)) i ((mellinOp^[r]) f (x i)) := by
    funext l
    by_cases hl : l = i
    · subst l
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hl, Function.iterate_zero_apply]
  rw [kepMellinPatternProduct, he, prod_update_of_mem (Finset.mem_univ i), sdiff_singleton_eq_erase]

theorem kepMellinPatternProduct_double {n : ℕ} (f : ℝ → ℝ) (i j : Fin n) (hij : j ≠ i)
    (x : Fin n → ℝ) :
    kepMellinPatternProduct f (Function.update (Function.update (fun _ => 0) i 1) j 1) x =
      mellinOp f (x i) * (mellinOp f (x j) *
        ∏ l ∈ (Finset.univ.erase i).erase j, f (x l)) := by
  classical
  have he : (fun l : Fin n =>
      (mellinOp^[Function.update (Function.update (fun _ => 0) i 1) j 1 l]) f (x l)) =
      Function.update (Function.update (fun l => f (x l)) i (mellinOp f (x i))) j (mellinOp f (x j)) := by
    funext l
    by_cases hlj : l = j
    · subst l
      simp only [Function.update_self, Function.iterate_one]
    · by_cases hli : l = i
      · subst l
        simp only [Function.update_of_ne hlj, Function.update_self, Function.iterate_one]
      · simp only [Function.update_of_ne hlj, Function.update_of_ne hli, Function.iterate_zero_apply]
  rw [kepMellinPatternProduct, he, prod_update_of_mem (Finset.mem_univ j), sdiff_singleton_eq_erase,
    prod_update_of_mem (mem_erase.mpr ⟨hij.symm, Finset.mem_univ i⟩), sdiff_singleton_eq_erase, erase_right_comm]
  ring

end

end PGM
