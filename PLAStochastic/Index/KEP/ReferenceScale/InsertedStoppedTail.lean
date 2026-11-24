import PLAStochastic.Index.KEP.ReferenceScale.InsertedPartialDeviation
import PLAStochastic.Index.KEP.ReferenceScale.FiniteGapGeometry

/-!
# Actual inserted weighted tail of the original short stopped prefix

The original stopping event is covered by its complete finite family of true
partial-sum deviations. Every coordinate remains in the original inserted
product measure. The union bound pays only the number of original prefixes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kep_integral_event_le_finset_sum {alpha I : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : alpha → ℝ} (hi : Integrable f mu) (hf : ∀ x, 0 ≤ f x)
    {E : Set alpha} (hE : MeasurableSet E) (T : Finset I) (F : I → Set alpha)
    (hm : ∀ i ∈ T, MeasurableSet (F i)) (hsub : E ⊆ ⋃ i ∈ T, F i) :
    (∫ x in E, f x ∂mu) ≤ ∑ i ∈ T, ∫ x in F i, f x ∂mu := by
  have hpt (x : alpha) : E.indicator f x ≤ ∑ i ∈ T, (F i).indicator f x := by
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      obtain ⟨i, hiF'⟩ := mem_iUnion.mp (hsub hx)
      obtain ⟨hiT, hiF⟩ := mem_iUnion.mp hiF'
      have hh := single_le_sum (s := T) (f := fun i => (F i).indicator f x)
        (fun i _ => indicator_nonneg (fun x _ => hf x) x) hiT
      simpa only [indicator_of_mem hiF] using hh
    · rw [indicator_of_notMem hx]
      exact sum_nonneg fun i _ => indicator_nonneg (fun x _ => hf x) x
  have hsum := integrable_finsetSum T (fun i hiT => hi.indicator (hm i hiT))
  have hh := integral_mono (hi.indicator hE) hsum hpt
  rw [integral_finsetSum T (fun i hiT => hi.indicator (hm i hiT)), integral_indicator hE] at hh
  exact hh.trans_eq (sum_congr rfl (fun i hiT => integral_indicator (hm i hiT)))

theorem kep_integral_event_le_two {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {f : alpha → ℝ} (hi : Integrable f mu) (hf : ∀ x, 0 ≤ f x)
    {E U L : Set alpha} (hE : MeasurableSet E) (hU : MeasurableSet U) (hL : MeasurableSet L)
    (hsub : E ⊆ U ∪ L) :
    (∫ x in E, f x ∂mu) ≤ (∫ x in U, f x ∂mu) + ∫ x in L, f x ∂mu := by
  let F : Bool → Set alpha := fun b => if b then U else L
  have hm (b : Bool) (_hb : b ∈ (univ : Finset Bool)) : MeasurableSet (F b) := by
    cases b <;> first | exact hL | exact hU
  have hsub' : E ⊆ ⋃ b ∈ (univ : Finset Bool), F b := by
    intro x hx
    rcases hsub hx with hxU | hxL
    · exact mem_iUnion.mpr ⟨true, mem_iUnion.mpr ⟨mem_univ _, hxU⟩⟩
    · exact mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨mem_univ _, hxL⟩⟩
  have hh := kep_integral_event_le_finset_sum hi hf hE univ F hm hsub'
  simpa only [Fintype.sum_bool, F, Bool.false_eq_true, if_false, if_true] using hh

theorem kepReference_inserted_stopped_tail :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 4 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, (n : ℝ) ≤ 17 * eps →
            ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 → ∀ u : ℝ, 0 ≤ u → u ≤ u0 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              (∫ x in kepFiniteStoppedEvent eps n, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (n + 1) * (1 + kepReferenceWeightedSecondNorm theta eps j) * Real.exp (-c * eps) := by
  obtain ⟨td, ed, htd, hed, hd⟩ := kepReference_inserted_partial_deviations
  obtain ⟨ti, ei, hti, hei, hi⟩ := kepReference_insertion_measure_budgets
  refine ⟨min td ti, max ed ei, lt_min htd hti, hed.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨K, c, u0, hK, hc, hu0, hucap, hdb⟩ := hd theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨_Ki, _, hib⟩ := hi theta ht (htheta.trans (min_le_right _ _))
  refine ⟨2 * K, c, u0, by positivity, hc, hu0, hucap, ?_⟩
  intro eps he heps j hj n hn r hr u hu huMax
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let J := kepReferenceWeightedSecondNorm theta eps j
  let f := fun x : Fin n → ℝ => Real.exp (u * ∑ i, x i)
  let F := fun m : ℕ => {x : Fin n → ℝ | eps ≤ |(∑ i ∈ kepFinitePrefix n m, x i) - m|}
  have hmu (i : Fin n) := hib eps ((le_max_right _ _).trans he) heps j hj (r i)
    ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have hfi : Integrable f (Measure.pi mu) := kep_pi_exp_sum_integrable mu
    (fun i => ((hmu i).2.2 u (huMax.trans hucap)).1)
  have hfm (m : ℕ) (_hm : m ∈ range (n + 1)) : MeasurableSet (F m) := by
    have hP : Measurable (fun x : Fin n → ℝ => ∑ i ∈ kepFinitePrefix n m, x i) :=
      Finset.measurable_sum (kepFinitePrefix n m) (fun i _ => measurable_pi_apply i)
    exact measurableSet_le measurable_const (hP.sub measurable_const).abs
  have hFbound (m : ℕ) (hm : m ∈ range (n + 1)) :
      (∫ x in F m, f x ∂Measure.pi mu) ≤ 2 * K * (1 + J) * Real.exp (-c * eps) := by
    have hmN : m ≤ n := by have hh := mem_range.mp hm; omega
    let P := fun x : Fin n → ℝ => (∑ i ∈ kepFinitePrefix n m, x i) - m
    let U := {x : Fin n → ℝ | eps ≤ P x}
    let L := {x : Fin n → ℝ | eps ≤ -P x}
    have hP : Measurable P := (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)).sub measurable_const
    have hU : MeasurableSet U := measurableSet_le measurable_const hP
    have hL : MeasurableSet L := measurableSet_le measurable_const hP.neg
    have hsub : F m ⊆ U ∪ L := by
      intro x hx
      change eps ≤ |P x| at hx
      by_cases hx0 : 0 ≤ P x
      · left
        change eps ≤ P x
        simpa only [abs_of_nonneg hx0] using hx
      · right
        change eps ≤ -P x
        simpa only [abs_of_neg (not_le.mp hx0)] using hx
    have hh := kep_integral_event_le_two hfi (fun _ => (Real.exp_pos _).le) (hfm m hm) hU hL hsub
    have hp := hdb eps ((le_max_left _ _).trans he) heps j hj n hn r hr (kepFinitePrefix n m)
      1 u (by norm_num) hu huMax
    have hl := hdb eps ((le_max_left _ _).trans he) heps j hj n hn r hr (kepFinitePrefix n m)
      (-1) u (by norm_num) hu huMax
    have hp' : (∫ x in U, f x ∂Measure.pi mu) ≤ K * (1 + J) * Real.exp (-c * eps) := by
      simpa only [kepFinitePrefix_card hmN, one_mul] using hp
    have hl' : (∫ x in L, f x ∂Measure.pi mu) ≤ K * (1 + J) * Real.exp (-c * eps) := by
      simpa only [kepFinitePrefix_card hmN, neg_one_mul] using hl
    exact hh.trans ((add_le_add hp' hl').trans_eq (by ring))
  have hh := kep_integral_event_le_finset_sum hfi (fun _ => (Real.exp_pos _).le)
    (measurableSet_kepFiniteStoppedEvent eps n) (range (n + 1)) F hfm
    (kepFiniteStoppedEvent_subset_deviations eps n)
  apply hh.trans
  calc
    _ ≤ ∑ _m ∈ range (n + 1), 2 * K * (1 + J) * Real.exp (-c * eps) :=
      sum_le_sum hFbound
    _ = _ := by
      rw [sum_const, card_range, nsmul_eq_mul]
      push_cast
      ring

end

end PGM
