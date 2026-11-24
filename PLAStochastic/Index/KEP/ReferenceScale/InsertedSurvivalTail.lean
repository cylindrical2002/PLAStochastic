import PLAStochastic.Index.KEP.ReferenceScale.FiniteWindowTail
import PLAStochastic.Index.KEP.ReferenceScale.CleanWindowSelection
import PLAStochastic.Index.KEP.ReferenceScale.InsertionProductBudget
import PLAStochastic.Index.KEP.ReferenceScale.InsertionNegativeBudget

/-!
# Actual surviving-prefix tail after at most two Mellin insertions

A deterministic clean third gives an unchanged iid stopping window. Integrating
out the inserted coordinates pays exactly their masses. No independence of
survival and bridge deviation events is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kep_pi_event_eq_inserted_mass {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (mu i)] (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (H : Finset (Fin n)) (hmu : ∀ i ∉ H, mu i = nu)
    {E : Set (Fin n → ℝ)} (hE : MeasurableSet E)
    (hind : ∀ x y : Fin n → ℝ, (∀ i ∉ H, x i = y i) → (x ∈ E ↔ y ∈ E)) :
    Measure.pi mu E = (∏ i ∈ H, mu i Set.univ) * Measure.pi (fun _ : Fin n => nu) E := by
  let f := E.indicator (fun _ : Fin n → ℝ => (1 : ℝ≥0∞))
  have hf : Measurable f := measurable_const.indicator hE
  have hdep : ∀ x y : Fin n → ℝ, (∀ i ∉ H, x i = y i) → f x = f y := by
    intro x y hxy
    by_cases hx : x ∈ E
    · have hy := (hind x y hxy).mp hx
      simp only [f, indicator_of_mem hx, indicator_of_mem hy]
    · have hy := mt (hind x y hxy).mpr hx
      simp only [f, indicator_of_notMem hx, indicator_of_notMem hy]
  have hh := lintegral_pi_eq_mul_of_indep mu nu H hmu hf hdep
  simpa only [f, lintegral_indicator hE, lintegral_const, Measure.restrict_apply_univ, one_mul] using hh

theorem kepReference_inserted_survival_tail :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
            Measure.pi mu (kepFiniteStoppedEvent eps n)ᶜ ≤
              ENNReal.ofReal (K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
                Real.exp (-c * n / eps ^ 2)) := by
  obtain ⟨cs, es, hcs, hes, hsurv⟩ := kepReference_finite_window_tail
  obtain ⟨tm, ei, htm, hei, hins⟩ := kepReference_insertion_measure_budgets
  refine ⟨tm, max es ei, htm, hes.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Ki, _, hi⟩ := hins theta ht htheta
  let K0 := max 1 Ki
  have hK0 : 1 ≤ K0 := le_max_left _ _
  have hKi : Ki ≤ K0 := le_max_right _ _
  refine ⟨K0 ^ 2 * (72 / 71) * Real.exp cs, cs / 3, by positivity, by positivity, ?_⟩
  intro eps he heps j hj n r hr
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let H := kepInsertedCoordinates r
  let J := kepReferenceWeightedSecondNorm theta eps j
  obtain ⟨hrcoord, hcard, _⟩ := kepInsertionPattern_bounds hr
  obtain ⟨a, w, haw, hw, hcleanWindow⟩ := kep_clean_window_selection H hcard
  have hmu (i : Fin n) := hi eps ((le_max_right _ _).trans he) heps j hj (r i) (hrcoord i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have hclean (i : Fin n) (hiH : i ∉ H) : mu i = (kepReferenceLaw eps j : Measure ℝ) := by
    have hr0 : r i = 0 := by
      by_contra hz
      exact hiH (mem_filter.mpr ⟨Finset.mem_univ _, hz⟩)
    dsimp [mu]
    rw [hr0, kepReferenceInsertionMeasure_zero]
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hcost (i : Fin n) : 0 ≤ K0 * kepMellinInsertionCost (r i) J := by
    rw [kepMellinInsertionCost_eq_pow hJ (hrcoord i)]
    positivity
  have hmass (i : Fin n) : mu i Set.univ ≤ ENNReal.ofReal (K0 * kepMellinInsertionCost (r i) J) := by
    rw [kep_measure_mass_eq_zero_moment]
    apply ENNReal.ofReal_le_ofReal
    exact (((hmu i).2.2 0 (by positivity)).2).trans
      (mul_le_mul_of_nonneg_right hKi (by
        rw [kepMellinInsertionCost_eq_pow hJ (hrcoord i)]; positivity))
  have hmassprod : (∏ i ∈ H, mu i Set.univ) ≤ ENNReal.ofReal (K0 ^ 2 * (1 + J)) := by
    calc
      _ ≤ ∏ i ∈ H, ENNReal.ofReal (K0 * kepMellinInsertionCost (r i) J) := prod_le_prod' (fun i _ => hmass i)
      _ = ENNReal.ofReal (∏ i ∈ H, K0 * kepMellinInsertionCost (r i) J) :=
        (ENNReal.ofReal_prod_of_nonneg (fun i _ => hcost i)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (kep_insertion_product_cost hr hJ hK0)
  have hdep : ∀ x y : Fin n → ℝ, (∀ i ∉ H, x i = y i) →
      (x ∈ kepFiniteWindowEvent eps n a w ↔ y ∈ kepFiniteWindowEvent eps n a w) := by
    intro x y hxy
    apply kepFiniteWindowEvent_congr
    intro i hia hiw
    apply hxy i
    intro hiH
    exact hcleanWindow i hiH ⟨hia, hiw⟩
  have hwindow := hsurv eps ((le_max_left _ _).trans he) j n a w haw
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hphase : -cs * w / eps ^ 2 ≤ cs - (cs / 3) * n / eps ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hw hcs.le
    have hs : 1 ≤ eps ^ 2 := by nlinarith
    have hextra : cs / eps ^ 2 ≤ cs := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    have hh := (div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ eps ^ 2))
    rw [show cs * ((n : ℝ) / 3 - 1) / eps ^ 2 =
      (cs / 3) * n / eps ^ 2 - cs / eps ^ 2 by ring] at hh
    rw [show -cs * (w : ℝ) / eps ^ 2 = -(cs * w / eps ^ 2) by ring]
    linarith only [hh, hextra]
  calc
    _ ≤ Measure.pi mu (kepFiniteWindowEvent eps n a w) := measure_mono (kepFinite_survival_subset_window eps haw)
    _ = (∏ i ∈ H, mu i Set.univ) *
        Measure.pi (fun _ : Fin n => (kepReferenceLaw eps j : Measure ℝ)) (kepFiniteWindowEvent eps n a w) :=
      kep_pi_event_eq_inserted_mass mu _ H hclean (measurableSet_kepFiniteWindowEvent eps n a w) hdep
    _ ≤ ENNReal.ofReal (K0 ^ 2 * (1 + J)) *
        ENNReal.ofReal (72 / 71 * Real.exp (-cs * w / eps ^ 2)) := mul_le_mul' hmassprod hwindow
    _ ≤ ENNReal.ofReal (K0 ^ 2 * (1 + J)) *
        ENNReal.ofReal (72 / 71 * Real.exp (cs - (cs / 3) * n / eps ^ 2)) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase)
          (by norm_num : (0 : ℝ) ≤ 72 / 71)))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity), show cs - (cs / 3) * (n : ℝ) / eps ^ 2 =
        cs + (-(cs / 3) * n / eps ^ 2) by ring, Real.exp_add]
      congr 1
      ring

end

end PGM
