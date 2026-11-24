import PLAStochastic.Index.KEP.ReferenceScale.MellinInsertionMeasures
import PLAStochastic.Index.KEP.ReferenceScale.CleanMomentBudget
import PLAStochastic.Index.KEP.ReferenceScale.InsertedChernoff

/-!
# A linear second-norm cost for every admissible insertion pattern

The total insertion order is at most two. Its square-root powers multiply to
at most one second norm. Every other coordinate retains the actual clean
quadratic moment bound, with the correct number of clean coordinates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

theorem kepMellinInsertionCost_eq_pow {J : ℝ} (hJ : 0 ≤ J) {r : ℕ} (hr : r ≤ 2) :
    kepMellinInsertionCost r J = Real.sqrt (1 + J) ^ r := by
  interval_cases r
  · simp [kepMellinInsertionCost]
  · simp [kepMellinInsertionCost]
  · simp only [kepMellinInsertionCost]
    norm_num only
    exact (Real.sq_sqrt (by linarith : 0 ≤ 1 + J)).symm

def kepInsertedCoordinates {n : ℕ} (r : Fin n → ℕ) : Finset (Fin n) :=
  univ.filter (fun i => r i ≠ 0)

theorem kepInsertionPattern_bounds {n : ℕ} {r : Fin n → ℕ} (hr : (∑ i, r i) ≤ 2) :
    (∀ i, r i ≤ 2) ∧ (kepInsertedCoordinates r).card ≤ 2 ∧
      (∑ i ∈ kepInsertedCoordinates r, r i) ≤ 2 := by
  classical
  have hsum : (∑ i ∈ kepInsertedCoordinates r, r i) = ∑ i, r i := by
    apply sum_subset (filter_subset _ _)
    intro i _ hi
    by_contra hz
    exact hi (mem_filter.mpr ⟨mem_univ _, hz⟩)
  have hcard : (kepInsertedCoordinates r).card ≤ ∑ i ∈ kepInsertedCoordinates r, r i := by
    have hh := sum_le_sum (fun i (hi : i ∈ kepInsertedCoordinates r) =>
      Nat.one_le_iff_ne_zero.mpr (mem_filter.mp hi).2)
    simpa using hh
  refine ⟨fun i => (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans hr,
    hcard.trans ?_, ?_⟩ <;> rwa [hsum]

theorem kep_insertion_product_cost {n : ℕ} {r : Fin n → ℕ} (hr : (∑ i, r i) ≤ 2)
    {J K : ℝ} (hJ : 0 ≤ J) (hK : 1 ≤ K) :
    (∏ i ∈ kepInsertedCoordinates r, K * kepMellinInsertionCost (r i) J) ≤ K ^ 2 * (1 + J) := by
  classical
  obtain ⟨hrcoord, hcard, hsum⟩ := kepInsertionPattern_bounds hr
  have hprod : (∏ i ∈ kepInsertedCoordinates r, kepMellinInsertionCost (r i) J) =
      Real.sqrt (1 + J) ^ (∑ i ∈ kepInsertedCoordinates r, r i) := by
    simp_rw [kepMellinInsertionCost_eq_pow hJ (hrcoord _)]
    exact prod_pow_eq_pow_sum _ _ _
  have hsqrt : 1 ≤ Real.sqrt (1 + J) := Real.one_le_sqrt.mpr (by linarith)
  have hprodBound : (∏ i ∈ kepInsertedCoordinates r, kepMellinInsertionCost (r i) J) ≤ 1 + J := by
    rw [hprod]
    exact (pow_le_pow_right₀ hsqrt hsum).trans_eq (Real.sq_sqrt (by linarith : 0 ≤ 1 + J))
  rw [prod_mul_distrib, prod_const]
  exact mul_le_mul (pow_le_pow_right₀ hK hcard) hprodBound
    (by rw [hprod]; positivity) (by positivity)

theorem kepReference_inserted_exponential_budget :
    ∃ C t0 thetaMax eps0 : ℝ, 0 < C ∧ 0 < t0 ∧ 0 < thetaMax ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ t : ℝ, |t| ≤ min t0 (theta / 4) →
            let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
            (∀ i, IsFiniteMeasure (mu i)) ∧
              (∀ i, Integrable (fun x => Real.exp (t * x)) (mu i)) ∧
              Integrable (fun x => Real.exp (t * ∑ i, x i)) (Measure.pi mu) ∧
              (∫ x, Real.exp (t * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
                  Real.exp (((n - (kepInsertedCoordinates r).card : ℕ) : ℝ) * (t + C * t ^ 2)) := by
  obtain ⟨C, t0, ec, hC, ht0, hclean⟩ := kepReference_uniform_two_sided_mgf
  obtain ⟨tm, ei, htm, hei, hins⟩ := kepReference_insertion_measure_budgets
  refine ⟨C, t0, tm, max ec ei, hC, ht0, htm, hei.trans (le_max_right _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Ki, hKi, hi⟩ := hins theta ht htheta
  let K0 := max 1 Ki
  have hK0 : 1 ≤ K0 := le_max_left _ _
  have hKi0 : Ki ≤ K0 := le_max_right _ _
  refine ⟨K0 ^ 2, by positivity, ?_⟩
  intro eps he heps j hj n r hr t htime
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let H := kepInsertedCoordinates r
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hrcoord := (kepInsertionPattern_bounds hr).1
  have Hmu (i : Fin n) := hi eps ((le_max_right _ _).trans he) heps j hj (r i) (hrcoord i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (Hmu i).1
  have htimeClean : |t| ≤ t0 := htime.trans (min_le_left _ _)
  have htimeIns : t ≤ theta / 4 := (le_abs_self t).trans (htime.trans (min_le_right _ _))
  have hI (i : Fin n) : Integrable (fun x => Real.exp (t * x)) (mu i) :=
    ((Hmu i).2.2 t htimeIns).1
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hcost (i : Fin n) : 0 ≤ kepMellinInsertionCost (r i) J := by
    rw [kepMellinInsertionCost_eq_pow hJ (hrcoord i)]
    positivity
  have hbound (i : Fin n) : (∫ x, Real.exp (t * x) ∂mu i) ≤
      if i ∈ H then K0 * kepMellinInsertionCost (r i) J else Real.exp (t + C * t ^ 2) := by
    by_cases hiH : i ∈ H
    · rw [if_pos hiH]
      exact (((Hmu i).2.2 t htimeIns).2).trans
        (mul_le_mul_of_nonneg_right hKi0 (hcost i))
    · rw [if_neg hiH]
      have hr0 : r i = 0 := by
        by_contra hn
        exact hiH (mem_filter.mpr ⟨mem_univ _, hn⟩)
      dsimp [mu]
      rw [hr0, kepReferenceInsertionMeasure_zero]
      exact (hclean eps ((le_max_left _ _).trans he) j t htimeClean).2
  have hb := kep_pi_exp_sum_inserted_le mu H t (Real.exp (t + C * t ^ 2))
    (fun i => K0 * kepMellinInsertionCost (r i) J) hbound
  rw [← Real.exp_nat_mul] at hb
  refine ⟨fun i => (Hmu i).1, hI, kep_pi_exp_sum_integrable mu hI, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (kep_insertion_product_cost hr hJ hK0) (Real.exp_pos _).le

end

end PGM
