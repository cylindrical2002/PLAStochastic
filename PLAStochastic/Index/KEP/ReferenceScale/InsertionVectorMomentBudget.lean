import PLAStochastic.Index.KEP.ReferenceScale.InsertionProductBudget

/-!
# Actual inserted moments with different parameters in every coordinate

Partial sums and the complete output weight use different Chernoff parameters.
Each clean coordinate retains its actual two-sided centered moment bound; at
most two inserted coordinates pay a single linear second-norm cost.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

theorem kep_pi_exp_linear_integral {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] (t : Fin n → ℝ) :
    (∫ x, Real.exp (∑ i, t i * x i) ∂Measure.pi mu) =
      ∏ i, ∫ x, Real.exp (t i * x) ∂mu i := by
  simp_rw [Real.exp_sum]
  exact integral_fintype_prod_eq_prod (fun i x => Real.exp (t i * x))

theorem kep_pi_exp_linear_integrable {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, SigmaFinite (mu i)] {t : Fin n → ℝ}
    (hi : ∀ i, Integrable (fun x => Real.exp (t i * x)) (mu i)) :
    Integrable (fun x => Real.exp (∑ i, t i * x i)) (Measure.pi mu) := by
  simp_rw [Real.exp_sum]
  exact Integrable.fintype_prod hi

theorem kepReference_inserted_vector_moment_budget :
    ∃ C t0 thetaMax eps0 : ℝ, 0 < C ∧ 0 < t0 ∧ 0 < thetaMax ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K : ℝ, 0 < K ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ t : Fin n → ℝ, (∀ i, |t i| ≤ min t0 (theta / 4)) →
            let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
            (∀ i, IsFiniteMeasure (mu i)) ∧
              (∀ i, Integrable (fun x => Real.exp (t i * x)) (mu i)) ∧
              Integrable (fun x => Real.exp (∑ i, t i * x i)) (Measure.pi mu) ∧
              (∫ x, Real.exp (∑ i, t i * x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
                  Real.exp (∑ i ∈ univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2)) := by
  obtain ⟨C, t0, ec, hC, ht0, hclean⟩ := kepReference_uniform_two_sided_mgf
  obtain ⟨tm, ei, htm, hei, hins⟩ := kepReference_insertion_measure_budgets
  refine ⟨C, t0, tm, max ec ei, hC, ht0, htm, hei.trans (le_max_right _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Ki, _, hi⟩ := hins theta ht htheta
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
  have htimeClean (i) : |t i| ≤ t0 := (htime i).trans (min_le_left _ _)
  have htimeIns (i) : t i ≤ theta / 4 := (le_abs_self (t i)).trans ((htime i).trans (min_le_right _ _))
  have hI (i) : Integrable (fun x => Real.exp (t i * x)) (mu i) :=
    ((Hmu i).2.2 (t i) (htimeIns i)).1
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hcost (i) : 0 ≤ kepMellinInsertionCost (r i) J := by
    rw [kepMellinInsertionCost_eq_pow hJ (hrcoord i)]
    positivity
  have hbound (i : Fin n) : (∫ x, Real.exp (t i * x) ∂mu i) ≤
      if i ∈ H then K0 * kepMellinInsertionCost (r i) J else Real.exp (t i + C * (t i) ^ 2) := by
    by_cases hiH : i ∈ H
    · rw [if_pos hiH]
      exact (((Hmu i).2.2 (t i) (htimeIns i)).2).trans
        (mul_le_mul_of_nonneg_right hKi0 (hcost i))
    · rw [if_neg hiH]
      have hr0 : r i = 0 := by
        by_contra hn
        exact hiH (mem_filter.mpr ⟨mem_univ _, hn⟩)
      dsimp [mu]
      rw [hr0, kepReferenceInsertionMeasure_zero]
      exact (hclean eps ((le_max_left _ _).trans he) j (t i) (htimeClean i)).2
  have hb : (∫ x, Real.exp (∑ i, t i * x i) ∂Measure.pi mu) ≤
      (∏ i ∈ H, K0 * kepMellinInsertionCost (r i) J) *
        Real.exp (∑ i ∈ univ \ H, (t i + C * (t i) ^ 2)) := by
    rw [kep_pi_exp_linear_integral]
    have hp := prod_le_prod (s := univ) (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
      (fun i _ => hbound i)
    apply hp.trans_eq
    rw [prod_ite, filter_mem_eq_inter, ← sdiff_eq_filter, Finset.univ_inter, ← Real.exp_sum]
  refine ⟨fun i => (Hmu i).1, hI, kep_pi_exp_linear_integrable mu hI, hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_right (kep_insertion_product_cost hr hJ hK0) (Real.exp_pos _).le

end

end PGM
