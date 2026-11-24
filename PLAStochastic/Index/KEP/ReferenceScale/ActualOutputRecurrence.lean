import PLAStochastic.Index.KEP.ReferenceScale.ActualOutputSecondBudget
import PLAStochastic.Index.KEP.ReferenceScale.ActualWeakSecondReadout

/-!
# The true weighted second-norm recurrence without analytic premises

The complete original output weak budget is read against the actual Gamma
second density. Compact C2 tests and their smooth sign approximation pay the
weighted norm. The recurrence is a theorem of the original reference orbit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepReference_actual_weighted_second_recurrence :
    ∃ thetaMax : ℝ, 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c E : ℝ,
        0 < K ∧ 0 < c ∧ kepReferenceClassicalThreshold ≤ E ∧
        ∀ eps, E ≤ eps → ∀ j : ℕ, 1 ≤ j →
          kepReferenceWeightedSecondNorm theta eps (j + 1) ≤
            K * eps ^ 47 * (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j)) +
            K * eps ^ 47 * Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j := by
  obtain ⟨tout, hto, houtput⟩ := kepReference_actual_output_weak_second_budget
  obtain ⟨ti, _Ki, ei, hti, -, _hei, hinitial⟩ := kepReference_small_weight_initial_budget
  refine ⟨min tout ti, lt_min hto hti, ?_⟩
  intro theta ht htmax
  obtain ⟨K, c, eo, hK, hc, heo, ho⟩ := houtput theta ht (htmax.trans (min_le_left _ _))
  refine ⟨K, c, max eo (max ei 3), hK, hc, heo.trans (le_max_left _ _), ?_⟩
  intro eps he j hj
  have heo' : eo ≤ eps := (le_max_left _ _).trans he
  have hei' : ei ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have he3 : 3 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have heps : kepReferenceClassicalThreshold ≤ eps := heo.trans heo'
  have hi := (hinitial theta ht.le (htmax.trans (min_le_right _ _)) eps hei').1 (j + 1) (by omega)
  have hbudget : kepReferenceWeightedSecondNorm theta eps (j + 1) ≤
      K * eps ^ 47 * (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j) +
        Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j) := by
    apply kepReference_weighted_norm_of_compact_second_tests heps he3 (by omega) hi
    intro phi hphi hsupp hb
    have hc1 : ContDiff ℝ 1 (deriv phi) := hphi.deriv'
    have hc2 := hc1.continuous_deriv (by norm_num)
    have hd : ∀ x, HasDerivAt phi (deriv phi x) x := fun x =>
      (hphi.differentiable (by norm_num) x).hasDerivAt
    have hdd : ∀ x, HasDerivAt (deriv phi) (deriv (deriv phi) x) x := fun x =>
      (hc1.differentiable (by norm_num) x).hasDerivAt
    obtain ⟨L, htest⟩ := kep_C2_compact_bounded_test hd hdd hc2 hsupp
    simpa only [one_mul] using ho eps heo' j hj phi (deriv phi) (deriv (deriv phi))
      hd hdd hc2 L htest 1 (by norm_num) (fun x _ => by simpa only [one_mul] using hb x)
  exact hbudget.trans_eq (by ring)

end

end PGM
