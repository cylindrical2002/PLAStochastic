import PLAStochastic.Index.KEP.ReferenceScale.FixedScaleBridgeTail
import PLAStochastic.Index.KEP.ReferenceScale.BridgeNegativeBudget

/-!
# Inverse-square insertion cost with a fixed stopping-scale output weight

The output scale coefficient is chosen before the input norm weight. A second
Cauchy--Schwarz pays the genuine fourth negative moment and preserves both
original event rates and a linear second-norm cost.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kepReference_inserted_bridge_fixed_scale_negative_budget :
    ∃ thetaMax eps0 V : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧ 0 < V ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c : ℝ,
        0 < K ∧ 0 < c ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 18 ≤ n → ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ A : Finset (Fin n), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
              E ⊆ (kepFiniteStoppedEvent eps n)ᶜ →
              E ⊆ {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} →
              ∀ u : ℝ, 0 ≤ u → u ≤ V / eps ^ 2 → u ≤ theta / 32 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              Integrable (E.indicator
                (fun x => ((∑ i, x i) ^ 2)⁻¹ * Real.exp (u * ∑ i, x i))) (Measure.pi mu) ∧
              (∫ x in E, ((∑ i, x i) ^ 2)⁻¹ * Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) / (n : ℝ) ^ 2 *
                  Real.exp (-c * A.card - c * n / eps ^ 2) := by
  obtain ⟨td, ed, Vd, htd, hed, hVd, hd⟩ := kepReference_inserted_bridge_fixed_scale_tail
  obtain ⟨tn, en, htn, hen, hn⟩ := kepReference_insertion_fourth_negative_budget
  obtain ⟨ti, ei, hti, hei, hi⟩ := kepReference_insertion_measure_budgets
  refine ⟨min td (min tn ti), max ed (max en ei), Vd / 2, lt_min htd (lt_min htn hti),
    hed.trans (le_max_left _ _), by positivity, ?_⟩
  intro theta ht htheta
  obtain ⟨Kd, cd, hKd, hcd, hdb⟩ := hd theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨Kn, hKn, hnb⟩ := hn theta ht ((htheta.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨_Ki, _, hib⟩ := hi theta ht ((htheta.trans (min_le_right _ _)).trans (min_le_right _ _))
  refine ⟨Real.sqrt (Kn * Kd), cd / 2, Real.sqrt_pos.mpr (mul_pos hKn hKd),
    by positivity, ?_⟩
  intro eps he heps j hj n hn18 r hr A E hE hEU hEL u hu0 hu huTheta
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let S := fun x : Fin n → ℝ => ∑ i, x i
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hS : Measurable S := Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hmu (i : Fin n) := hib eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    heps j hj (r i) ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have huScale : 2 * u ≤ Vd / eps ^ 2 :=
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have huCap : 2 * u ≤ theta / 4 := by linarith
  have hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) (Measure.pi mu) := by
    apply kep_pi_exp_sum_integrable
    exact fun i => ((hmu i).2.2 (2 * u) huCap).1
  have hnegative := hnb eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps j hj n hn18 r hr
  have hmass := hdb eps ((le_max_left _ _).trans he) heps j hj n r hr A E hE hEU hEL
    (2 * u) (by positivity) huScale (by linarith)
  have hh := kep_inverse_square_event_cauchy hS hE
    (by positivity : 0 ≤ Kn * (1 + J) / (n : ℝ) ^ 4)
    (by positivity : 0 ≤ Kd * (1 + J) * Real.exp (-cd * A.card - cd * n / eps ^ 2))
    hnegative hexp hmass
  refine ⟨hh.1, ?_⟩
  rw [kep_sqrt_inverse_square_exponential_budget hKn.le hKd.le hJ (by omega),
    show (-cd * A.card - cd * n / eps ^ 2) / 2 =
      -(cd / 2) * A.card - (cd / 2) * n / eps ^ 2 by ring] at hh
  exact hh.2

end

end PGM
