import PLAStochastic.Index.KEP.ReferenceScale.InsertedSurvivalTail
import PLAStochastic.Index.KEP.ReferenceScale.InsertedSubsetLowerTail
import PLAStochastic.Index.KEP.ReferenceScale.EventGeometricBudget

/-!
# Joint actual inserted mass of survival and a tiny bridge

The two genuine event bounds combine geometrically. The result retains decay
both in the complete prefix length on the stopping scale and in the bridge
length, without an independence assumption between those events.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kepReference_inserted_bridge_survival_mass :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ A : Finset (Fin n), ∀ E : Set (Fin n → ℝ),
              E ⊆ (kepFiniteStoppedEvent eps n)ᶜ →
              E ⊆ {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              (Measure.pi mu).real E ≤ K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
                Real.exp (-c * A.card - c * n / eps ^ 2) := by
  obtain ⟨ts, es, hts, hes, hsurv⟩ := kepReference_inserted_survival_tail
  obtain ⟨tb, eb, htb, heb, hbridge⟩ := kepReference_inserted_subset_lower_tail
  obtain ⟨ti, ei, hti, hei, hins⟩ := kepReference_insertion_measure_budgets
  refine ⟨min ts (min tb ti), max es (max eb ei), lt_min hts (lt_min htb hti),
    hes.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Ks, cs, hKs, hcs, hsb⟩ := hsurv theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨Kb, cb, hKb, hcb, hbb⟩ := hbridge theta ht
    ((htheta.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨_Ki, _, hib⟩ := hins theta ht
    ((htheta.trans (min_le_right _ _)).trans (min_le_right _ _))
  let c := min cs cb / 2
  have hc : 0 < c := by dsimp [c]; exact div_pos (lt_min hcs hcb) (by norm_num)
  have hccs : 2 * c ≤ cs := by dsimp [c]; linarith [min_le_left cs cb]
  have hccb : 2 * c ≤ cb := by dsimp [c]; linarith [min_le_right cs cb]
  refine ⟨Real.sqrt (Ks * Kb), c, Real.sqrt_pos.mpr (mul_pos hKs hKb), hc, ?_⟩
  intro eps he heps j hj n r hr A E hEU hEL
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hmu (i : Fin n) := hib eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    heps j hj (r i) ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hU : (Measure.pi mu).real (kepFiniteStoppedEvent eps n)ᶜ ≤
      Ks * (1 + J) * Real.exp (-cs * n / eps ^ 2) := by
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    exact hsb eps ((le_max_left _ _).trans he) heps j hj n r hr
  have hL : (Measure.pi mu).real {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} ≤
      Kb * (1 + J) * Real.exp (-cb * A.card) := by
    have hh := hbb eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps j hj n r hr A
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using hh
  have hh := kep_measureReal_event_geometric hEU hEL (by positivity) (by positivity) hU hL
  rw [kep_sqrt_two_linear_exponential_budgets hKs.le hKb.le hJ] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg A.card
  have hs := mul_le_mul_of_nonneg_right hccs (div_nonneg hn0 (sq_nonneg eps))
  have hb := mul_le_mul_of_nonneg_right hccb hA0
  calc
    (-cs * n / eps ^ 2 + -cb * A.card) / 2 =
        -(cs * ((n : ℝ) / eps ^ 2)) / 2 - cb * A.card / 2 := by ring
    _ ≤ -c * ((n : ℝ) / eps ^ 2) - c * A.card := by nlinarith only [hs, hb]
    _ = _ := by ring

end

end PGM
