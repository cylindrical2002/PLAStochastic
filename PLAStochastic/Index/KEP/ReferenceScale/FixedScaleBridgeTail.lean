import PLAStochastic.Index.KEP.ReferenceScale.FixedInsertedSurvivalRate
import PLAStochastic.Index.KEP.ReferenceScale.InsertedBridgeSurvivalMass
import PLAStochastic.Index.KEP.ReferenceScale.InsertedBridgeWeightedTail

/-!
# A stopping-scale output weight chosen before the Mellin input weight

Survival and tiny-bridge rates are kept separate until the output weight has
been absorbed. Thus the allowed coefficient of `eps⁻²` is independent of the
input derivative weight; the ordinary small-moment restriction is explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kepReference_inserted_bridge_fixed_scale_tail :
    ∃ thetaMax eps0 V : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧ 0 < V ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ A : Finset (Fin n), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
              E ⊆ (kepFiniteStoppedEvent eps n)ᶜ →
              E ⊆ {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} →
              ∀ u : ℝ, 0 ≤ u → u ≤ V / eps ^ 2 → u ≤ theta / 16 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              (∫ x in E, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
                  Real.exp (-c * A.card - c * n / eps ^ 2) := by
  obtain ⟨ts, es, cs, hts, hes, hcs, hsurv⟩ := kepReference_inserted_survival_fixed_rate
  obtain ⟨tb, eb, htb, heb, hbridge⟩ := kepReference_inserted_subset_lower_tail
  obtain ⟨C, t0, te, ee, hC, ht0, hte, hee, hexp⟩ := kepReference_inserted_exponential_budget
  let V := min (t0 / 4) (min (cs / 32) (1 / (16 * C)))
  have hV : 0 < V := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hVt : V ≤ t0 / 4 := min_le_left _ _
  have hVs : V ≤ cs / 32 := (min_le_right _ _).trans (min_le_left _ _)
  have hVC : V ≤ 1 / (16 * C) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨min ts (min tb te), max es (max eb ee), V,
    lt_min hts (lt_min htb hte), hes.trans (le_max_left _ _), hV, ?_⟩
  intro theta ht htcap
  obtain ⟨Ks, hKs, hsb⟩ := hsurv theta ht (htcap.trans (min_le_left _ _))
  obtain ⟨Kb, cb, hKb, hcb, hbb⟩ := hbridge theta ht
    ((htcap.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨Ke, hKe, hebudget⟩ := hexp theta ht
    ((htcap.trans (min_le_right _ _)).trans (min_le_right _ _))
  let c := min (cs / 8) (cb / 4)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨Real.sqrt (Ke * Real.sqrt (Ks * Kb)), c, by positivity, hc, ?_⟩
  intro eps he heps j hj n r hr A E hE hEU hEL u hu huScale huTheta
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let J := kepReferenceWeightedSecondNorm theta eps j
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hesq : 1 ≤ eps ^ 2 := by nlinarith
  have huV : u ≤ V := huScale.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith [hV.le]))
  have hparam : |2 * u| ≤ min t0 (theta / 4) := by
    rw [abs_of_nonneg (by positivity)]
    exact le_min (by linarith) (by linarith)
  have hb := hebudget eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    heps j hj n r hr (2 * u) hparam
  have : ∀ i, IsFiniteMeasure (mu i) := hb.1
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hU : (Measure.pi mu).real (kepFiniteStoppedEvent eps n)ᶜ ≤
      Ks * (1 + J) * Real.exp (-cs * n / eps ^ 2) := by
    apply ENNReal.toReal_le_of_le_ofReal (by positivity)
    exact hsb eps ((le_max_left _ _).trans he) heps j hj n r hr
  have hL : (Measure.pi mu).real {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} ≤
      Kb * (1 + J) * Real.exp (-cb * A.card) := by
    have hh := hbb eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps j hj n r hr A
    simpa only [integral_const, smul_eq_mul, mul_one, measureReal_restrict_apply_univ] using hh
  have hm := kep_measureReal_event_geometric hEU hEL (by positivity) (by positivity) hU hL
  rw [kep_sqrt_two_linear_exponential_budgets hKs.le hKb.le hJ] at hm
  have hfull : (∫ x, Real.exp ((2 * u) * ∑ i, x i) ∂Measure.pi mu) ≤
      Ke * (1 + J) * Real.exp ((n : ℝ) * (2 * u + C * (2 * u) ^ 2)) := by
    apply hb.2.2.2.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le n (kepInsertedCoordinates r).card
  have hS : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)
  have hh := kep_weighted_event_cauchy hS hE (by positivity) (by positivity) hb.2.2.1 hfull hm
  rw [kep_sqrt_two_linear_exponential_budgets hKe.le (Real.sqrt_nonneg _) hJ] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have huC : 16 * C * u ≤ 1 := by
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 16 * C)).mp (huV.trans hVC)
  have hquad : 2 * u + C * (2 * u) ^ 2 ≤ 3 * u := by
    nlinarith only [mul_le_mul_of_nonneg_right huC hu, hu]
  have huS : u ≤ (cs / 32) / eps ^ 2 :=
    huScale.trans (div_le_div_of_nonneg_right hVs (sq_nonneg eps))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg A.card
  have hphase : (n : ℝ) * (2 * u + C * (2 * u) ^ 2) ≤ (3 / 32) * (cs * n / eps ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hquad hn0
    have h2 := mul_le_mul_of_nonneg_left huS (by positivity : (0 : ℝ) ≤ 3 * n)
    have heq : 3 * (n : ℝ) * ((cs / 32) / eps ^ 2) = (3 / 32) * (cs * n / eps ^ 2) := by ring
    rw [heq] at h2
    nlinarith only [h1, h2]
  have hcsN : 0 ≤ cs * n / eps ^ 2 := by positivity
  have hcbA : 0 ≤ cb * A.card := by positivity
  have hcn := mul_le_mul_of_nonneg_right (min_le_left (cs / 8) (cb / 4))
    (div_nonneg hn0 (sq_nonneg eps))
  have hcA := mul_le_mul_of_nonneg_right (min_le_right (cs / 8) (cb / 4)) ha0
  have hp : ((n : ℝ) * (2 * u + C * (2 * u) ^ 2) +
      (-cs * n / eps ^ 2 + -cb * A.card) / 2) / 2 ≤
      -(cs * n / eps ^ 2) / 8 - (cb * A.card) / 4 := by
    rw [show (-cs * (n : ℝ) / eps ^ 2 + -cb * A.card) / 2 =
      -(cs * n / eps ^ 2) / 2 - (cb * A.card) / 2 by ring]
    linarith only [hphase, hcsN]
  have hn' : c * ((n : ℝ) / eps ^ 2) ≤ (cs * n / eps ^ 2) / 8 := hcn.trans_eq (by ring)
  have hA' : c * (A.card : ℝ) ≤ (cb * A.card) / 4 := hcA.trans_eq (by ring)
  calc
    _ ≤ -(cs * n / eps ^ 2) / 8 - (cb * A.card) / 4 := hp
    _ ≤ -c * ((n : ℝ) / eps ^ 2) - c * A.card := by linarith only [hn', hA']
    _ = _ := by ring

end

end PGM
