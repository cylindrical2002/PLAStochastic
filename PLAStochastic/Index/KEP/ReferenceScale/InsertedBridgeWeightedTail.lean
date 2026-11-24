import PLAStochastic.Index.KEP.ReferenceScale.InsertedBridgeSurvivalMass

/-!
# Actual weighted joint tail of survival and a tiny bridge

The complete output weight is paid by its genuine inserted product moment.
A fixed exponent on the original stopping scale is absorbed into survival
decay. Cauchy--Schwarz preserves the linear insertion budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kepReference_inserted_bridge_weighted_tail :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 16 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ A : Finset (Fin n), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
              E ⊆ (kepFiniteStoppedEvent eps n)ᶜ →
              E ⊆ {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} →
              ∀ u : ℝ, 0 ≤ u → u ≤ u0 / eps ^ 2 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              (∫ x in E, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
                  Real.exp (-c * A.card - c * n / eps ^ 2) := by
  obtain ⟨tm, em, htm, hem, hmass⟩ := kepReference_inserted_bridge_survival_mass
  obtain ⟨C, t0, te, ee, hC, ht0, hte, hee, hexp⟩ := kepReference_inserted_exponential_budget
  refine ⟨min tm te, max em ee, lt_min htm hte, hem.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Km, cm, hKm, hcm, hmb⟩ := hmass theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨Ke, hKe, heb⟩ := hexp theta ht (htheta.trans (min_le_right _ _))
  let u0 := min (t0 / 4) (min (theta / 16) (min (cm / 16) (1 / (16 * C))))
  have hu0 : 0 < u0 := lt_min (by positivity) (lt_min (by positivity)
    (lt_min (by positivity) (by positivity)))
  have htime : u0 ≤ t0 / 4 := min_le_left _ _
  have hthetaCap : u0 ≤ theta / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hdecay : u0 ≤ cm / 16 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hquad : u0 ≤ 1 / (16 * C) := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨Real.sqrt (Ke * Km), cm / 4, u0, Real.sqrt_pos.mpr (mul_pos hKe hKm),
    by positivity, hu0, hthetaCap, ?_⟩
  intro eps he heps j hj n r hr A E hE hEU hEL u hu huMax
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let J := kepReferenceWeightedSecondNorm theta eps j
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepssq : 1 ≤ eps ^ 2 := by nlinarith
  have hu0cap : u ≤ u0 := huMax.trans ((div_le_iff₀ (by positivity)).mpr (by nlinarith [hu0.le]))
  have hparam : |2 * u| ≤ min t0 (theta / 4) := by
    rw [abs_of_nonneg (by positivity)]
    exact le_min (by linarith) (by linarith)
  have hb := heb eps ((le_max_right _ _).trans he) heps j hj n r hr (2 * u) hparam
  have : ∀ i, IsFiniteMeasure (mu i) := hb.1
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hfull : (∫ x, Real.exp ((2 * u) * ∑ i, x i) ∂Measure.pi mu) ≤
      Ke * (1 + J) * Real.exp ((n : ℝ) * (2 * u + C * (2 * u) ^ 2)) := by
    apply hb.2.2.2.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.sub_le n (kepInsertedCoordinates r).card
  have hm := hmb eps ((le_max_left _ _).trans he) heps j hj n r hr A E hEU hEL
  have hS : Measurable (fun x : Fin n → ℝ => ∑ i, x i) :=
    Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)
  have hh := kep_weighted_event_cauchy hS hE (by positivity) (by positivity) hb.2.2.1 hfull hm
  rw [kep_sqrt_two_linear_exponential_budgets hKe.le hKm.le hJ] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have huC : 16 * C * u ≤ 1 := by
    have hbound := hu0cap.trans hquad
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 16 * C)).mp hbound
  have hquadratic : 2 * u + C * (2 * u) ^ 2 ≤ 3 * u := by
    have hh' := mul_le_mul_of_nonneg_right huC hu
    nlinarith only [hh', hu]
  have hsmall : u ≤ (cm / 16) / eps ^ 2 :=
    huMax.trans (div_le_div_of_nonneg_right hdecay (by positivity))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg A.card
  have hphase1 := mul_le_mul_of_nonneg_left hquadratic hn0
  have hphase2 := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 3 * n)
  have hphase : (n : ℝ) * (2 * u + C * (2 * u) ^ 2) ≤
      (3 * cm / 16) * n / eps ^ 2 := by
    have heq : 3 * (n : ℝ) * ((cm / 16) / eps ^ 2) = (3 * cm / 16) * n / eps ^ 2 := by ring
    rw [heq] at hphase2
    nlinarith only [hphase1, hphase2]
  have hneg : 0 ≤ cm * A.card := mul_nonneg hcm.le ha0
  have hnTerm : 0 ≤ cm * n / eps ^ 2 := div_nonneg (mul_nonneg hcm.le hn0) (sq_nonneg eps)
  have hphase' : (n : ℝ) * (2 * u + C * (2 * u) ^ 2) ≤
      (3 / 16) * (cm * n / eps ^ 2) := hphase.trans_eq (by ring)
  convert (show ((n : ℝ) * (2 * u + C * (2 * u) ^ 2) - cm * A.card -
      (cm * n / eps ^ 2)) / 2 ≤ -(cm * A.card) / 4 - (cm * n / eps ^ 2) / 4 by
    nlinarith only [hphase', hneg, hnTerm]) using 1 <;> ring

end

end PGM
