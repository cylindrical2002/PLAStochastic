import PLAStochastic.Index.KEP.ReferenceScale.RareSupportInsertionBudget
import PLAStochastic.Index.KEP.ReferenceScale.FixedScaleBridgeNegative

/-!
# The complete original rare support at a fixed stopping-scale weight

The stopping-scale coefficient is fixed before the derivative norm weight.
The bad-proportion cutoff remains an ordinary moment restriction, which a
large actual segment mean pays without changing the recurrence norm weight.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kepReference_original_rare_support_fixed_scale_budget :
    ∃ thetaMax eps0 V : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧ 0 < V ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 32 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ layer, ∀ hlayer : 1 ≤ layer, ∀ n i j : ℕ, 18 ≤ n → 16 * eps ≤ n →
            i < j → j ≤ n → 2 * eps < (j : ℝ) - i →
            ∀ r : Fin n → ℕ, (∑ t, r t) ≤ 2 → ∀ u : ℝ, 0 ≤ u → u ≤ V / eps ^ 2 → u ≤ u0 →
              let mu := fun t => kepReferenceInsertionMeasure heps hlayer (r t)
              Integrable ((kepFiniteRareSupport eps n i j).indicator
                (fun x => ((∑ t, x t) ^ 2)⁻¹ * Real.exp (u * ∑ t, x t))) (Measure.pi mu) ∧
              (∫ x in kepFiniteRareSupport eps n i j,
                ((∑ t, x t) ^ 2)⁻¹ * Real.exp (u * ∑ t, x t) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps layer) / (n : ℝ) ^ 2 *
                  (Real.exp (-c * n) + Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2)) := by
  obtain ⟨tb, eb, htb, heb, hbad⟩ := kepReference_inserted_rare_negative_budget
  obtain ⟨tt, et, Vt, htt, het, hVt, htiny⟩ := kepReference_inserted_bridge_fixed_scale_negative_budget
  obtain ⟨tn, en, htn, hen, hnegative⟩ := kepReference_insertion_fourth_negative_budget
  obtain ⟨ti, ei, hti, hei, hins⟩ := kepReference_insertion_measure_budgets
  let tm := min tb (min tt (min tn ti))
  let e0 := max 104 (max eb (max et (max en ei)))
  refine ⟨tm, e0, Vt, lt_min htb (lt_min htt (lt_min htn hti)),
    heb.trans ((le_max_left _ _).trans (le_max_right _ _)), hVt, ?_⟩
  intro theta ht htheta
  obtain ⟨Kb, cb, ub, hKb, hcb, hub, _hubcap, hbb⟩ :=
    hbad theta ht (htheta.trans (min_le_left _ _))
  have hrest := htheta.trans (min_le_right _ _)
  obtain ⟨Kt, ct, hKt, hct, htb'⟩ :=
    htiny theta ht (hrest.trans (min_le_left _ _))
  obtain ⟨Kn, hKn, hnb⟩ := hnegative theta ht
    ((hrest.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨_Ki, _, hib⟩ := hins theta ht
    ((hrest.trans (min_le_right _ _)).trans (min_le_right _ _))
  let c := min cb ct
  let u0 := min ub (theta / 32)
  have hc : 0 < c := lt_min hcb hct
  have hu0 : 0 < u0 := lt_min hub (by positivity)
  refine ⟨Kb + Kt, c, u0, by positivity, hc, hu0,
    min_le_right _ _, ?_⟩
  intro eps he heps layer hlayer n i j hn18 hn hij hjn hL r hr u hu huMax huDirect
  dsimp only
  let mu := fun t => kepReferenceInsertionMeasure heps hlayer (r t)
  let S := fun x : Fin n → ℝ => ∑ t, x t
  let J := kepReferenceWeightedSecondNorm theta eps layer
  let E := kepFiniteRareSupport eps n i j
  let Bad := E ∩ kepFiniteProportionBad n
  let Tiny := E \ kepFiniteProportionBad n
  let F := fun x => ((S x) ^ 2)⁻¹ * Real.exp (u * S x)
  have hE : MeasurableSet E := measurableSet_kepFiniteRareSupport eps n i j
  have hBad : MeasurableSet Bad := hE.inter (measurableSet_kepFiniteProportionBad n)
  have hTiny : MeasurableSet Tiny := hE.diff (measurableSet_kepFiniteProportionBad n)
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps layer
  have h104 : 104 ≤ eps := (le_max_left _ _).trans he
  have heRest : max eb (max et (max en ei)) ≤ eps := (le_max_right _ _).trans he
  have heB : eb ≤ eps := (le_max_left _ _).trans heRest
  have heT : et ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans heRest)
  have heN : en ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans heRest))
  have heI : ei ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans heRest))
  have hmu (t : Fin n) := hib eps heI heps layer hlayer (r t) ((kepInsertionPattern_bounds hr).1 t)
  have : ∀ t, IsFiniteMeasure (mu t) := fun t => (hmu t).1
  have huB : u ≤ ub := huDirect.trans (min_le_left _ _)
  have huTheta : u ≤ theta / 32 := huDirect.trans (min_le_right _ _)
  have huCap : 2 * u ≤ theta / 4 := by linarith
  have hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) (Measure.pi mu) := by
    apply kep_pi_exp_sum_integrable
    exact fun t => ((hmu t).2.2 (2 * u) huCap).1
  have hS : Measurable S := Finset.measurable_sum Finset.univ (fun t _ => measurable_pi_apply t)
  have hneg := hnb eps heN heps layer hlayer n hn18 r hr
  have hGlobal := kep_inverse_square_event_cauchy hS MeasurableSet.univ
    (by positivity : 0 ≤ Kn * (1 + J) / (n : ℝ) ^ 4)
    (integral_nonneg (fun _ => (Real.exp_pos _).le)) hneg hexp
    (by simp only [setIntegral_univ]; exact le_rfl)
  have hiF : Integrable F (Measure.pi mu) := by simpa only [indicator_univ] using hGlobal.1
  have hfb := hbb eps heB heps layer hlayer n hn18 r hr u hu huB Bad hBad inter_subset_right
  have hft := htb' eps heT heps layer hlayer n hn18 r hr (kepFiniteBridge n i j) Tiny hTiny
    (kepFiniteRareSupport_tiny_subset_survival eps n i j)
    (kepFiniteRareSupport_tiny_subset_bridge h104 hn hij hjn hL) u hu huMax huTheta
  have hcover : E ⊆ Bad ∪ Tiny := by
    intro x hx
    by_cases hb : x ∈ kepFiniteProportionBad n
    · exact Or.inl ⟨hx, hb⟩
    · exact Or.inr ⟨hx, hb⟩
  have hh := kep_integral_event_le_two hiF (fun _ => by dsimp [F]; positivity) hE hBad hTiny hcover
  have hcb' : c ≤ cb := min_le_left _ _
  have hct' : c ≤ ct := min_le_right _ _
  have hbexp : Real.exp (-cb * n) ≤ Real.exp (-c * n) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hcb', (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have htexp : Real.exp (-ct * (j - i : ℕ) - ct * n / eps ^ 2) ≤
      Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hl := mul_le_mul_of_nonneg_right hct' (Nat.cast_nonneg (j - i) : (0 : ℝ) ≤ (j - i : ℕ))
    have hn' := mul_le_mul_of_nonneg_right hct' (div_nonneg (Nat.cast_nonneg n) (sq_nonneg eps))
    convert (show -(ct * (j - i : ℕ)) - ct * ((n : ℝ) / eps ^ 2) ≤
        -(c * (j - i : ℕ)) - c * ((n : ℝ) / eps ^ 2) by linarith only [hl, hn']) using 1 <;> ring
  refine ⟨hiF.indicator hE, ?_⟩
  apply hh.trans
  rw [kepFiniteBridge_card hij.le hjn] at hft
  have hb' := hfb.trans (mul_le_mul_of_nonneg_left hbexp (by positivity))
  have ht' := hft.2.trans (mul_le_mul_of_nonneg_left htexp (by positivity))
  apply (add_le_add hb' ht').trans
  have hbnn : 0 ≤ Real.exp (-c * n) := (Real.exp_pos _).le
  have htnn : 0 ≤ Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2) := (Real.exp_pos _).le
  have hbase : 0 ≤ (1 + J) / (n : ℝ) ^ 2 := by positivity
  have hcross : 0 ≤ Kb * ((1 + J) / (n : ℝ) ^ 2) * Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2) +
      Kt * ((1 + J) / (n : ℝ) ^ 2) * Real.exp (-c * n) := by positivity
  calc
    _ ≤ Kb * (1 + J) / (n : ℝ) ^ 2 * Real.exp (-c * n) +
        Kt * (1 + J) / (n : ℝ) ^ 2 * Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2) +
        (Kb * ((1 + J) / (n : ℝ) ^ 2) * Real.exp (-c * (j - i : ℕ) - c * n / eps ^ 2) +
          Kt * ((1 + J) / (n : ℝ) ^ 2) * Real.exp (-c * n)) := le_add_of_nonneg_right hcross
    _ = _ := by dsimp only [J]; ring

end

end PGM
