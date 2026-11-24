import PLAStochastic.Index.KEP.ReferenceScale.InsertedStoppedTail
import PLAStochastic.Index.KEP.ReferenceScale.RareNegativeBudget

/-!
# Actual inverse-square budget on the original short stopping event

The fourth negative moment and the complete original stopping tail combine by
Cauchy--Schwarz. The result includes integrability of the weighted event term,
and keeps the insertion cost linear in the actual weighted second norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kep_inverse_square_event_cauchy {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} {S : alpha → ℝ} (hS : Measurable S)
    {E : Set alpha} (hE : MeasurableSet E) {u A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hnegative : (∫⁻ x, ENNReal.ofReal ((S x) ^ (-4 : ℝ)) ∂mu) ≤ ENNReal.ofReal A)
    (hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) mu)
    (hmass : (∫ x in E, Real.exp ((2 * u) * S x) ∂mu) ≤ B) :
    Integrable (E.indicator (fun x => ((S x) ^ 2)⁻¹ * Real.exp (u * S x))) mu ∧
      (∫ x in E, ((S x) ^ 2)⁻¹ * Real.exp (u * S x) ∂mu) ≤ Real.sqrt (A * B) := by
  let f := fun x => ((S x) ^ 2)⁻¹
  let g := E.indicator (fun x => Real.exp (u * S x))
  have hf : Measurable f := (hS.pow_const 2).inv
  have hg : Measurable g := (hS.const_mul u).exp.indicator hE
  have hfn (x) : 0 ≤ f x := inv_nonneg.mpr (sq_nonneg _)
  have hgn (x) : 0 ≤ g x := indicator_nonneg (fun x _ => (Real.exp_pos _).le) x
  have hsq (x) : f x ^ 2 = (S x) ^ (-4 : ℝ) := by
    dsimp [f]
    rw [Real.rpow_neg_ofNat]
    simp only [zpow_neg, zpow_ofNat, inv_pow]
    congr 1
    ring
  have hneg : Integrable (fun x => f x ^ 2) mu ∧ (∫ x, f x ^ 2 ∂mu) ≤ A := by
    apply kep_integrable_of_nonnegative_lintegral_bound (hf.pow_const 2) (fun _ => sq_nonneg _) hA
    simpa only [hsq] using hnegative
  have hg2 (x) : g x ^ 2 = E.indicator (fun x => Real.exp ((2 * u) * S x)) x := by
    by_cases hx : x ∈ E
    · simp only [g, indicator_of_mem hx, sq, ← Real.exp_add]
      congr 1
      ring
    · simp only [g, indicator_of_notMem hx, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  have hgi : Integrable (fun x => g x ^ 2) mu := by
    simpa only [hg2] using hexp.indicator hE
  have hgB : (∫ x, g x ^ 2 ∂mu) ≤ B := by
    simpa only [hg2, integral_indicator hE] using hmass
  have heq : (fun x => f x * g x) = E.indicator (fun x => ((S x) ^ 2)⁻¹ * Real.exp (u * S x)) := by
    funext x
    by_cases hx : x ∈ E
    · simp only [f, g, indicator_of_mem hx]
    · simp only [g, indicator_of_notMem hx, mul_zero]
  have hflp : MemLp f 2 mu := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hneg.1
  have hglp : MemLp g 2 mu := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr hgi
  have hfg : Integrable (fun x => f x * g x) mu := memLp_one_iff_integrable.mp (hglp.mul' hflp)
  refine ⟨heq ▸ hfg, ?_⟩
  have hh := kep_integral_mul_le_sqrt_budget hf hg hfn hgn hneg.1 hgi hA hB hneg.2 hgB
  rw [heq, integral_indicator hE] at hh
  exact hh

theorem kep_sqrt_short_stopped_budget {A B J c eps : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hJ : 0 ≤ J) {n : ℕ} (hn : 0 < n) :
    Real.sqrt ((A * (1 + J) / (n : ℝ) ^ 4) *
      (B * ((n : ℝ) + 1) ^ 2 * (1 + J) * Real.exp (-c * eps))) =
        Real.sqrt (A * B) * ((n : ℝ) + 1) * (1 + J) / (n : ℝ) ^ 2 *
          Real.exp (-(c / 2) * eps) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (A * (1 + J) / (n : ℝ) ^ 4) *
      (B * ((n : ℝ) + 1) ^ 2 * (1 + J) * Real.exp (-c * eps)) =
      (A * B) * ((((n : ℝ) + 1) * (1 + J)) ^ 2 / ((n : ℝ) ^ 2) ^ 2) * Real.exp (-c * eps) by ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ A * B *
      ((((n : ℝ) + 1) * (1 + J)) ^ 2 / ((n : ℝ) ^ 2) ^ 2)),
    Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_div (by positivity),
    Real.sqrt_sq (by positivity : 0 ≤ ((n : ℝ) + 1) * (1 + J)),
    Real.sqrt_sq (sq_nonneg (n : ℝ)), ← Real.exp_half]
  rw [show -c * eps / 2 = -(c / 2) * eps by ring]
  ring

theorem kepReference_inserted_stopped_negative_budget :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 8 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 18 ≤ n → (n : ℝ) ≤ 17 * eps →
            ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 → ∀ u : ℝ, 0 ≤ u → u ≤ u0 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              Integrable ((kepFiniteStoppedEvent eps n).indicator
                (fun x => ((∑ i, x i) ^ 2)⁻¹ * Real.exp (u * ∑ i, x i))) (Measure.pi mu) ∧
              (∫ x in kepFiniteStoppedEvent eps n, ((∑ i, x i) ^ 2)⁻¹ *
                Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (n + 1) * (1 + kepReferenceWeightedSecondNorm theta eps j) / (n : ℝ) ^ 2 *
                  Real.exp (-c * eps) := by
  obtain ⟨td, ed, htd, hed, hd⟩ := kepReference_inserted_stopped_tail
  obtain ⟨tn, en, htn, hen, hn⟩ := kepReference_insertion_fourth_negative_budget
  obtain ⟨ti, ei, hti, hei, hi⟩ := kepReference_insertion_measure_budgets
  refine ⟨min td (min tn ti), max ed (max en ei), lt_min htd (lt_min htn hti),
    hed.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨Kd, cd, ud, hKd, hcd, hud, hudcap, hdb⟩ := hd theta ht (htheta.trans (min_le_left _ _))
  obtain ⟨Kn, hKn, hnb⟩ := hn theta ht ((htheta.trans (min_le_right _ _)).trans (min_le_left _ _))
  obtain ⟨_Ki, _, hib⟩ := hi theta ht ((htheta.trans (min_le_right _ _)).trans (min_le_right _ _))
  refine ⟨Real.sqrt (Kn * Kd), cd / 2, ud / 2, Real.sqrt_pos.mpr (mul_pos hKn hKd),
    by positivity, by positivity, by linarith, ?_⟩
  intro eps he heps j hj n hn18 hnMax r hr u hu0 hu
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let S := fun x : Fin n → ℝ => ∑ i, x i
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hS : Measurable S := Finset.measurable_sum univ (fun i _ => measurable_pi_apply i)
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hmu (i : Fin n) := hib eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    heps j hj (r i) ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) (Measure.pi mu) := by
    apply kep_pi_exp_sum_integrable
    exact fun i => ((hmu i).2.2 (2 * u) (by linarith)).1
  have hm := hdb eps ((le_max_left _ _).trans he) heps j hj n hnMax r hr (2 * u)
    (by positivity) (by linarith)
  have hmass : (∫ x in kepFiniteStoppedEvent eps n, Real.exp ((2 * u) * S x) ∂Measure.pi mu) ≤
      Kd * ((n : ℝ) + 1) ^ 2 * (1 + J) * Real.exp (-cd * eps) := by
    apply hm.trans
    have hn1 : 1 ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hnsq : (n : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnsq hKd.le) (by positivity))
      (Real.exp_pos _).le
  have hnegative := hnb eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps j hj n hn18 r hr
  have hh := kep_inverse_square_event_cauchy hS (measurableSet_kepFiniteStoppedEvent eps n)
    (by positivity : 0 ≤ Kn * (1 + J) / (n : ℝ) ^ 4)
    (by positivity : 0 ≤ Kd * ((n : ℝ) + 1) ^ 2 * (1 + J) * Real.exp (-cd * eps))
    hnegative hexp hmass
  refine ⟨hh.1, ?_⟩
  rw [kep_sqrt_short_stopped_budget hKn.le hKd.le hJ (by omega)] at hh
  exact hh.2

end

end PGM
