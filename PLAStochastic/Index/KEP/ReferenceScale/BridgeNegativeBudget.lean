import PLAStochastic.Index.KEP.ReferenceScale.InsertedBridgeWeightedTail
import PLAStochastic.Index.KEP.ReferenceScale.StoppedNegativeBudget

/-!
# Actual inverse-square budget on every surviving tiny-bridge event

The true weighted joint tail and the actual fourth negative moment pay the
physical derivative factor. All insertion costs remain linear, and both the
bridge and complete-prefix decay survive Cauchy--Schwarz.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

theorem kep_sqrt_inverse_square_exponential_budget {A B J z : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J) {n : ℕ} (hn : 0 < n) :
    Real.sqrt ((A * (1 + J) / (n : ℝ) ^ 4) * (B * (1 + J) * Real.exp z)) =
      Real.sqrt (A * B) * (1 + J) / (n : ℝ) ^ 2 * Real.exp (z / 2) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [show (A * (1 + J) / (n : ℝ) ^ 4) * (B * (1 + J) * Real.exp z) =
      (A * B) * ((1 + J) ^ 2 / ((n : ℝ) ^ 2) ^ 2) * Real.exp z by ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ A * B * ((1 + J) ^ 2 / ((n : ℝ) ^ 2) ^ 2)),
    Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_div (by positivity),
    Real.sqrt_sq (by positivity : 0 ≤ 1 + J), Real.sqrt_sq (sq_nonneg (n : ℝ)), ← Real.exp_half]
  ring

theorem kepReference_inserted_bridge_negative_budget :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 32 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 18 ≤ n → ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ A : Finset (Fin n), ∀ E : Set (Fin n → ℝ), MeasurableSet E →
              E ⊆ (kepFiniteStoppedEvent eps n)ᶜ →
              E ⊆ {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8} →
              ∀ u : ℝ, 0 ≤ u → u ≤ u0 / eps ^ 2 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              Integrable (E.indicator
                (fun x => ((∑ i, x i) ^ 2)⁻¹ * Real.exp (u * ∑ i, x i))) (Measure.pi mu) ∧
              (∫ x in E, ((∑ i, x i) ^ 2)⁻¹ * Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) / (n : ℝ) ^ 2 *
                  Real.exp (-c * A.card - c * n / eps ^ 2) := by
  obtain ⟨td, ed, htd, hed, hd⟩ := kepReference_inserted_bridge_weighted_tail
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
  intro eps he heps j hj n hn18 r hr A E hE hEU hEL u hu0 hu
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let S := fun x : Fin n → ℝ => ∑ i, x i
  let J := kepReferenceWeightedSecondNorm theta eps j
  have hS : Measurable S := Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hmu (i : Fin n) := hib eps ((le_max_right _ _).trans ((le_max_right _ _).trans he))
    heps j hj (r i) ((kepInsertionPattern_bounds hr).1 i)
  have : ∀ i, IsFiniteMeasure (mu i) := fun i => (hmu i).1
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hepssq : 1 ≤ eps ^ 2 := by nlinarith
  have huScale : 2 * u ≤ ud / eps ^ 2 :=
    (mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have huCap : 2 * u ≤ theta / 4 := by
    have hscale : ud / eps ^ 2 ≤ ud := (div_le_iff₀ (by positivity)).mpr (by nlinarith [hud.le])
    linarith only [huScale, hscale, hudcap, ht]
  have hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) (Measure.pi mu) := by
    apply kep_pi_exp_sum_integrable
    exact fun i => ((hmu i).2.2 (2 * u) huCap).1
  have hnegative := hnb eps ((le_max_left _ _).trans ((le_max_right _ _).trans he)) heps j hj n hn18 r hr
  have hmass := hdb eps ((le_max_left _ _).trans he) heps j hj n r hr A E hE hEU hEL
    (2 * u) (by positivity) huScale
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
