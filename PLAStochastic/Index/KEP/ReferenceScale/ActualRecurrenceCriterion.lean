import PLAStochastic.Index.KEP.ReferenceScale.ActualScaleFamily
import PLAStochastic.Index.KEP.ReferenceScale.Recurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Closing the actual orbit once its weighted output recurrence is proved

The initial budget and finite weighted derivative norms come from the actual
Gamma orbit. The only remaining analytic premise in the uniform-norm criterion
is the recurrence for the actual weighted second norm; no abstract replacement
sequence or independent regularity certificate is used.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem kepReference_small_weight_initial_budget :
    ∃ thetaMax K eps0 : ℝ, 0 < thetaMax ∧ 0 ≤ K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 ≤ theta → theta ≤ thetaMax →
        ∀ eps, eps0 ≤ eps →
          (∀ j : ℕ, 1 ≤ j →
            Integrable (fun t => Real.exp (theta * t) *
              gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j) t) volume) ∧
          kepReferenceWeightedSecondNorm theta eps 1 ≤ K * eps ^ 4 := by
  obtain ⟨D, theta0, vlo, vhi, e0, hD, ht0, hvlo, -, hreg⟩ := kepReferenceLaw_regular
  let thetaMax := min (theta0 / 2) (1 / 2)
  let M := 2 * D / theta0
  let cb := cBr (bIn 1 1) (vIn 1 1)
  have ht : 0 < thetaMax := lt_min (by positivity) (by norm_num)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨thetaMax, 4 * M * cb ^ 2, max kepReferenceClassicalThreshold e0,
    ht, by positivity, le_max_left _ _, ?_⟩
  intro theta htheta hsmall eps heps
  have he : kepReferenceClassicalThreshold ≤ eps := (le_max_left _ _).trans heps
  have hr : e0 ≤ eps := (le_max_right _ _).trans heps
  have hb (j : ℕ) (hj : 1 ≤ j) := kepReferenceDensity_weighted_of_regular he hj ht0 hvlo
    (hreg eps hr j) htheta (hsmall.trans (min_le_left _ _)) (hsmall.trans (min_le_right _ _))
  refine ⟨fun j hj => (hb j hj).2.1, ?_⟩
  have h := (hb 1 le_rfl).2.2.2
  have hm := kepReferenceSpan_pos he 1
  have hup := kepReferenceSpan_one_le he
  have hsq : (kepReferenceSpan eps 1) ^ 2 ≤ (cb * eps ^ 2) ^ 2 := by gcongr
  calc
    _ ≤ 4 * (kepReferenceSpan eps 1) ^ 2 * M := h
    _ ≤ 4 * (cb * eps ^ 2) ^ 2 * M := by gcongr
    _ = _ := by ring

/-- This criterion does not assert its actual-output recurrence premise. -/
theorem kepReference_uniform_second_norm_of_recurrence :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax →
        ∀ A : ℝ, 0 ≤ A → ∀ p : ℕ, ∀ c : ℝ, 0 < c →
          (∀ eps, eps0 ≤ eps → ∀ j : ℕ, 1 ≤ j →
            kepReferenceWeightedSecondNorm theta eps (j + 1) ≤
              A * eps ^ p * (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j)) +
              A * eps ^ p * Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j) →
          ∃ K E : ℝ, 0 < K ∧ eps0 ≤ E ∧
            ∀ eps, E ≤ eps → ∀ j : ℕ, 1 ≤ j →
              kepReferenceWeightedSecondNorm theta eps j ≤ K * eps ^ (2 * p + 4) := by
  obtain ⟨thetaMax, K0, e0, htmax, hK0, he0, hinit⟩ := kepReference_small_weight_initial_budget
  refine ⟨thetaMax, max e0 2, htmax, he0.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta A hA p c hc hrec
  have hlim : Tendsto (fun x : ℝ => A * x ^ p * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_assoc, mul_zero] using
      tendsto_const_nhds.mul (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p : ℝ) c hc)
  have hevent : ∀ᶠ x : ℝ in atTop, A * x ^ p * Real.exp (-c * x) ≤ 1 / 4 :=
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono fun _ h => h.le
  obtain ⟨e1, hsmall⟩ := eventually_atTop.mp hevent
  let K := K0 + 16 * (A + 1) ^ 2
  have hK : 0 < K := by dsimp [K]; nlinarith only [hK0, hA, sq_nonneg A]
  refine ⟨K, max (max e0 2) e1, hK, le_max_left _ _, ?_⟩
  intro eps he j hj
  have he0' : e0 ≤ eps := (le_max_left _ _).trans ((le_max_left _ _).trans he)
  have he2 : 2 ≤ eps := (le_max_right _ _).trans ((le_max_left _ _).trans he)
  have he1 : e1 ≤ eps := (le_max_right _ _).trans he
  have heps1 : 1 ≤ eps := by linarith
  have heps0 : 0 ≤ eps := by linarith
  have hp1 : 1 ≤ eps ^ p := one_le_pow₀ heps1
  have hq4 : eps ^ 4 ≤ eps ^ (2 * p + 4) := pow_le_pow_right₀ heps1 (by omega)
  have hq2 : eps ^ (2 * p) ≤ eps ^ (2 * p + 4) := pow_le_pow_right₀ heps1 (by omega)
  let B := K * eps ^ (2 * p + 4)
  have hbase : kepReferenceWeightedSecondNorm theta eps 1 ≤ B := by
    apply ((hinit theta ht.le htheta eps he0').2).trans
    calc
      K0 * eps ^ 4 ≤ K0 * eps ^ (2 * p + 4) := mul_le_mul_of_nonneg_left hq4 hK0
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg heps0 _)
        dsimp [K]
        nlinarith only [sq_nonneg (A + 1)]
  have hbudget : 16 * (A * eps ^ p + 1) ^ 2 ≤ B := by
    have hAp : A * eps ^ p + 1 ≤ (A + 1) * eps ^ p := by nlinarith only [hp1]
    calc
      _ ≤ 16 * ((A + 1) * eps ^ p) ^ 2 := by gcongr
      _ = (16 * (A + 1) ^ 2) * eps ^ (2 * p) := by
        rw [mul_pow, ← pow_mul, Nat.mul_comm p 2]
        ring
      _ ≤ (16 * (A + 1) ^ 2) * eps ^ (2 * p + 4) :=
        mul_le_mul_of_nonneg_left hq2 (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg heps0 _)
        dsimp [K]
        linarith only [hK0]
  have hbound := KEPReferenceScale.uniform_bound_of_recurrence
    (J := fun k => kepReferenceWeightedSecondNorm theta eps (k + 1))
    (A := A * eps ^ p) (B := B) (r := A * eps ^ p * Real.exp (-c * eps))
    (by positivity) (hsmall eps he1)
    (fun k => kepReferenceWeightedSecondNorm_nonneg theta eps (k + 1))
    hbase hbudget (fun k => hrec eps ((le_max_left _ _).trans he) (k + 1) (by omega))
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
  exact hbound k

/-- The actual recurrence alone gives one polynomial scale budget for all layers,
including the nonsmooth exponential base layer. The recurrence is still a premise. -/
theorem kepReference_uniform_scale_of_second_norm_recurrence :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax →
        ∀ A : ℝ, 0 ≤ A → ∀ p : ℕ, ∀ c : ℝ, 0 < c →
          (∀ eps, eps0 ≤ eps → ∀ j : ℕ, 1 ≤ j →
            kepReferenceWeightedSecondNorm theta eps (j + 1) ≤
              A * eps ^ p * (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j)) +
              A * eps ^ p * Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j) →
          ∃ K E : ℝ, 0 < K ∧ eps0 ≤ E ∧
            ∀ eps, E ≤ eps →
              (∀ j : ℕ, 1 ≤ j →
                kepReferenceWeightedSecondNorm theta eps j ≤ K * eps ^ (2 * p + 4)) ∧
              (∀ j : ℕ, ∀ s : ℝ,
                let P : Measure ℝ := (kepReferenceLaw eps j : Measure ℝ)
                let : IsProbabilityMeasure (P.map (fun x => Real.exp s * x)) :=
                  Measure.isProbabilityMeasure_map
                    (measurable_const.mul measurable_id).aemeasurable
                measureHellinger (P.map (fun x => Real.exp s * x)) P ≤
                  K * eps ^ (2 * p + 4) * |s| ^ (2 / 3 : ℝ)) := by
  obtain ⟨tN, eN, htN, heN, hnorm⟩ := kepReference_uniform_second_norm_of_recurrence
  obtain ⟨tS, eS, htS, -, hscale⟩ := kepReference_actual_scale_bound_for_small_weights
  obtain ⟨Kb, hKb, hbase⟩ := kepReferenceLaw_zero_scale_budget
  refine ⟨min tN tS, eN, lt_min htN htS, heN, ?_⟩
  intro theta ht htheta A hA p c hc hrec
  obtain ⟨Kn, En, hKn, heEn, hn⟩ :=
    hnorm theta ht (htheta.trans (min_le_left _ _)) A hA p c hc hrec
  obtain ⟨Ks, hKs, hs⟩ := hscale theta ht (htheta.trans (min_le_right _ _))
  let K := Kn + Kb + Ks * (1 + Kn)
  have hK : 0 < K := by dsimp [K]; positivity
  have hprod : 0 ≤ Ks * (1 + Kn) := by positivity
  have hKnK : Kn ≤ K := by dsimp [K]; linarith only [hKb, hprod]
  have hKbK : Kb ≤ K := by dsimp [K]; linarith only [hKn, hprod]
  have hKsK : Ks * (1 + Kn) ≤ K := by dsimp [K]; linarith only [hKn, hKb]
  refine ⟨K, max En (max eS 2), hK, heEn.trans (le_max_left _ _), ?_⟩
  intro eps he
  have hnE : En ≤ eps := (le_max_left _ _).trans he
  have hsE : eS ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have he2 : 2 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have he1 : 1 ≤ eps := by linarith
  have hp1 : 1 ≤ eps ^ (2 * p + 4) := one_le_pow₀ he1
  constructor
  · intro j hj
    exact (hn eps hnE j hj).trans
      (mul_le_mul_of_nonneg_right hKnK (by positivity))
  · intro j s
    cases j with
    | zero =>
      apply (hbase eps s).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg s) _)
      exact (le_mul_of_one_le_right hKb hp1).trans
        (mul_le_mul_of_nonneg_right hKbK (by positivity))
    | succ j =>
      have hJ := kepReferenceWeightedSecondNorm_nonneg theta eps (j + 1)
      have hsq : Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps (j + 1)) ≤
          1 + kepReferenceWeightedSecondNorm theta eps (j + 1) := by
        have hss := Real.sq_sqrt (by linarith :
          0 ≤ 1 + kepReferenceWeightedSecondNorm theta eps (j + 1))
        have hs0 := Real.sqrt_nonneg (1 + kepReferenceWeightedSecondNorm theta eps (j + 1))
        nlinarith only [hss, hs0, hJ]
      have hcoef : Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps (j + 1)) ≤
          (1 + Kn) * eps ^ (2 * p + 4) := by
        apply hsq.trans
        have hjn := hn eps hnE (j + 1) (by omega)
        nlinarith only [hjn, hp1]
      apply (hs eps hsE (j + 1) (by omega) s).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg s) _)
      calc
        _ ≤ Ks * ((1 + Kn) * eps ^ (2 * p + 4)) :=
          mul_le_mul_of_nonneg_left hcoef hKs.le
        _ = (Ks * (1 + Kn)) * eps ^ (2 * p + 4) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKsK (by positivity)

end

end PGM
