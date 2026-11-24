import PLAStochastic.Index.KEP.ReferenceScale.ActualOutputRecurrence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Layer-uniform norm and scale regularity of the actual reference orbit

The true output recurrence and the actual first-layer initial budget close a
fixed polynomial invariant. The measure-level two-thirds scale estimate is
therefore unconditional, including the nonsmooth exponential base layer.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem kepReference_close_fixed_weight_recurrence (theta K0 e0 A c er : ℝ)
    (hK0 : 0 ≤ K0) (hA : 0 ≤ A) (hc : 0 < c)
    (hinit : ∀ eps, e0 ≤ eps → kepReferenceWeightedSecondNorm theta eps 1 ≤ K0 * eps ^ 4)
    (hrec : ∀ eps, er ≤ eps → ∀ j : ℕ, 1 ≤ j →
      kepReferenceWeightedSecondNorm theta eps (j + 1) ≤
        A * eps ^ 47 * (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j)) +
        A * eps ^ 47 * Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j) :
    ∃ K E : ℝ, 0 < K ∧ max e0 er ≤ E ∧
      ∀ eps, E ≤ eps → ∀ j : ℕ, 1 ≤ j →
        kepReferenceWeightedSecondNorm theta eps j ≤ K * eps ^ 98 := by
  have hlim : Tendsto (fun x : ℝ => A * x ^ 47 * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, mul_assoc, mul_zero] using
      (tendsto_const_nhds (x := A)).mul
        (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((47 : ℕ) : ℝ) c hc)
  have hevent : ∀ᶠ x : ℝ in atTop, A * x ^ 47 * Real.exp (-c * x) ≤ 1 / 4 :=
    (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))).mono fun _ h => h.le
  obtain ⟨e1, hsmall⟩ := eventually_atTop.mp hevent
  let K := K0 + 16 * (A + 1) ^ 2
  have hK : 0 < K := by dsimp [K]; nlinarith only [hK0, hA, sq_nonneg A]
  refine ⟨K, max (max e0 er) (max e1 2), hK, le_max_left _ _, ?_⟩
  intro eps he j hj
  have he0 : e0 ≤ eps := (le_max_left _ _).trans ((le_max_left _ _).trans he)
  have her : er ≤ eps := (le_max_right _ _).trans ((le_max_left _ _).trans he)
  have he1 : e1 ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have he2 : 2 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have heps1 : 1 ≤ eps := by linarith
  have heps0 : 0 ≤ eps := by linarith
  have hp1 : 1 ≤ eps ^ 47 := one_le_pow₀ heps1
  have hq4 : eps ^ 4 ≤ eps ^ 98 := pow_le_pow_right₀ heps1 (by omega)
  have hq94 : eps ^ 94 ≤ eps ^ 98 := pow_le_pow_right₀ heps1 (by omega)
  let B := K * eps ^ 98
  have hbase : kepReferenceWeightedSecondNorm theta eps 1 ≤ B := by
    apply (hinit eps he0).trans
    calc
      _ ≤ K0 * eps ^ 98 := mul_le_mul_of_nonneg_left hq4 hK0
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        nlinarith only [sq_nonneg (A + 1)]
  have hbudget : 16 * (A * eps ^ 47 + 1) ^ 2 ≤ B := by
    have hAp : A * eps ^ 47 + 1 ≤ (A + 1) * eps ^ 47 := by nlinarith only [hp1]
    calc
      _ ≤ 16 * ((A + 1) * eps ^ 47) ^ 2 := by gcongr
      _ = (16 * (A + 1) ^ 2) * eps ^ 94 := by ring
      _ ≤ (16 * (A + 1) ^ 2) * eps ^ 98 := mul_le_mul_of_nonneg_left hq94 (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        linarith only [hK0]
  have hbound := KEPReferenceScale.uniform_bound_of_recurrence
    (J := fun k => kepReferenceWeightedSecondNorm theta eps (k + 1))
    (A := A * eps ^ 47) (B := B) (r := A * eps ^ 47 * Real.exp (-c * eps))
    (by positivity) (hsmall eps he1)
    (fun k => kepReferenceWeightedSecondNorm_nonneg theta eps (k + 1))
    hbase hbudget (fun k => hrec eps her (k + 1) (by omega))
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = k + 1 := ⟨j - 1, by omega⟩
  exact hbound k

theorem kepReference_uniform_second_norm_and_scale :
    ∃ thetaMax : ℝ, 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K E : ℝ,
        0 < K ∧ kepReferenceClassicalThreshold ≤ E ∧
        ∀ eps, E ≤ eps →
          (∀ j : ℕ, 1 ≤ j → kepReferenceWeightedSecondNorm theta eps j ≤ K * eps ^ 98) ∧
          (∀ j : ℕ, ∀ s : ℝ,
            let P : Measure ℝ := (kepReferenceLaw eps j : Measure ℝ)
            let : IsProbabilityMeasure (P.map (fun x => Real.exp s * x)) :=
              Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
            measureHellinger (P.map (fun x => Real.exp s * x)) P ≤
              K * eps ^ 98 * |s| ^ (2 / 3 : ℝ)) := by
  obtain ⟨tr, htr, hrec⟩ := kepReference_actual_weighted_second_recurrence
  obtain ⟨ti, K0, ei, hti, hK0, hei, hinitial⟩ := kepReference_small_weight_initial_budget
  obtain ⟨ts, es, hts, -, hscale⟩ := kepReference_actual_scale_bound_for_small_weights
  obtain ⟨Kb, hKb, hbase⟩ := kepReferenceLaw_zero_scale_budget
  refine ⟨min tr (min ti ts), lt_min htr (lt_min hti hts), ?_⟩
  intro theta ht htmax
  have htr' : theta ≤ tr := htmax.trans (min_le_left _ _)
  have hti' : theta ≤ ti := htmax.trans ((min_le_right tr _).trans (min_le_left ti _))
  have hts' : theta ≤ ts := htmax.trans ((min_le_right tr _).trans (min_le_right ti _))
  obtain ⟨A, c, er, hA, hc, _her, hr⟩ := hrec theta ht htr'
  obtain ⟨Kn, En, hKn, heEn, hn⟩ := kepReference_close_fixed_weight_recurrence theta K0 ei A c er
    hK0 hA.le hc (fun eps he => (hinitial theta ht.le hti' eps he).2) hr
  obtain ⟨Ks, hKs, hs⟩ := hscale theta ht hts'
  let K := Kn + Kb + Ks * (1 + Kn)
  have hK : 0 < K := by dsimp [K]; positivity
  have hprod : 0 ≤ Ks * (1 + Kn) := by positivity
  have hKnK : Kn ≤ K := by dsimp [K]; linarith only [hKb, hprod]
  have hKbK : Kb ≤ K := by dsimp [K]; linarith only [hKn, hprod]
  have hKsK : Ks * (1 + Kn) ≤ K := by dsimp [K]; linarith only [hKn, hKb]
  refine ⟨K, max En (max es 2), hK,
    hei.trans ((le_max_left _ _).trans (heEn.trans (le_max_left _ _))), ?_⟩
  intro eps he
  have hnE : En ≤ eps := (le_max_left _ _).trans he
  have hsE : es ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have he2 : 2 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have he1 : 1 ≤ eps := by linarith
  have hp1 : 1 ≤ eps ^ 98 := one_le_pow₀ he1
  constructor
  · intro j hj
    exact (hn eps hnE j hj).trans (mul_le_mul_of_nonneg_right hKnK (by positivity))
  · intro j s
    cases j with
    | zero =>
      apply (hbase eps s).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg s) _)
      exact (le_mul_of_one_le_right hKb hp1).trans (mul_le_mul_of_nonneg_right hKbK (by positivity))
    | succ j =>
      have hJ := kepReferenceWeightedSecondNorm_nonneg theta eps (j + 1)
      have hsq : Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps (j + 1)) ≤
          1 + kepReferenceWeightedSecondNorm theta eps (j + 1) := by
        have hss := Real.sq_sqrt (by linarith : 0 ≤ 1 + kepReferenceWeightedSecondNorm theta eps (j + 1))
        have hs0 := Real.sqrt_nonneg (1 + kepReferenceWeightedSecondNorm theta eps (j + 1))
        nlinarith only [hss, hs0, hJ]
      have hcoef : Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps (j + 1)) ≤ (1 + Kn) * eps ^ 98 := by
        apply hsq.trans
        have hjn := hn eps hnE (j + 1) (by omega)
        nlinarith only [hjn, hp1]
      apply (hs eps hsE (j + 1) (by omega) s).trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (abs_nonneg s) _)
      calc
        _ ≤ Ks * ((1 + Kn) * eps ^ 98) := mul_le_mul_of_nonneg_left hcoef hKs.le
        _ = (Ks * (1 + Kn)) * eps ^ 98 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hKsK (by positivity)

end

end PGM
