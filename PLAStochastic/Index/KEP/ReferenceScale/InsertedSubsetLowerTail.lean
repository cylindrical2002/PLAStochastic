import PLAStochastic.Index.KEP.ReferenceScale.PartialChernoffPhases

/-!
# Actual lower Chernoff tail for every coordinate subset

Only coordinates inside the bridge pay the quadratic Chernoff phase. The
complete ambient prefix may be arbitrarily long. Two inserted coordinates
cost a fixed factor and the original linear weighted second-norm budget.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kep_clean_subset_negative_phase {n : ℕ} {H A : Finset (Fin n)} (hH : H.card ≤ 2)
    {C tau : ℝ} (_hC : 0 ≤ C) (ht : 0 ≤ tau) (hCt : C * tau ≤ 1 / 4) :
    (∑ i ∈ Finset.univ \ H,
      ((if i ∈ A then -tau else 0) + C * (if i ∈ A then -tau else 0) ^ 2)) ≤
      -(3 * tau / 4) * A.card + 2 * tau := by
  classical
  have hphase : -tau + C * tau ^ 2 ≤ -(3 * tau / 4) := by
    have hh := mul_le_mul_of_nonneg_right hCt ht
    nlinarith only [hh]
  have hsum : (∑ i ∈ Finset.univ \ H,
      ((if i ∈ A then -tau else 0) + C * (if i ∈ A then -tau else 0) ^ 2)) =
      (A \ H).card * (-tau + C * tau ^ 2) := by
    have hp (i : Fin n) :
        ((if i ∈ A then -tau else 0) + C * (if i ∈ A then -tau else 0) ^ 2) =
          if i ∈ A then -tau + C * tau ^ 2 else 0 := by
      split_ifs <;> ring
    simp_rw [hp]
    rw [← sum_filter]
    have hfilter : (Finset.univ \ H).filter (fun i => i ∈ A) = A \ H := by
      ext i
      simp only [mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
      tauto
    rw [hfilter, sum_const, nsmul_eq_mul]
  have hcards : (A \ H).card + (A ∩ H).card = A.card := card_sdiff_add_card_inter A H
  have hinter : (A ∩ H).card ≤ 2 := (Finset.card_le_card Finset.inter_subset_right).trans hH
  have hcardsR : ((A \ H).card : ℝ) + (A ∩ H).card = A.card := by exact_mod_cast hcards
  have hinterR : ((A ∩ H).card : ℝ) ≤ 2 := by exact_mod_cast hinter
  rw [hsum]
  have hh := mul_le_mul_of_nonneg_left hphase (Nat.cast_nonneg (A \ H).card)
  have hh2 := mul_le_mul_of_nonneg_left hinterR (by positivity : 0 ≤ 3 * tau / 4)
  nlinarith only [hh, hh2, hcardsR, ht]

theorem kepReference_inserted_subset_lower_tail :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ A : Finset (Fin n), let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              (∫ _x in {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8}, (1 : ℝ) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) * Real.exp (-c * A.card) := by
  obtain ⟨C, t0, tm, e0, hC, ht0, htm, he0, hmoment⟩ := kepReference_inserted_vector_moment_budget
  refine ⟨tm, e0, htm, he0, ?_⟩
  intro theta ht htheta
  obtain ⟨K, hK, hmb⟩ := hmoment theta ht htheta
  let tau := min (t0 / 4) (min (theta / 16) (1 / (256 * C)))
  have htau : 0 < tau := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htauT : tau ≤ t0 / 4 := min_le_left _ _
  have htauTheta : tau ≤ theta / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have htauC : tau ≤ 1 / (256 * C) := (min_le_right _ _).trans (min_le_right _ _)
  have hCt : C * tau ≤ 1 / 4 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 256 * C)).mp htauC
    nlinarith only [hh]
  refine ⟨K * Real.exp (2 * tau), tau / 2, by positivity, by positivity, ?_⟩
  intro eps he heps j hj n r hr A
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let t : Fin n → ℝ := fun i => if i ∈ A then -tau else 0
  have htime (i : Fin n) : |t i| ≤ min t0 (theta / 4) := by
    dsimp [t]
    split_ifs
    · rw [abs_neg, abs_of_pos htau]
      exact le_min (by linarith) (by linarith)
    · simp only [abs_zero]
      exact le_min ht0.le (by positivity)
  have hm := hmb eps he heps j hj n r hr t htime
  have : ∀ i, IsFiniteMeasure (mu i) := hm.1
  let E := {x : Fin n → ℝ | (∑ i ∈ A, x i) ≤ A.card / 8}
  have hE : MeasurableSet E := measurableSet_le
    (Finset.measurable_sum A (fun i _ => measurable_pi_apply i)) measurable_const
  have htSum (x : Fin n → ℝ) : (∑ i, t i * x i) = -tau * ∑ i ∈ A, x i := by
    dsimp [t]
    simp only [ite_mul, zero_mul, sum_ite, sum_const_zero, add_zero, filter_mem_eq_inter,
      Finset.univ_inter, mul_sum]
  have hpt (x : Fin n → ℝ) (hx : x ∈ E) :
      (0 : ℝ) * (∑ i, x i) ≤ tau * A.card / 8 + ∑ i, t i * x i := by
    rw [zero_mul, htSum]
    have hh := mul_le_mul_of_nonpos_left hx (neg_nonpos.mpr htau.le)
    linarith only [hh]
  have hh := kep_pi_weighted_linear_event_bound mu (t := t) (u := 0)
    (b := tau * A.card / 8) hE hm.2.1 hpt
  have hmoment' := hm.2.2.2
  rw [kep_pi_exp_linear_integral] at hmoment'
  have hphase := kep_clean_subset_negative_phase (kepInsertionPattern_bounds hr).2.1 hC.le htau.le hCt
    (A := A)
  have hs : tau * A.card / 8 +
      (∑ i ∈ Finset.univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2)) ≤
        2 * tau - (tau / 2) * A.card := by
    have hh' : (∑ i ∈ Finset.univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2)) ≤
        -(3 * tau / 4) * A.card + 2 * tau := hphase
    nlinarith only [hh', htau.le, (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card)]
  have hJ := kepReferenceWeightedSecondNorm_nonneg theta eps j
  calc
    _ ≤ Real.exp (tau * A.card / 8) *
        (K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
          Real.exp (∑ i ∈ Finset.univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2))) := by
      simpa only [zero_mul, Real.exp_zero] using
        hh.trans (mul_le_mul_of_nonneg_left hmoment' (Real.exp_pos _).le)
    _ = K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
        Real.exp (tau * A.card / 8 +
          ∑ i ∈ Finset.univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2)) := by
      rw [Real.exp_add]
      ring
    _ ≤ K * (1 + kepReferenceWeightedSecondNorm theta eps j) *
        Real.exp (2 * tau - (tau / 2) * A.card) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hs) (by positivity)
    _ = _ := by
      rw [show 2 * tau - (tau / 2) * (A.card : ℝ) =
        2 * tau + (-(tau / 2) * A.card) by ring, Real.exp_add]
      ring

end

end PGM
