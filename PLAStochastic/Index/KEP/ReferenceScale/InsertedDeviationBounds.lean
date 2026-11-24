import PLAStochastic.Index.KEP.ReferenceScale.InsertionProductBudget

/-!
# Actual weighted proportion deviations after at most two Mellin insertions

Both Chernoff tails have an exponential rate independent of tolerance and
layer. The insertion cost remains linear in the actual weighted second norm.
The number of clean coordinates is kept in the exponent until the final
two-coordinate loss is paid by a fixed constant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset

theorem kep_inserted_chernoff_phases {C tau u : ℝ} (hC : 0 ≤ C) (htau : 0 < tau)
    (hCt : C * tau ≤ 1 / 256) (hu0 : 0 ≤ u) (hu : u ≤ tau / 64)
    {n h : ℕ} (hn : 2 ≤ n) (hh : h ≤ 2) (hhn : h ≤ n) :
    -tau * (7 * n / 6) + ((n - h : ℕ) : ℝ) * ((u + tau) + C * (u + tau) ^ 2) ≤
      -tau * n / 8 ∧
    tau * (3 * n / 4) + ((n - h : ℕ) : ℝ) * ((u - tau) + C * (u - tau) ^ 2) ≤
      2 * tau - tau * n / 8 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hh2 : (h : ℝ) ≤ 2 := by exact_mod_cast hh
  have hnm : ((n - h : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n h
  have hnmLower : (n : ℝ) - 2 ≤ ((n - h : ℕ) : ℝ) := by
    rw [Nat.cast_sub hhn]
    linarith
  have hsqU : (u + tau) ^ 2 ≤ (2 * tau) ^ 2 := by nlinarith
  have hsqL : (u - tau) ^ 2 ≤ tau ^ 2 := by nlinarith
  have hcurv := mul_le_mul_of_nonneg_right hCt htau.le
  have hcurvU := mul_le_mul_of_nonneg_left hsqU hC
  have hcurvL := mul_le_mul_of_nonneg_left hsqL hC
  have haU : (u + tau) + C * (u + tau) ^ 2 ≤ 33 * tau / 32 := by
    nlinarith only [hcurv, hcurvU, hu]
  have haU0 : 0 ≤ (u + tau) + C * (u + tau) ^ 2 := by positivity
  have haL : (u - tau) + C * (u - tau) ^ 2 ≤ -7 * tau / 8 := by
    nlinarith only [hcurv, hcurvL, hu, htau.le]
  constructor
  · have h1 := mul_le_mul_of_nonneg_right hnm haU0
    have h2 := mul_le_mul_of_nonneg_left haU hn0
    nlinarith only [h1, h2, mul_nonneg htau.le hn0]
  · have haL0 : (u - tau) + C * (u - tau) ^ 2 ≤ 0 := by linarith
    have h1 := mul_le_mul_of_nonpos_right hnmLower haL0
    have h2 := mul_le_mul_of_nonneg_left haL (by linarith : (0 : ℝ) ≤ (n : ℝ) - 2)
    nlinarith only [h1, h2, htau.le]

theorem kepReference_inserted_proportion_deviations :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 4 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, 2 ≤ n → ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 →
            ∀ u : ℝ, 0 ≤ u → u ≤ u0 →
            let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
            (∫ x in {x | 7 * n / 6 ≤ ∑ i, x i}, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) +
              (∫ x in {x | (∑ i, x i) ≤ 3 * n / 4}, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                K * (1 + kepReferenceWeightedSecondNorm theta eps j) * Real.exp (-c * n) := by
  obtain ⟨C, t0, tm, e0, hC, ht0, htm, he0, hbudget⟩ := kepReference_inserted_exponential_budget
  refine ⟨tm, e0, htm, he0, ?_⟩
  intro theta ht htheta
  obtain ⟨K, hK, hb⟩ := hbudget theta ht htheta
  let tau := min (t0 / 4) (min (theta / 16) (1 / (256 * C)))
  have htau : 0 < tau := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htauT : tau ≤ t0 / 4 := min_le_left _ _
  have htauTheta : tau ≤ theta / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have htauC : C * tau ≤ 1 / 256 := by
    have hh : tau ≤ 1 / (256 * C) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 256 * C)).mp hh
    linarith
  refine ⟨2 * K * Real.exp (2 * tau), tau / 8, tau / 64, by positivity, by positivity,
    by positivity, by linarith, ?_⟩
  intro eps he heps j hj n hn r hr u hu0 hu
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let J := kepReferenceWeightedSecondNorm theta eps j
  let H := kepInsertedCoordinates r
  have hH : H.card ≤ n := by
    have hh := card_le_card (filter_subset (fun i => r i ≠ 0) (univ : Finset (Fin n)))
    simpa only [H, kepInsertedCoordinates, card_univ, Fintype.card_fin] using hh
  have hcapU : |u + tau| ≤ min t0 (theta / 4) := by
    rw [abs_of_nonneg (by positivity)]
    exact le_min (by linarith) (by linarith)
  have hcapL : |u - tau| ≤ min t0 (theta / 4) := by
    rw [abs_of_nonpos (by linarith : u - tau ≤ 0)]
    exact le_min (by linarith) (by linarith)
  have hp := hb eps he heps j hj n r hr (u + tau) hcapU
  have hm := hb eps he heps j hj n r hr (u - tau) hcapL
  have : ∀ i, IsFiniteMeasure (mu i) := hp.1
  have hupper := kep_pi_weighted_upper_tail mu u (7 * n / 6) htau.le hp.2.1
  have hlower := kep_pi_weighted_lower_tail mu u (3 * n / 4) htau.le hm.2.1
  rw [← kep_pi_exp_sum_integral mu (u + tau)] at hupper
  rw [← kep_pi_exp_sum_integral mu (u - tau)] at hlower
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hphases := kep_inserted_chernoff_phases hC.le htau htauC hu0 hu hn
    (kepInsertionPattern_bounds hr).2.1 hH
  have huBound := hupper.trans (mul_le_mul_of_nonneg_left hp.2.2.2 (Real.exp_pos _).le)
  have hlBound := hlower.trans (mul_le_mul_of_nonneg_left hm.2.2.2 (Real.exp_pos _).le)
  have hU : (∫ x in {x | 7 * n / 6 ≤ ∑ i, x i}, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
      K * (1 + J) * Real.exp (2 * tau) * Real.exp (-tau * n / 8) := by
    apply huBound.trans
    calc
      _ = K * (1 + J) * Real.exp (-tau * (7 * n / 6) +
          ((n - H.card : ℕ) : ℝ) * ((u + tau) + C * (u + tau) ^ 2)) := by
        rw [Real.exp_add]
        ring
      _ ≤ K * (1 + J) * Real.exp (2 * tau - tau * n / 8) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hphases.1.trans (by linarith)))
          (by positivity)
      _ = _ := by
        rw [show 2 * tau - tau * (n : ℝ) / 8 = 2 * tau + (-tau * n / 8) by ring, Real.exp_add]
        ring
  have hL : (∫ x in {x | (∑ i, x i) ≤ 3 * n / 4}, Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
      K * (1 + J) * Real.exp (2 * tau) * Real.exp (-tau * n / 8) := by
    apply hlBound.trans
    calc
      _ = K * (1 + J) * Real.exp (tau * (3 * n / 4) +
          ((n - H.card : ℕ) : ℝ) * ((u - tau) + C * (u - tau) ^ 2)) := by
        rw [Real.exp_add]
        ring
      _ ≤ K * (1 + J) * Real.exp (2 * tau - tau * n / 8) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphases.2) (by positivity)
      _ = _ := by
        rw [show 2 * tau - tau * (n : ℝ) / 8 = 2 * tau + (-tau * n / 8) by ring, Real.exp_add]
        ring
  have hh := add_le_add hU hL
  convert hh using 1 <;> first
  | rfl
  | (rw [show -(tau / 8) * (n : ℝ) = -tau * n / 8 by ring]; ring)

end

end PGM
