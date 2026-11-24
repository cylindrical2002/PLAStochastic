import PLAStochastic.Index.KEP.ReferenceScale.PartialChernoffPhases

/-!
# Actual weighted partial-sum deviations after at most two insertions

Every fixed coordinate subset and either Chernoff sign is covered. For a
prefix of at most seventeen tolerance units the original inserted product
measure has exponentially small deviation mass, uniformly over the layer,
subset, sign and insertion locations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set

theorem kep_partial_tilt_sum {n : ℕ} (A : Finset (Fin n)) (u v : ℝ) (x : Fin n → ℝ) :
    (∑ i, (u + if i ∈ A then v else 0) * x i) =
      u * (∑ i, x i) + v * (∑ i ∈ A, x i) := by
  simp_rw [add_mul, ite_mul, zero_mul]
  rw [sum_add_distrib, ← mul_sum, sum_ite, filter_mem_eq_inter, Finset.univ_inter]
  simp only [sum_const_zero, add_zero, mul_sum]

theorem kep_partial_tilt_parameter_sum {n : ℕ} (A : Finset (Fin n)) (u v : ℝ) :
    (∑ i, (u + if i ∈ A then v else 0)) = u * n + v * A.card := by
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_univ, Fintype.card_fin,
    sum_ite, filter_mem_eq_inter, Finset.univ_inter]
  simp only [sum_const, nsmul_eq_mul]
  ring

theorem kepReference_inserted_partial_deviations :
    ∃ thetaMax eps0 : ℝ, 0 < thetaMax ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c u0 : ℝ,
        0 < K ∧ 0 < c ∧ 0 < u0 ∧ u0 ≤ theta / 4 ∧
        ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j, ∀ hj : 1 ≤ j, ∀ n : ℕ, (n : ℝ) ≤ 17 * eps →
            ∀ r : Fin n → ℕ, (∑ i, r i) ≤ 2 → ∀ A : Finset (Fin n),
              ∀ sigma u : ℝ, |sigma| ≤ 1 → 0 ≤ u → u ≤ u0 →
              let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
              (∫ x in {x | eps ≤ sigma * ((∑ i ∈ A, x i) - A.card)},
                Real.exp (u * ∑ i, x i) ∂Measure.pi mu) ≤
                  K * (1 + kepReferenceWeightedSecondNorm theta eps j) * Real.exp (-c * eps) := by
  obtain ⟨C, t0, tm, e0, hC, ht0, htm, he0, hbudget⟩ := kepReference_inserted_vector_moment_budget
  refine ⟨tm, max e0 1, htm, he0.trans (le_max_left _ _), ?_⟩
  intro theta ht htheta
  obtain ⟨K, hK, hb⟩ := hbudget theta ht htheta
  let tau := min (t0 / 4) (min (theta / 16) (1 / (1024 * C)))
  have htau : 0 < tau := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have htauT : tau ≤ t0 / 4 := min_le_left _ _
  have htauTheta : tau ≤ theta / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have htauC : C * tau ≤ 1 / 1024 := by
    have hh : tau ≤ 1 / (1024 * C) := (min_le_right _ _).trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by positivity : 0 < 1024 * C)).mp hh
    linarith
  refine ⟨K * Real.exp (2 * tau), tau / 2, tau / 256, by positivity, by positivity,
    by positivity, by linarith, ?_⟩
  intro eps he heps j hj n hn r hr A sigma u hsigma hu0 hu
  dsimp only
  let mu := fun i => kepReferenceInsertionMeasure heps hj (r i)
  let J := kepReferenceWeightedSecondNorm theta eps j
  let t := fun i : Fin n => u + if i ∈ A then sigma * tau else 0
  let E := {x : Fin n → ℝ | eps ≤ sigma * ((∑ i ∈ A, x i) - A.card)}
  have hsig : |sigma * tau| ≤ tau := by
    rw [abs_mul, abs_of_pos htau]
    exact (mul_le_mul_of_nonneg_right hsigma htau.le).trans_eq (one_mul tau)
  have hmin (i) : -tau ≤ t i := by
    dsimp [t]
    split
    · have hh := (abs_le.mp hsig).1
      linarith
    · linarith
  have habs (i) : |t i| ≤ u + tau := by
    dsimp [t]
    split
    · exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hu0]; linarith)
    · rw [add_zero, abs_of_nonneg hu0]
      linarith
  have hcap (i) : |t i| ≤ min t0 (theta / 4) := (habs i).trans (le_min (by linarith) (by linarith))
  have hp := hb eps ((le_max_left _ _).trans he) heps j hj n r hr t hcap
  have : ∀ i, IsFiniteMeasure (mu i) := hp.1
  have hP : Measurable (fun x : Fin n → ℝ => ∑ i ∈ A, x i) :=
    Finset.measurable_sum A (fun i _ => measurable_pi_apply i)
  have hE : MeasurableSet E := measurableSet_le measurable_const ((hP.sub measurable_const).const_mul sigma)
  have htail := kep_pi_weighted_linear_event_bound mu hE u (-tau * eps - sigma * tau * A.card) t hp.2.1
    (fun x hx => by
      dsimp only [E, mem_ofPred_eq] at hx
      rw [kep_partial_tilt_sum]
      nlinarith [mul_le_mul_of_nonneg_left hx htau.le])
  rw [← kep_pi_exp_linear_integral mu t] at htail
  have hbound := htail.trans (mul_le_mul_of_nonneg_left hp.2.2.2 (Real.exp_pos _).le)
  have hphase := kep_clean_vector_phase_bound (kepInsertedCoordinates r)
    (kepInsertionPattern_bounds hr).2.1 hC.le htau.le hu0 t hmin habs
  rw [kep_partial_tilt_parameter_sum] at hphase
  have heps1 : 1 ≤ eps := (le_max_right _ _).trans he
  have hcost := kep_short_chernoff_weight_cost (by linarith : 0 ≤ eps) hC.le htau htauC hu0 hu hn
  have hphase' : -tau * eps - sigma * tau * A.card +
      (∑ i ∈ Finset.univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2)) ≤
        2 * tau - tau * eps / 2 := by
    linarith only [hphase, hcost, mul_nonneg htau.le (by linarith : 0 ≤ eps)]
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  apply hbound.trans
  calc
    _ = K * (1 + J) * Real.exp (-tau * eps - sigma * tau * A.card +
        (∑ i ∈ Finset.univ \ kepInsertedCoordinates r, (t i + C * (t i) ^ 2))) := by
      rw [Real.exp_add]
      ring
    _ ≤ K * (1 + J) * Real.exp (2 * tau - tau * eps / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase') (by positivity)
    _ = _ := by
      rw [show 2 * tau - tau * eps / 2 = 2 * tau + (-(tau / 2) * eps) by ring, Real.exp_add]
      ring

end

end PGM
