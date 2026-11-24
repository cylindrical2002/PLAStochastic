import PLAStochastic.Index.KEP.ReferenceScale.CleanMomentBudget

/-!
# Uniform small fixed exponential moments of the true reference laws

The actual orbit has mean one and positive support. Its proved centered
cumulant budget provides a common positive interval on which all raw
exponential moments are at most two.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem kepReference_uniform_small_exponential_moment :
    ∃ theta E : ℝ, 0 < theta ∧ ∀ eps, E ≤ eps → ∀ j : ℕ,
      (∀ᵐ z ∂(kepReferenceLaw eps j : Measure ℝ), 0 ≤ z) ∧
      (∫ z, z ∂(kepReferenceLaw eps j : Measure ℝ)) = 1 ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ theta →
        Integrable (fun z => Real.exp (t * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
          ∫ z, Real.exp (t * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 2 := by
  obtain ⟨C, t0, e0, hC, ht0, hmgf⟩ := kepReference_uniform_two_sided_mgf
  obtain ⟨D, a, vl, vu, e1, _, ha, hvl, _, hreg⟩ := kepReferenceLaw_regular
  let theta := min t0 (min 1 C⁻¹) / 4
  have htheta : 0 < theta := div_pos (lt_min ht0 (lt_min zero_lt_one (inv_pos.mpr hC))) (by norm_num)
  refine ⟨theta, max e0 e1, htheta, ?_⟩
  intro eps he j
  have hnu := hreg eps ((le_max_right _ _).trans he) j
  refine ⟨?_, hnu.mean, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hnu.momClass ha hvl).pos] with z hz
    exact (not_le.mp hz).le
  · intro t ht hbound
    have htheta0 : 0 ≤ theta := htheta.le
    have htheta1 : theta ≤ 1 / 4 := by dsimp [theta]; gcongr; exact (min_le_right _ _).trans (min_le_left _ _)
    have hthetaC : theta ≤ C⁻¹ / 4 := by
      dsimp [theta]; gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
    have hthetaT : theta ≤ t0 := by
      have hmin : min t0 (min 1 C⁻¹) ≤ t0 := min_le_left _ _
      dsimp [theta]
      linarith
    obtain ⟨hi, hb⟩ := hmgf eps ((le_max_left _ _).trans he) j t
      (by rw [abs_of_nonneg ht]; exact hbound.trans hthetaT)
    refine ⟨hi, hb.trans ?_⟩
    have hCt : C * t ≤ 1 / 4 := by
      have h := mul_le_mul_of_nonneg_left (hbound.trans hthetaC) hC.le
      have heq : C * (C⁻¹ / 4) = 1 / 4 := by
        rw [div_eq_mul_inv, ← mul_assoc, mul_inv_cancel₀ hC.ne']
        norm_num
      rwa [heq] at h
    have hexponent : t + C * t ^ 2 ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_right hCt ht
      nlinarith
    calc
      _ ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr hexponent
      _ ≤ 1 / (1 - 1 / 2) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 2 := by norm_num

end

end PGM
