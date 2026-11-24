import PLAStochastic.Affine.Moments.Optimal.Survival.Image.SmoothSeries
import PLAStochastic.Affine.Moments.Optimal.Survival.ImageSeries
import PLAStochastic.Brownian.Construction.ContinuousVersion
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Exponential decay of all jets of the actual optimal lifetime survival law -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ContDiff

namespace BrownianAffine

theorem optimalImageSeries_nonneg (t : ℝ) : 0 ≤ optimalImageSeries t := by
  rw [optimalImageSeries_eq_measureReal isBrownianReal_canonicalBrownian]
  exact measureReal_nonneg

theorem antitone_optimalImageSeries : Antitone optimalImageSeries := by
  intro s t hst
  rw [optimalImageSeries_eq_measureReal isBrownianReal_canonicalBrownian,
    optimalImageSeries_eq_measureReal isBrownianReal_canonicalBrownian]
  exact measureReal_mono (fun _ h => hst.trans_lt h)

/-- The actual exponential moment pays the value bound without a spectral assumption. -/
theorem optimalImageSeries_exponential_bound :
    ∃ A ρ : ℝ, 0 ≤ A ∧ 0 < ρ ∧ ∀ t : ℝ, |optimalImageSeries t| ≤ A * Real.exp (-ρ * t) := by
  obtain ⟨ρ, hρ, hi⟩ := optimalUnitLifetime_exp_neighborhood isBrownianReal_canonicalBrownian
  have hint := hi ρ (by rw [abs_of_pos hρ])
  let A : ℝ := ∫ w, Real.exp (ρ * optimalUnitLifetime canonicalBrownian w) ∂canonicalPreBrownianMeasure
  refine ⟨A, ρ, integral_nonneg (fun _ => Real.exp_nonneg _), hρ, fun t => ?_⟩
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun _ => Real.exp_nonneg _) hint (Real.exp (ρ * t))
  have hsurv : Real.exp (ρ * t) * optimalImageSeries t ≤ A := by
    rw [optimalImageSeries_eq_measureReal isBrownianReal_canonicalBrownian]
    exact (mul_le_mul_of_nonneg_left
      (measureReal_mono (fun w hw => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hw.le hρ.le)))
      (Real.exp_nonneg _)).trans hmark
  rw [abs_of_nonneg (optimalImageSeries_nonneg t)]
  calc
    _ ≤ A / Real.exp (ρ * t) := (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using hsurv)
    _ = A * Real.exp (-ρ * t) := by
      rw [show -ρ * t = -(ρ * t) by ring, Real.exp_neg]
      rfl

/-- Every fixed jet retains a strictly positive exponential rate. -/
theorem iteratedDeriv_optimalImageSeries_exponential_bound (r : ℕ) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ 0 < ρ ∧ ∀ t : ℝ, 1 ≤ t →
      |iteratedDeriv r optimalImageSeries t| ≤ A * Real.exp (-ρ * t) := by
  induction r with
  | zero =>
    obtain ⟨A, ρ, hA, hρ, hb⟩ := optimalImageSeries_exponential_bound
    exact ⟨A, ρ, hA, hρ, fun t _ => by simpa only [iteratedDeriv_zero] using hb t⟩
  | succ r ih =>
    obtain ⟨A, ρ, hA, hρ, ha⟩ := ih
    obtain ⟨B, hB, hb⟩ := iteratedDeriv_optimalImageSeries_succ_polynomial_bound (r + 1)
    have hf : ContDiff ℝ ∞ (iteratedDeriv r optimalImageSeries) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv r contDiff_optimalImageSeries
    have hsecond : ∀ t : ℝ, 1 ≤ t →
        |iteratedDeriv 2 (iteratedDeriv r optimalImageSeries) t| ≤ B * t ^ 3 := by
      intro t ht
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Real.norm_eq_abs] using hb t ht
    obtain ⟨D, hD, hd⟩ := Real.exists_exponential_deriv_bound_of_polynomial_second_deriv
      hf hA hB hρ ha hsecond
    refine ⟨D, ρ / 4, hD, by positivity, ?_⟩
    simpa only [iteratedDeriv_succ] using hd

/-- The compact interval near zero can be absorbed into the same fixed-order envelope. -/
theorem iteratedDeriv_optimalImageSeries_exponential_bound_nonneg (r : ℕ) :
    ∃ A ρ : ℝ, 0 ≤ A ∧ 0 < ρ ∧ ∀ t : ℝ, 0 ≤ t →
      |iteratedDeriv r optimalImageSeries t| ≤ A * Real.exp (-ρ * t) := by
  obtain ⟨A, ρ, hA, hρ, hb⟩ := iteratedDeriv_optimalImageSeries_exponential_bound r
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    ((contDiff_optimalImageSeries).continuous_iteratedDeriv r (by
      exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤))).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  refine ⟨A + C * Real.exp ρ, ρ, by positivity, hρ, fun t ht => ?_⟩
  by_cases ht1 : 1 ≤ t
  · exact (hb t ht1).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right (mul_nonneg hC0 (Real.exp_nonneg _))) (Real.exp_nonneg _))
  · have hnorm : |iteratedDeriv r optimalImageSeries t| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC t ⟨ht, le_of_not_ge ht1⟩
    have he : 1 ≤ Real.exp (ρ - ρ * t) := Real.one_le_exp_iff.mpr (by nlinarith [le_of_not_ge ht1])
    calc
      _ ≤ C := hnorm
      _ = C * 1 := (mul_one C).symm
      _ ≤ C * Real.exp (ρ - ρ * t) := mul_le_mul_of_nonneg_left he hC0
      _ = (C * Real.exp ρ) * Real.exp (-ρ * t) := by rw [sub_eq_add_neg, Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)

end BrownianAffine
