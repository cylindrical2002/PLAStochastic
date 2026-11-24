import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import PLAStochastic.Affine.Lifetime.ToleranceMoments

/-!
# WP5: the actual Brownian lifetime law

The lifetime is finite almost surely before passing from its extended value to
its real representative. Tolerance scaling identifies closed fitting-error
sublevels with closed tails of the unit lifetime law, including time zero.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Set
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Continuous fitting-error sublevels are exactly the scaled closed lifetime tails. -/
theorem brownian_error_le_eq_lifetime_tail (hB : IsBrownianReal B μ)
    (T : ℝ≥0) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | optimalProcessError B T ω ≤ a} =
      (μ.map (optimalUnitLifetime B)).real (Ici ((T : ℝ) / a ^ 2)) := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable (aemeasurable_optimalUnitLifetime hB)
      measurableSet_Ici]
  apply congrArg ENNReal.toReal
  calc
    μ {ω | optimalProcessError B T ω ≤ a} =
        μ {ω | (T : ℝ) ≤ (optimalProcessLifetime B a ω).toReal} := by
      apply measure_congr
      filter_upwards [optimalProcessLifetime_tolerance_ae_ne_top hB ha] with ω hfin
      apply propext
      change (optimalProcessError B T ω ≤ a) ↔
        (T : ℝ) ≤ (optimalProcessLifetime B a ω).toReal
      rw [← optimalProcessLifetime_closed_tails B ha.le ω T]
      simpa only [ENNReal.coe_toReal] using
        (ENNReal.toReal_le_toReal (a := (T : ℝ≥0∞)) (by simp) hfin).symm
    _ = μ {ω | (T : ℝ) ≤ a ^ 2 * optimalUnitLifetime B ω} :=
      (identDistrib_optimalLifetime_toReal_tolerance hB ha).measure_mem_eq measurableSet_Ici
    _ = μ (optimalUnitLifetime B ⁻¹' Ici ((T : ℝ) / a ^ 2)) := by
      congr 1
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, mem_Ici, div_le_iff₀ (sq_pos_of_pos ha)]
      rw [mul_comm]

/-- The actual unit lifetime induces a probability law supported on nonnegative reals. -/
theorem brownian_lifetime_law (hB : IsBrownianReal B μ) :
    IsProbabilityMeasure (μ.map (optimalUnitLifetime B)) ∧
      (μ.map (optimalUnitLifetime B)) (Iio 0) = 0 := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨Measure.isProbabilityMeasure_map (aemeasurable_optimalUnitLifetime hB), ?_⟩
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_optimalUnitLifetime hB)
    measurableSet_Iio]
  have he : optimalUnitLifetime B ⁻¹' Iio 0 = ∅ := by
    ext ω
    simp only [mem_preimage, mem_Iio, mem_empty_iff_false, iff_false]
    exact not_lt_of_ge (optimalUnitLifetime_nonnegative B ω)
  rw [he, measure_empty]

/-- The lifetime law has a finite exponential moment at a strictly positive rate. -/
theorem brownian_lifetime_exp_moment (hB : IsBrownianReal B μ) :
    ∃ θ E : ℝ, 0 < θ ∧
      (∫⁻ t, ENNReal.ofReal (Real.exp (θ * t)) ∂μ.map (optimalUnitLifetime B)) ≤
        ENNReal.ofReal E := by
  obtain ⟨θ, hθ, hint⟩ := optimalUnitLifetime_exp_neighborhood hB
  have hi := hint θ (by rw [abs_of_pos hθ])
  refine ⟨θ, ∫ ω, Real.exp (θ * optimalUnitLifetime B ω) ∂μ, hθ, ?_⟩
  rw [lintegral_map' (by fun_prop) (aemeasurable_optimalUnitLifetime hB)]
  exact le_of_eq (ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun _ => Real.exp_nonneg _)).symm

end

end PGM
