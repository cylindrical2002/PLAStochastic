import PLAStochastic.Affine.Lifetime.InverseErrorMoments
import PLAStochastic.Affine.Moments.Optimal.Slope.Range

/-!
# Almost sure positivity and nonaffinity of actual Brownian paths

The inverse-error law and positive finite lifetime force positive unit-time
fitting errors. Scaling gives the result at every fixed positive horizon.
In particular, the actual Brownian bridge satisfies the nonaffinity assumption
needed by deterministic slope integration.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem anchoredProcessError_unit_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < anchoredProcessError B 1 ω := by
  have h := (identDistrib_anchoredUnitLifetime_inverse_square hB).ae_snd
    (p := fun x : ℝ => 0 < x) measurableSet_Ioi (anchoredUnitLifetime_positive_ae hB)
  filter_upwards [h] with ω hω
  by_contra hn
  have hz : anchoredProcessError B 1 ω = 0 :=
    le_antisymm (le_of_not_gt hn) (anchoredTimeError_nonneg (processPath B ω) 1)
  simp [hz] at hω

theorem optimalProcessError_unit_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < optimalProcessError B 1 ω := by
  have h := (identDistrib_optimalUnitLifetime_inverse_square hB).ae_snd
    (p := fun x : ℝ => 0 < x) measurableSet_Ioi (optimalUnitLifetime_positive_ae hB)
  filter_upwards [h] with ω hω
  by_contra hn
  have hz : optimalProcessError B 1 ω = 0 :=
    le_antisymm (le_of_not_gt hn) (optimalTimeError_nonneg (processPath B ω) 1)
  simp [hz] at hω

theorem anchoredProcessError_positive_ae (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : T ≠ 0) : ∀ᵐ ω ∂μ, 0 < anchoredProcessError B T ω := by
  apply (identDistrib_anchoredProcessError_time hB hT).symm.ae_snd measurableSet_Ioi
  filter_upwards [anchoredProcessError_unit_positive_ae hB] with ω hω
  exact mul_pos (Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hT))) hω

theorem optimalProcessError_positive_ae (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : T ≠ 0) : ∀ᵐ ω ∂μ, 0 < optimalProcessError B T ω := by
  apply (identDistrib_optimalProcessError_time hB hT).symm.ae_snd measurableSet_Ioi
  filter_upwards [optimalProcessError_unit_positive_ae hB] with ω hω
  exact mul_pos (Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hT))) hω

theorem optimalError_bridge_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < optimalError (bridgeUnitPath B ω) := by
  simpa only [optimalError_bridgeUnitPath] using optimalProcessError_unit_positive_ae hB

theorem bridgeUnitPath_nonaffine_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ¬ ∃ a b : ℝ, bridgeUnitPath B ω = a • timePath 1 + b • (1 : Path 1) := by
  filter_upwards [optimalError_bridge_positive_ae hB] with ω hω
  rintro ⟨a, b, hab⟩
  have he : optimalError (bridgeUnitPath B ω) ≤ 0 := by
    have hd := Metric.infDist_le_dist_of_mem (x := bridgeUnitPath B ω)
      (Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩ :
        a • timePath 1 + b • (1 : Path 1) ∈ affineSubspace 1)
    simpa only [optimalError, bestError, affineSubspace, hab, dist_self] using hd
  exact (not_lt_of_ge he) hω

theorem bridge_slopeMinimum_positive_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 < slopeMinimum (bridgeUnitPath B ω) := by
  filter_upwards [optimalError_bridge_positive_ae hB] with ω hω
  rw [slopeMinimum_eq_two_optimal]
  positivity

end BrownianAffine
