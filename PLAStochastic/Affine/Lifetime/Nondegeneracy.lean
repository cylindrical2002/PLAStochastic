import PLAStochastic.Affine.Lifetime.BrownianProcess
import PLAStochastic.Affine.Error.Unbounded

/-!
# Nonconstant Brownian approximation lifetimes

Positivity and the unbounded support of each fixed-time fitting error rule out
every constant lifetime, including infinity. A Brownian small-ball theorem is
not an assumption of this proof.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem anchoredProcessLifetime_not_ae_constant (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) (c : ℝ≥0∞) :
    ¬ anchoredProcessLifetime B ε =ᵐ[μ] fun _ => c := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  intro hconst
  have hc : 0 < c := by
    obtain ⟨ω, hω, hp⟩ := (hconst.and (anchoredProcessLifetime_pos_ae hB hε)).exists
    simpa only [hω] using hp
  obtain ⟨t, ht, htc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have ht₀ : t ≠ 0 := by intro hz; simp [hz] at ht
  apply anchoredProcessError_not_bounded hB ht₀ ε
  filter_upwards [hconst, anchoredProcessLifetime_closed_tails hB hε.le] with ω hω htail
  apply (htail t).mp
  rw [hω]
  exact htc.le

theorem optimalProcessLifetime_not_ae_constant (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) (c : ℝ≥0∞) :
    ¬ optimalProcessLifetime B ε =ᵐ[μ] fun _ => c := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  intro hconst
  have hc : 0 < c := by
    obtain ⟨ω, hω⟩ := hconst.exists
    simpa only [hω] using optimalProcessLifetime_pos B hε ω
  obtain ⟨t, ht, htc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hc
  have ht₀ : t ≠ 0 := by intro hz; simp [hz] at ht
  apply optimalProcessError_not_bounded hB ht₀ ε
  filter_upwards [hconst] with ω hω
  apply (optimalProcessLifetime_closed_tails B hε.le ω t).mp
  rw [hω]
  exact htc.le

end BrownianAffine
