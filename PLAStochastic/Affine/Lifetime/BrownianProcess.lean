import PLAStochastic.Affine.Lifetime.Pathwise
import PLAStochastic.Affine.Error.Measurable

/-!
# Lifetimes attached to an actual Brownian motion

Every statement below starts from `IsBrownianReal`. The total continuous-path
representative agrees with the Brownian trajectory simultaneously at all
nonnegative times outside one null set. No path-space measurability assumption
or finiteness of the lifetime is added.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def anchoredProcessLifetime (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  anchoredLifetime (processPath B ω) ε

def optimalProcessLifetime (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  optimalLifetime (processPath B ω) ε

theorem aemeasurable_anchoredProcessLifetime (hB : IsBrownianReal B μ) (ε : ℝ) :
    AEMeasurable (anchoredProcessLifetime B ε) μ :=
  aemeasurable_anchoredLifetime (fun t => aemeasurable_anchoredProcessError hB t) ε

theorem aemeasurable_optimalProcessLifetime (hB : IsBrownianReal B μ) (ε : ℝ) :
    AEMeasurable (optimalProcessLifetime B ε) μ :=
  aemeasurable_optimalLifetime (fun t => aemeasurable_optimalProcessError hB t) ε

omit [MeasurableSpace Ω] in
theorem anchoredProcessLifetime_le_optimalProcessLifetime (B : ℝ≥0 → Ω → ℝ)
    (ε : ℝ) (ω : Ω) : anchoredProcessLifetime B ε ω ≤ optimalProcessLifetime B ε ω :=
  anchoredLifetime_le_optimalLifetime (processPath B ω) ε

/-- All anchored closed tails hold simultaneously outside one null set. -/
theorem anchoredProcessLifetime_closed_tails (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) ≤ anchoredProcessLifetime B ε ω ↔ anchoredProcessError B t ω ≤ ε := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  have hzero : processPath B ω 0 = 0 := by
    simpa only [NNReal.coe_zero, hz] using processPath_apply_of_continuous hc 0
  intro t
  exact le_anchoredLifetime_iff (processPath B ω) hzero hε t

omit [MeasurableSpace Ω] in
theorem optimalProcessLifetime_closed_tails (B : ℝ≥0 → Ω → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (ω : Ω) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ optimalProcessLifetime B ε ω ↔ optimalProcessError B t ω ≤ ε :=
  le_optimalLifetime_iff (processPath B ω) hε t

theorem anchoredProcessLifetime_pos_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) : ∀ᵐ ω ∂μ, 0 < anchoredProcessLifetime B ε ω := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  apply anchoredLifetime_pos (processPath B ω) _ hε
  simpa only [NNReal.coe_zero, hz] using processPath_apply_of_continuous hc 0

omit [MeasurableSpace Ω] in
theorem optimalProcessLifetime_pos (B : ℝ≥0 → Ω → ℝ)
    {ε : ℝ} (hε : 0 < ε) (ω : Ω) : 0 < optimalProcessLifetime B ε ω :=
  optimalLifetime_pos (processPath B ω) hε

/-- Closed tails of the actual Brownian lifetime are equivalent to an actual anchored fit
at every nonnegative time in the observation interval. -/
theorem anchoredProcessLifetime_tail_iff_fit_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) ≤ anchoredProcessLifetime B ε ω ↔
        ∃ a : ℝ, ∀ s : ℝ≥0, s ≤ t → |B s ω - a * (s : ℝ)| ≤ ε := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  have hzero : processPath B ω 0 = 0 := by
    simpa only [NNReal.coe_zero, hz] using processPath_apply_of_continuous hc 0
  intro t
  rw [show anchoredProcessLifetime B ε ω = anchoredLifetime (processPath B ω) ε from rfl,
    le_anchoredLifetime_iff_exists_fit (processPath B ω) hzero hε t]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a, fun s hs => ?_⟩
    have h := ha ⟨s, s.property, hs⟩
    simpa only [processPath_apply_of_continuous hc s] using! h
  · rintro ⟨a, ha⟩
    refine ⟨a, fun s => ?_⟩
    have h := ha ⟨s, s.property.1⟩ s.property.2
    simpa only [← processPath_apply_of_continuous hc ⟨s, s.property.1⟩] using! h

theorem optimalProcessLifetime_tail_iff_fit_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
      (t : ℝ≥0∞) ≤ optimalProcessLifetime B ε ω ↔
        ∃ a b : ℝ, ∀ s : ℝ≥0, s ≤ t → |B s ω - a * (s : ℝ) - b| ≤ ε := by
  filter_upwards [hB.cont] with ω hc
  intro t
  rw [show optimalProcessLifetime B ε ω = optimalLifetime (processPath B ω) ε from rfl,
    le_optimalLifetime_iff_exists_fit (processPath B ω) hε t]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, fun s hs => ?_⟩
    have h := hab ⟨s, s.property, hs⟩
    simpa only [processPath_apply_of_continuous hc s] using! h
  · rintro ⟨a, b, hab⟩
    refine ⟨a, b, fun s => ?_⟩
    have h := hab ⟨s, s.property.1⟩ s.property.2
    simpa only [← processPath_apply_of_continuous hc ⟨s, s.property.1⟩] using! h

end

end BrownianAffine
