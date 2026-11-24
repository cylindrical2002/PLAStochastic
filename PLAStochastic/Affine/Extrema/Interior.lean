import PLAStochastic.Affine.Extrema.UniqueExtrema
import PLAStochastic.Brownian.PathLaw.TimeReversal
import PLAStochastic.Affine.Process.Hitting.LinearOscillation

/-!
# Brownian residual extrema are distinct and interior

Two-sided linear oscillation excludes the origin simultaneously for every
drift. Applying the same result to the actual reversed Brownian process
excludes the terminal point. This completes the fixed-drift uniqueness lemma.
-/

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def nnrealRangeTime (t : ℝ≥0) (ht : t ≤ 1) : RangeTime :=
  ⟨t, t.coe_nonneg, by exact_mod_cast ht⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem slopeResidual_actual_unit (B : ℝ≥0 → Ω → ℝ) {ω : Ω}
    (hω : Continuous (B · ω)) (a : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    slopeResidual (unitPath (processPath B ω) 1) a (nnrealRangeTime t ht) =
      B t ω - a * (t : ℝ) := by
  have hu : unitPath (processPath B ω) 1 (nnrealRangeTime t ht) = B t ω := by
    simpa only [NNReal.coe_one, nnrealRangeTime, one_mul] using!
      unitPath_processPath_apply hω 1 (nnrealRangeTime t ht)
  unfold slopeResidual
  rw [hu]
  rfl

/-- Neither endpoint can be a residual maximum or minimum, for any drift,
on one common full-measure event. -/
theorem brownian_endpoint_strict_extrema_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ,
      slopeLower (unitPath (processPath B ω) 1) a <
        slopeResidual (unitPath (processPath B ω) 1) a rangeTimeZero ∧
      slopeResidual (unitPath (processPath B ω) 1) a rangeTimeZero <
        slopeUpper (unitPath (processPath B ω) 1) a ∧
      slopeLower (unitPath (processPath B ω) 1) a <
        slopeResidual (unitPath (processPath B ω) 1) a rangeTimeOne ∧
      slopeResidual (unitPath (processPath B ω) 1) a rangeTimeOne <
        slopeUpper (unitPath (processPath B ω) 1) a := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    brownian_linear_oscillation_zero_ae hB,
    brownian_linear_oscillation_zero_ae (isBrownianReal_timeReversal hB 1)]
    with ω hc hzero hleft hright
  intro a
  have h₀ : slopeResidual (unitPath (processPath B ω) 1) a rangeTimeZero = 0 := by
    have h := slopeResidual_actual_unit B hc a 0 (by simp)
    simpa only [nnrealRangeTime, rangeTimeZero, hzero, NNReal.coe_zero, mul_zero, sub_self] using h
  have h₁ : slopeResidual (unitPath (processPath B ω) 1) a rangeTimeOne = B 1 ω - a := by
    have h := slopeResidual_actual_unit B hc a 1 le_rfl
    simpa only [nnrealRangeTime, rangeTimeOne, NNReal.coe_one, mul_one] using h
  obtain ⟨⟨s, hs0, hs1, hs⟩, ⟨t, ht0, ht1, ht⟩⟩ := hleft a 1 (by norm_num)
  have hsU := slopeResidual_le_upper (unitPath (processPath B ω) 1) a (nnrealRangeTime s hs1.le)
  have htL := slopeLower_le_residual (unitPath (processPath B ω) 1) a (nnrealRangeTime t ht1.le)
  rw [slopeResidual_actual_unit B hc a s hs1.le] at hsU
  rw [slopeResidual_actual_unit B hc a t ht1.le] at htL
  obtain ⟨⟨u, hu0, hu1, hu⟩, ⟨v, hv0, hv1, hv⟩⟩ := hright a 1 (by norm_num)
  rw [timeReversedProcess_of_le B hu1.le ω] at hu
  rw [timeReversedProcess_of_le B hv1.le ω] at hv
  have huL := slopeLower_le_residual (unitPath (processPath B ω) 1) a
    (nnrealRangeTime (1 - u) tsub_le_self)
  have hvU := slopeResidual_le_upper (unitPath (processPath B ω) 1) a
    (nnrealRangeTime (1 - v) tsub_le_self)
  rw [slopeResidual_actual_unit B hc a (1 - u) tsub_le_self, NNReal.coe_sub hu1.le,
    NNReal.coe_one] at huL
  rw [slopeResidual_actual_unit B hc a (1 - v) tsub_le_self, NNReal.coe_sub hv1.le,
    NNReal.coe_one] at hvU
  rw [h₀, h₁]
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> nlinarith

private theorem extremizer_interior_of_endpoint_bounds (g : Path 1) (a : ℝ)
    (h₀ : slopeLower g a < slopeResidual g a rangeTimeZero ∧
      slopeResidual g a rangeTimeZero < slopeUpper g a)
    (h₁ : slopeLower g a < slopeResidual g a rangeTimeOne ∧
      slopeResidual g a rangeTimeOne < slopeUpper g a)
    {t : RangeTime} (ht : slopeResidual g a t = slopeUpper g a ∨
      slopeResidual g a t = slopeLower g a) : 0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  have hn₀ : t ≠ rangeTimeZero := by
    intro he
    subst t
    rcases ht with ht | ht <;> linarith
  have hn₁ : t ≠ rangeTimeOne := by
    intro he
    subst t
    rcases ht with ht | ht <;> linarith
  constructor
  · refine lt_of_le_of_ne t.property.1 ?_
    intro he
    exact hn₀ (Subtype.ext he.symm)
  · refine lt_of_le_of_ne t.property.2 ?_
    intro he
    exact hn₁ (Subtype.ext he)

theorem brownian_all_drift_extrema_interior_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ t : RangeTime,
      (slopeResidual (unitPath (processPath B ω) 1) a t =
          slopeUpper (unitPath (processPath B ω) 1) a ∨
        slopeResidual (unitPath (processPath B ω) 1) a t =
          slopeLower (unitPath (processPath B ω) 1) a) →
      0 < (t : ℝ) ∧ (t : ℝ) < 1 := by
  filter_upwards [brownian_endpoint_strict_extrema_ae hB] with ω hω
  intro a t ht
  exact extremizer_interior_of_endpoint_bounds _ a ⟨(hω a).1, (hω a).2.1⟩ (hω a).2.2 ht

theorem brownian_all_drift_extrema_distinct_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ,
      upperTime (unitPath (processPath B ω) 1) a ≠ lowerTime (unitPath (processPath B ω) 1) a := by
  filter_upwards [brownian_endpoint_strict_extrema_ae hB] with ω hω
  intro a heq
  have hu := upperTime_attains (unitPath (processPath B ω) 1) a
  have hl := lowerTime_attains (unitPath (processPath B ω) 1) a
  rw [heq] at hu
  have hlo := (hω a).1
  have hhi := (hω a).2.1
  linarith

/-- The manuscript's full fixed-drift extremum lemma: unique maxima and minima,
distinct selected times, and both times strictly between zero and one. -/
theorem brownian_extrema_unique_distinct_interior_ae (hB : IsBrownianReal B μ) (a : ℝ) :
    ∀ᵐ ω ∂μ,
      (∃! t : RangeTime, slopeResidual (unitPath (processPath B ω) 1) a t =
        slopeUpper (unitPath (processPath B ω) 1) a) ∧
      (∃! t : RangeTime, slopeResidual (unitPath (processPath B ω) 1) a t =
        slopeLower (unitPath (processPath B ω) 1) a) ∧
      (0 < (upperTime (unitPath (processPath B ω) 1) a : ℝ) ∧
        (upperTime (unitPath (processPath B ω) 1) a : ℝ) < 1) ∧
      (0 < (lowerTime (unitPath (processPath B ω) 1) a : ℝ) ∧
        (lowerTime (unitPath (processPath B ω) 1) a : ℝ) < 1) ∧
      upperTime (unitPath (processPath B ω) 1) a ≠ lowerTime (unitPath (processPath B ω) 1) a := by
  filter_upwards [brownian_extrema_unique_ae hB a, brownian_all_drift_extrema_interior_ae hB,
    brownian_all_drift_extrema_distinct_ae hB] with ω hu hi hd
  exact ⟨hu.1, hu.2, hi a _ (Or.inl (upperTime_attains _ a)),
    hi a _ (Or.inr (lowerTime_attains _ a)), hd a⟩

theorem brownian_abs_slopeRange_deriv_positive_ae (hB : IsBrownianReal B μ) (a : ℝ) :
    ∀ᵐ ω ∂μ, 0 < |deriv (slopeRange (unitPath (processPath B ω) 1)) a| := by
  filter_upwards [brownian_slopeRange_deriv_eq_extremal_times_ae hB a,
    brownian_all_drift_extrema_distinct_ae hB] with ω he hd
  rw [he]
  apply abs_pos.mpr
  apply sub_ne_zero.mpr
  intro hc
  exact hd a (Subtype.ext hc.symm)

end BrownianAffine
