import PLAStochastic.Brownian.PathLaw.TimeInversion

/-!
# Almost-sure termination at every lower drift barrier

The sublinear-growth conclusion follows from the already proved continuity of
time-inverted Brownian motion at zero. No Brownian strong law is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem brownian_ratio_tendsto_zero_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ≥0 => B t ω / (t : ℝ)) atTop (𝓝 0) := by
  filter_upwards [(isBrownianReal_timeInversion hB).cont] with ω hω
  have ht := (hω.tendsto 0).comp
    (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ≥0 => t⁻¹) atTop (𝓝 0))
  simpa [Function.comp_def, timeInvertedProcess, div_eq_mul_inv, mul_comm] using ht

omit [MeasurableSpace Ω] in
theorem drift_tendsto_atBot_of_ratio {X : ℝ≥0 → ℝ}
    (hX : Tendsto (fun t : ℝ≥0 => X t / (t : ℝ)) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ≥0 => X t - c * (t : ℝ)) atTop atBot := by
  have ht : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hr : Tendsto (fun t : ℝ≥0 => X t / (t : ℝ) - c) atTop (𝓝 (-c)) := by
    simpa only [zero_sub] using hX.sub_const c
  have hd := ht.atTop_mul_neg (neg_neg_of_pos hc) hr
  apply hd.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp

theorem brownian_drift_tendsto_atBot_ae (hB : IsBrownianReal B μ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ≥0 => B t ω - c * (t : ℝ)) atTop atBot :=
  (brownian_ratio_tendsto_zero_ae hB).mono (fun _ hω => drift_tendsto_atBot_of_ratio hω hc)

/-- Every finite lower barrier is crossed by the drifted Brownian path, outside
one null set, and after any prescribed deterministic starting time. -/
theorem brownian_eventually_below_every_barrier (hB : IsBrownianReal B μ) {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ s : ℝ≥0, ∃ t : ℝ≥0, s ≤ t ∧ B t ω - c * (t : ℝ) < a := by
  filter_upwards [brownian_drift_tendsto_atBot_ae hB hc] with ω hω
  intro a s
  exact ((eventually_ge_atTop s).and (hω.eventually (eventually_lt_atBot a))).exists

end BrownianAffine
