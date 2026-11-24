import PLAStochastic.Affine.Process.DriftedSurvival.IntervalExponential

/-! # A linear finite-horizon drifted survival bound from exponential stopping -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Exponential stopping gives a finite-horizon survival bound uniform in the
upper endpoint r. In particular it is linear in the initial boundary distance. -/
theorem measureReal_boundedDriftedIntervalExit_eq_cutoff_le (hB : IsBrownianReal B μ)
    {x d r c : ℝ} (hx : x ∈ Icc 0 r) (hc : 0 ≤ c)
    (hrate : 0 < c ^ 2 / 2 - c * d) {T : ℝ≥0} (hT : 0 < T) :
    μ.real {ω | boundedDriftedIntervalExit B x d r T ω = T} ≤
      (1 - Real.exp (-c * x)) / (1 - Real.exp (-(c ^ 2 / 2 - c * d) * (T : ℝ))) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let τ := boundedDriftedIntervalExit B x d r T
  let rate := c ^ 2 / 2 - c * d
  let F (ω : Ω) := Real.exp (-c * x) * actualBrownianExponentialWith B (-c) (τ ω) ω
  let G (ω : Ω) := 1 - F ω
  let A := 1 - Real.exp (-rate * (T : ℝ))
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hA : 0 < A := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by dsimp only [rate]; nlinarith))
  have hstop := integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB (-c) x d r T
  have hFint : Integrable F μ := hstop.1.const_mul _
  have hGint : Integrable G μ := (integrable_const 1).sub hFint
  have hFval (ω : Ω) : F ω = Real.exp
      (-c * (x + B (τ ω) ω + d * (τ ω : ℝ)) - rate * (τ ω : ℝ)) := by
    dsimp only [F, actualBrownianExponentialWith, rate]
    rw [← Real.exp_add]
    congr 1
    ring
  have hX := boundedDriftedIntervalExit_endpoint_mem_ae hB hx d T
  have hG0 : 0 ≤ᵐ[μ] G := by
    filter_upwards [hX] with ω hω
    change 0 ≤ 1 - F ω
    rw [hFval]
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    have ht : (0 : ℝ) ≤ τ ω := NNReal.coe_nonneg _
    have hx0 : 0 ≤ x + B (τ ω) ω + d * (τ ω : ℝ) := hω.1
    have hl : 0 ≤ rate := hrate.le
    nlinarith [mul_nonneg hc hx0, mul_nonneg hl ht]
  have hGi : (∫ ω, G ω ∂μ) = 1 - Real.exp (-c * x) := by
    rw [integral_sub (integrable_const 1) hFint]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, mul_one]
    dsimp only [F]
    rw [integral_const_mul, hstop.2, mul_one]
  have hsub : {ω | τ ω = T} ≤ᵐ[μ] {ω | A ≤ G ω} := by
    filter_upwards [hX] with ω hω
    intro he
    change τ ω = T at he
    change A ≤ 1 - F ω
    rw [hFval]
    apply sub_le_sub_left
    apply Real.exp_le_exp.mpr
    dsimp only [A] at *
    rw [← he]
    have hx0 : 0 ≤ x + B (τ ω) ω + d * (τ ω : ℝ) := hω.1
    nlinarith [mul_nonneg hc hx0]
  have hm : μ.real {ω | τ ω = T} ≤ μ.real {ω | A ≤ G ω} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hb := mul_meas_ge_le_integral_of_nonneg hG0 hGint A
  change μ.real {ω | τ ω = T} ≤ (1 - Real.exp (-c * x)) / A
  apply (le_div_iff₀ hA).mpr
  rw [hGi] at hb
  nlinarith

/-- The constant depends only on the drift and time cutoff, uniformly in both
strip endpoints and the starting distance from the lower boundary. -/
theorem exists_linear_drifted_interval_survival_bound (hB : IsBrownianReal B μ)
    (d : ℝ) {T : ℝ≥0} (hT : 0 < T) : ∃ C : ℝ, 0 < C ∧
      ∀ x r : ℝ, x ∈ Icc 0 r →
        μ.real {ω | boundedDriftedIntervalExit B x d r T ω = T} ≤ C * x := by
  let c := 2 * |d| + 1
  let rate := c ^ 2 / 2 - c * d
  let A := 1 - Real.exp (-rate * (T : ℝ))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hrate : 0 < rate := by
    have hp : 0 < c / 2 - d := by dsimp only [c]; linarith [le_abs_self d]
    have he : rate = c * (c / 2 - d) := by dsimp only [rate]; ring
    rw [he]
    exact mul_pos hc hp
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hA : 0 < A := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hrate hT']))
  refine ⟨c / A, div_pos hc hA, ?_⟩
  intro x r hx
  have hb := measureReal_boundedDriftedIntervalExit_eq_cutoff_le hB hx hc.le hrate hT
  have hn : 1 - Real.exp (-c * x) ≤ c * x := by
    linarith [Real.add_one_le_exp (-c * x)]
  calc
    _ ≤ (1 - Real.exp (-c * x)) / A := hb
    _ ≤ (c * x) / A := div_le_div_of_nonneg_right hn hA.le
    _ = _ := by ring

omit [MeasurableSpace Ω] in
theorem boundedDriftedIntervalExit_eq_cutoff_of_mem {x d r : ℝ} {T : ℝ≥0} {ω : Ω}
    (hmem : ∀ t : ℝ≥0, t ≤ T → x + B t ω + d * (t : ℝ) ∈ Icc 0 r) :
    boundedDriftedIntervalExit B x d r T ω = T := by
  have he : {t : ℝ≥0 | t ≤ T ∧ x + B t ω + d * (t : ℝ) ∈ driftBarrierSet r 0} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have hb := hmem t ht.1
    have hx := ht.2
    simp only [driftBarrierSet, mem_union, mem_Iio, mem_Ioi, neg_zero] at hx
    rcases hx with hlo | hhi
    · exact (not_lt.mpr hb.1) hlo
    · exact (not_lt.mpr hb.2) hhi
  simp only [boundedDriftedIntervalExit, boundedOpenExitTime, he, insert_empty_eq, csInf_singleton]

/-- A closed-strip survival event inherits the same linear boundary-distance
bound. This is the continuous comparison needed for accepted grid prefixes. -/
theorem exists_linear_drifted_strip_survival_bound (hB : IsBrownianReal B μ)
    (d : ℝ) {T : ℝ≥0} (hT : 0 < T) : ∃ C : ℝ, 0 < C ∧
      ∀ x r : ℝ, x ∈ Icc 0 r →
        μ.real {ω | ∀ t : ℝ≥0, t ≤ T → x + B t ω + d * (t : ℝ) ∈ Icc 0 r} ≤ C * x := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨C, hC, hb⟩ := exists_linear_drifted_interval_survival_bound hB d hT
  refine ⟨C, hC, fun x r hx => ?_⟩
  exact (measureReal_mono (fun ω hω => boundedDriftedIntervalExit_eq_cutoff_of_mem hω)).trans (hb x r hx)

end BrownianAffine
