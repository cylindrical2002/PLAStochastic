import PLAStochastic.Affine.Process.DriftedSurvival.IntervalExponential

/-! # Finite-horizon Brownian maximum bounds from genuine exponential stopping -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A strict maximum excursion forces exit before the cutoff, so the stopped
Brownian position is exactly one of the two excursion boundaries. -/
theorem brownian_max_excursion_exit_boundary_ae (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 ≤ r) (T : ℝ≥0) :
    ∀ᵐ ω ∂μ, (∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|) →
      B (boundedDriftedIntervalExit B r 0 (2 * r) T ω) ω = r ∨
        B (boundedDriftedIntervalExit B r 0 (2 * r) T ω) ω = -r := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  intro hexc
  let X (t : ℝ≥0) (_ : Ω) := r + B t ω
  let τ := boundedOpenExitTime X (driftBarrierSet (2 * r) 0) T ω
  have hct : Continuous (X · ω) := hc.const_add r
  have h0 : X 0 ω ∈ Icc (-0) (2 * r) := by dsimp only [X]; rw [hz]; constructor <;> linarith
  have hτ : τ < T := by
    by_contra ht
    have he : τ = T := le_antisymm (boundedOpenExitTime_le X _ T ω) (le_of_not_gt ht)
    obtain ⟨t, ht, hbad⟩ := hexc
    have hmem : X t ω ∈ Icc (-0) (2 * r) := by
      rcases ht.lt_or_eq with hlt | heq
      · exact before_boundedOpenExitTime_mem_strip (T := T) (by change t < τ; rwa [he])
      · rw [heq, ← he]
        exact boundedOpenExitTime_mem_strip hct h0
    have hb : |B t ω| ≤ r := by
      rw [abs_le]
      dsimp only [X] at hmem
      constructor <;> linarith [hmem.1, hmem.2]
    exact (not_lt.mpr hb) hbad
  have hbd := boundedOpenExitTime_boundary hct h0 hτ
  have he : τ = boundedDriftedIntervalExit B r 0 (2 * r) T ω := by
    simp only [τ, X, boundedDriftedIntervalExit, boundedOpenExitTime, zero_mul, add_zero]
  change r + B τ ω = 2 * r ∨ r + B τ ω = -0 at hbd
  rw [he] at hbd
  rcases hbd with hp | hn
  · left; linarith
  · right; linarith

/-- A Chernoff bound for the whole continuous Brownian excursion, not just
sampled endpoints. The parameter c can be optimized for any grid width. -/
theorem measureReal_brownian_max_excursion_le_chernoff (hB : IsBrownianReal B μ)
    {r c : ℝ} (hr : 0 ≤ r) (T : ℝ≥0) :
    μ.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤
      2 * Real.exp (-(c * r - c ^ 2 / 2 * (T : ℝ))) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let τ := boundedDriftedIntervalExit B r 0 (2 * r) T
  let F (ω : Ω) := actualBrownianExponentialWith B c (τ ω) ω +
    actualBrownianExponentialWith B (-c) (τ ω) ω
  let A := Real.exp (c * r - c ^ 2 / 2 * (T : ℝ))
  have hA : 0 < A := Real.exp_pos _
  have hp := integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB c r 0 (2 * r) T
  have hn := integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB (-c) r 0 (2 * r) T
  have hFi : Integrable F μ := hp.1.add hn.1
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω => add_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)
  have hFe : (∫ ω, F ω ∂μ) = 2 := by rw [integral_add hp.1 hn.1, hp.2, hn.2]; norm_num
  have hsub : {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ᵐ[μ] {ω | A ≤ F ω} := by
    filter_upwards [brownian_max_excursion_exit_boundary_ae hB hr T] with ω hω
    intro he
    have hτ : (τ ω : ℝ) ≤ T := by exact_mod_cast boundedDriftedIntervalExit_le r 0 (2 * r) T ω
    have hquad : c ^ 2 / 2 * (τ ω : ℝ) ≤ c ^ 2 / 2 * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hτ (by positivity)
    rcases hω he with hpos | hneg
    · have hex : A ≤ actualBrownianExponentialWith B c (τ ω) ω := by
        dsimp only [A, actualBrownianExponentialWith]
        change B (τ ω) ω = r at hpos
        rw [hpos]
        exact Real.exp_le_exp.mpr (by linarith)
      exact hex.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · have hex : A ≤ actualBrownianExponentialWith B (-c) (τ ω) ω := by
        dsimp only [A, actualBrownianExponentialWith]
        change B (τ ω) ω = -r at hneg
        rw [hneg]
        exact Real.exp_le_exp.mpr (by nlinarith)
      exact hex.trans (le_add_of_nonneg_left (Real.exp_nonneg _))
  have hm := ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
  have hmark := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall hF0) hFi A
  rw [hFe] at hmark
  have hb : μ.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ 2 / A := by
    apply (le_div_iff₀ hA).mpr
    change μ.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤ μ.real {ω | A ≤ F ω} at hm
    nlinarith
  simpa only [A, div_eq_mul_inv, ← Real.exp_neg] using hb

/-- The standard Gaussian excursion estimate, optimized at c=r/T. -/
theorem measureReal_brownian_max_excursion_le (hB : IsBrownianReal B μ)
    {r : ℝ} (hr : 0 ≤ r) {T : ℝ≥0} (hT : 0 < T) :
    μ.real {ω | ∃ t : ℝ≥0, t ≤ T ∧ r < |B t ω|} ≤
      2 * Real.exp (-(r ^ 2 / (2 * (T : ℝ)))) := by
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  have he : (r / (T : ℝ)) * r - (r / (T : ℝ)) ^ 2 / 2 * (T : ℝ) = r ^ 2 / (2 * (T : ℝ)) := by
    field_simp
    ring
  simpa only [he] using measureReal_brownian_max_excursion_le_chernoff (c := r / (T : ℝ)) hB hr T

/-- A bad within-grid fluctuation in one of the first N sampling cells. -/
def brownianGridOscillationEvent (B : ℝ≥0 → Ω → ℝ) (h : ℝ≥0) (N : ℕ) (ρ : ℝ) : Set Ω :=
  ⋃ k ∈ Finset.range N, {ω | ∃ t : ℝ≥0, t ≤ h ∧
    ρ < |B ((k : ℝ≥0) * h + t) ω - B ((k : ℝ≥0) * h) ω|}

/-- The grid union bound uses Brownian increments' laws, without claiming that
successive recording intervals or carried values are independent. -/
theorem measureReal_brownianGridOscillationEvent_le (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : 0 < h) (N : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    μ.real (brownianGridOscillationEvent B h N ρ) ≤
      (N : ℝ) * (2 * Real.exp (-(ρ ^ 2 / (2 * (h : ℝ))))) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply le_trans (measureReal_biUnion_finset_le (Finset.range N) _) ?_
  calc
    _ ≤ ∑ _k ∈ Finset.range N, 2 * Real.exp (-(ρ ^ 2 / (2 * (h : ℝ)))) := by
      apply Finset.sum_le_sum
      intro k _
      exact measureReal_brownian_max_excursion_le (hB.shift ((k : ℝ≥0) * h)) hρ hh
    _ = _ := by simp

/-- A radius whose exceptional grid fluctuation probability is O(h^3) over a
fixed physical horizon. -/
def brownianGridLogRadius (h : ℝ) : ℝ := Real.sqrt (8 * h * Real.log (1 / h))

theorem brownianGridLogRadius_chernoff {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Real.exp (-(brownianGridLogRadius h ^ 2 / (2 * h))) = h ^ 4 := by
  have hlog : 0 ≤ Real.log (1 / h) := Real.log_nonneg ((one_le_div hh).mpr hh1)
  rw [brownianGridLogRadius, Real.sq_sqrt (mul_nonneg (by positivity) hlog)]
  have he : -(8 * h * Real.log (1 / h) / (2 * h)) = 4 * Real.log h := by
    rw [one_div, Real.log_inv]
    field_simp
    ring
  rw [he]
  convert Real.exp_nat_mul (Real.log h) 4 using 1 <;> simp [Real.exp_log hh]

/-- Uniform quantitative mesh error bound over any fixed total grid duration. -/
theorem measureReal_brownianGridOscillationEvent_logRadius_le (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : 0 < h) (hh1 : (h : ℝ) ≤ 1) (N : ℕ) {T : ℝ}
    (hN : (N : ℝ) * h ≤ T) :
    μ.real (brownianGridOscillationEvent B h N (brownianGridLogRadius h)) ≤
      2 * T * (h : ℝ) ^ 3 := by
  have hh' : (0 : ℝ) < h := by exact_mod_cast hh
  have hb := measureReal_brownianGridOscillationEvent_le (ρ := brownianGridLogRadius h) hB hh N
    (Real.sqrt_nonneg (8 * (h : ℝ) * Real.log (1 / (h : ℝ))))
  rw [brownianGridLogRadius_chernoff hh' hh1] at hb
  calc
    _ ≤ (N : ℝ) * (2 * (h : ℝ) ^ 4) := hb
    _ = 2 * ((N : ℝ) * (h : ℝ)) * (h : ℝ) ^ 3 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity)

end BrownianAffine
