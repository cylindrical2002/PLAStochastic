import PLAStochastic.Affine.Process.DriftedSurvival.IntervalExponential

/-! # Boundary-sensitive drifted survival estimates by two stopped exponentials -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def driftedExitPosition (B : ℝ≥0 → Ω → ℝ) (x d r : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  x + B (boundedDriftedIntervalExit B x d r T ω) ω +
    d * (boundedDriftedIntervalExit B x d r T ω : ℝ)

/-- Twice exp(-d*x)*sinh(2*d*x); this form exposes its two exponential martingales. -/
def driftedExitWeight (d x : ℝ) : ℝ := Real.exp (d * x) - Real.exp (-3 * d * x)

theorem driftedExitWeight_nonneg {d x : ℝ} (hd : 0 ≤ d) (hx : 0 ≤ x) :
    0 ≤ driftedExitWeight d x := by
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hd hx]

theorem driftedExitWeight_pos {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    0 < driftedExitWeight d x := by
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  nlinarith [mul_pos hd hx]

/-- A small general Markov wrapper that keeps the dominated event explicit. -/
theorem measureReal_le_integral_div_of_ae_dom [IsFiniteMeasure μ]
    {F : Ω → ℝ} {E : Set Ω} {a : ℝ} (ha : 0 < a) (hFi : Integrable F μ)
    (hF0 : 0 ≤ᵐ[μ] F) (hE : E ≤ᵐ[μ] {ω | a ≤ F ω}) :
    μ.real E ≤ (∫ ω, F ω ∂μ) / a := by
  have hm : μ.real E ≤ μ.real {ω | a ≤ F ω} :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hE)
  have hb := mul_meas_ge_le_integral_of_nonneg hF0 hFi a
  apply (le_div_iff₀ ha).mpr
  nlinarith

/-- The upper-boundary weight is integrated at the genuine bounded exit time.
Its small-start factor is retained exactly. -/
theorem integral_driftedExitWeight_stopped (hB : IsBrownianReal B μ)
    (x d r : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => Real.exp (-(3 * d ^ 2 / 2) *
      (boundedDriftedIntervalExit B x d r T ω : ℝ)) *
      driftedExitWeight d (driftedExitPosition B x d r T ω)) μ ∧
      (∫ ω, Real.exp (-(3 * d ^ 2 / 2) *
        (boundedDriftedIntervalExit B x d r T ω : ℝ)) *
        driftedExitWeight d (driftedExitPosition B x d r T ω) ∂μ) = driftedExitWeight d x := by
  have hp := integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB d x d r T
  have hn := integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB (-3 * d) x d r T
  have heq : (fun ω => Real.exp (-(3 * d ^ 2 / 2) *
      (boundedDriftedIntervalExit B x d r T ω : ℝ)) *
      driftedExitWeight d (driftedExitPosition B x d r T ω)) =
      (fun ω => Real.exp (d * x) * actualBrownianExponentialWith B d
        (boundedDriftedIntervalExit B x d r T ω) ω -
        Real.exp (-3 * d * x) * actualBrownianExponentialWith B (-3 * d)
          (boundedDriftedIntervalExit B x d r T ω) ω) := by
    funext ω
    dsimp only [driftedExitWeight, driftedExitPosition, actualBrownianExponentialWith]
    rw [mul_sub, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> congr 1 <;> ring
  rw [heq]
  refine ⟨(hp.1.const_mul _).sub (hn.1.const_mul _), ?_⟩
  rw [integral_sub (hp.1.const_mul _) (hn.1.const_mul _), integral_const_mul,
    integral_const_mul, hp.2, hn.2, mul_one, mul_one]
  rfl

/-- The harmonic exponential controls exits through the nearby lower boundary. -/
theorem integral_driftedExit_harmonic (hB : IsBrownianReal B μ)
    (x d r : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => Real.exp (-2 * d * driftedExitPosition B x d r T ω)) μ ∧
      (∫ ω, Real.exp (-2 * d * driftedExitPosition B x d r T ω) ∂μ) = Real.exp (-2 * d * x) := by
  have hs := integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB (-2 * d) x d r T
  have heq : (fun ω => Real.exp (-2 * d * driftedExitPosition B x d r T ω)) =
      (fun ω => Real.exp (-2 * d * x) * actualBrownianExponentialWith B (-2 * d)
        (boundedDriftedIntervalExit B x d r T ω) ω) := by
    funext ω
    dsimp only [driftedExitPosition, actualBrownianExponentialWith]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact ⟨hs.1.const_mul _, by rw [integral_const_mul, hs.2, mul_one]⟩

theorem measureReal_driftedExit_lower_le (hB : IsBrownianReal B μ)
    (x d r : ℝ) (T : ℝ≥0) :
    μ.real {ω | driftedExitPosition B x d r T ω = 0} ≤ Real.exp (-2 * d * x) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hs := integral_driftedExit_harmonic hB x d r T
  have hE : {ω | driftedExitPosition B x d r T ω = 0} ≤ᵐ[μ]
      {ω | 1 ≤ Real.exp (-2 * d * driftedExitPosition B x d r T ω)} := by
    apply Eventually.of_forall
    intro ω hω
    change driftedExitPosition B x d r T ω = 0 at hω
    change 1 ≤ Real.exp (-2 * d * driftedExitPosition B x d r T ω)
    rw [hω]
    simp
  have hb := measureReal_le_integral_div_of_ae_dom zero_lt_one hs.1
    (Eventually.of_forall fun _ => Real.exp_nonneg _) hE
  simpa only [hs.2, div_one] using hb

theorem measureReal_driftedExit_upper_le (hB : IsBrownianReal B μ)
    {x d r : ℝ} (hx : x ∈ Icc 0 r) (hd : 0 < d) (hr : 0 < r) (T : ℝ≥0) :
    μ.real {ω | driftedExitPosition B x d r T ω = r} ≤
      driftedExitWeight d x / (Real.exp (-(3 * d ^ 2 / 2) * (T : ℝ)) * driftedExitWeight d r) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let τ := boundedDriftedIntervalExit B x d r T
  let F (ω : Ω) := Real.exp (-(3 * d ^ 2 / 2) * (τ ω : ℝ)) *
    driftedExitWeight d (driftedExitPosition B x d r T ω)
  let A := Real.exp (-(3 * d ^ 2 / 2) * (T : ℝ)) * driftedExitWeight d r
  have hA : 0 < A := mul_pos (Real.exp_pos _) (driftedExitWeight_pos hd hr)
  have hs := integral_driftedExitWeight_stopped hB x d r T
  have hF0 : 0 ≤ᵐ[μ] F := by
    filter_upwards [boundedDriftedIntervalExit_endpoint_mem_ae hB hx d T] with ω hω
    exact mul_nonneg (Real.exp_nonneg _) (driftedExitWeight_nonneg hd.le hω.1)
  have hE : {ω | driftedExitPosition B x d r T ω = r} ≤ᵐ[μ] {ω | A ≤ F ω} := by
    apply Eventually.of_forall
    intro ω hω
    change driftedExitPosition B x d r T ω = r at hω
    change A ≤ Real.exp (-(3 * d ^ 2 / 2) * (τ ω : ℝ)) * driftedExitWeight d (driftedExitPosition B x d r T ω)
    rw [hω]
    apply mul_le_mul_of_nonneg_right _ (driftedExitWeight_pos hd hr).le
    apply Real.exp_le_exp.mpr
    have ht : (τ ω : ℝ) ≤ T := by exact_mod_cast boundedDriftedIntervalExit_le (B := B) x d r T ω
    exact mul_le_mul_of_nonpos_left ht (neg_nonpos.mpr (by positivity))
  have hb := measureReal_le_integral_div_of_ae_dom hA hs.1 hF0 hE
  simpa only [hs.2] using hb

/-- Exit before the cutoff must use one of the two boundaries. Combining the
two estimates gives a lower bound for actual finite-horizon survival. -/
theorem measureReal_drifted_survival_ge (hB : IsBrownianReal B μ)
    {x d r : ℝ} (hx : x ∈ Icc 0 r) (hd : 0 < d) (hr : 0 < r) (T : ℝ≥0) :
    1 - Real.exp (-2 * d * x) -
      driftedExitWeight d x / (Real.exp (-(3 * d ^ 2 / 2) * (T : ℝ)) * driftedExitWeight d r) ≤
        μ.real {ω | boundedDriftedIntervalExit B x d r T ω = T} := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let E₀ : Set Ω := {ω | driftedExitPosition B x d r T ω = 0}
  let Eᵣ : Set Ω := {ω | driftedExitPosition B x d r T ω = r}
  let S : Set Ω := {ω | boundedDriftedIntervalExit B x d r T ω = T}
  have hcover : (Set.univ : Set Ω) ≤ᵐ[μ] (((E₀ ∪ Eᵣ) ∪ S) : Set Ω) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
    intro _
    by_cases he : boundedDriftedIntervalExit B x d r T ω = T
    · exact Or.inr he
    · have ht : boundedDriftedIntervalExit B x d r T ω < T :=
        lt_of_le_of_ne (boundedDriftedIntervalExit_le x d r T ω) he
      have h0 : x + B 0 ω + d * ((0 : ℝ≥0) : ℝ) ∈ Icc (-0) r := by
        simpa only [hz, add_zero, NNReal.coe_zero, mul_zero, neg_zero] using hx
      have hb := boundedOpenExitTime_boundary
        (X := fun t ω => x + B t ω + d * (t : ℝ))
        ((hc.const_add x).add (continuous_subtype_val.const_mul d)) h0 ht
      change driftedExitPosition B x d r T ω = r ∨ driftedExitPosition B x d r T ω = -0 at hb
      rcases hb with hb | hb
      · exact Or.inl (Or.inr hb)
      · apply Or.inl
        apply Or.inl
        change driftedExitPosition B x d r T ω = 0
        simpa only [neg_zero] using hb
  have hm : μ.real Set.univ ≤ μ.real ((E₀ ∪ Eᵣ) ∪ S) :=
    ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hcover)
  have hu := (measureReal_union_le (μ := μ) (E₀ ∪ Eᵣ) S).trans
    (add_le_add (measureReal_union_le (μ := μ) E₀ Eᵣ) le_rfl)
  have hlo := measureReal_driftedExit_lower_le hB x d r T
  have hhi := measureReal_driftedExit_upper_le hB hx hd hr T
  have huniv : μ.real Set.univ = 1 := by simp [measureReal_def]
  rw [huniv] at hm
  change 1 - Real.exp (-2 * d * x) - _ ≤ μ.real S
  change μ.real E₀ ≤ _ at hlo
  change μ.real Eᵣ ≤ _ at hhi
  linarith

/-- Two genuine stopped exponentials recover the real-valued exit clock,
proving its almost sure measurability directly. -/
theorem aemeasurable_boundedDriftedIntervalExit_coe (hB : IsBrownianReal B μ)
    (x d r : ℝ) (T : ℝ≥0) :
    AEMeasurable (fun ω => (boundedDriftedIntervalExit B x d r T ω : ℝ)) μ := by
  have hp := (integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB 1 x d r T).1.aemeasurable
  have hn := (integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB (-1) x d r T).1.aemeasurable
  have hm := (Real.measurable_log.comp_aemeasurable (hp.mul hn)).neg
  convert hm using 1
  funext ω
  dsimp only [actualBrownianExponentialWith, Function.comp_apply, Pi.mul_apply, Pi.neg_apply]
  rw [← Real.exp_add, Real.log_exp]
  ring

/-- The stopped Brownian value, hence the actual drifted exit endpoint, is
almost surely measurable with no separate endpoint-selection assumption. -/
theorem aemeasurable_driftedExitPosition (hB : IsBrownianReal B μ)
    (x d r : ℝ) (T : ℝ≥0) : AEMeasurable (driftedExitPosition B x d r T) μ := by
  have hp := (integral_actualBrownianExponentialWith_boundedDriftedIntervalExit hB 1 x d r T).1.aemeasurable
  have ht := aemeasurable_boundedDriftedIntervalExit_coe hB x d r T
  have hm := (((Real.measurable_log.comp_aemeasurable hp).add (ht.div_const 2)).const_add x).add (ht.const_mul d)
  convert hm using 1
  funext ω
  dsimp only [driftedExitPosition, actualBrownianExponentialWith, Function.comp_apply, Pi.add_apply]
  rw [Real.log_exp]
  ring

end BrownianAffine
