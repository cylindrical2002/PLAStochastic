import PLAStochastic.Brownian.Construction.CountableObservations
import Mathlib.Tactic

/-!
# Brownian time inversion, including continuity at zero

The zero-time modulus is a measurable event on a countable dense set of times.
Equal countable observation laws transfer this event to the inverted process.
Continuity at positive times then extends its bounds to every small time.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

/-- A fixed countable dense set in the whole nonnegative time axis. -/
def inversionSampleSet : Set ℝ≥0 :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose

theorem inversionSampleSet_countable : inversionSampleSet.Countable :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.1

theorem inversionSampleSet_dense : Dense inversionSampleSet :=
  (TopologicalSpace.exists_countable_dense ℝ≥0).choose_spec.2

abbrev InversionSample := inversionSampleSet

instance : Countable InversionSample := inversionSampleSet_countable.to_subtype

/-- Uniform control on every sufficiently small sampled time, for each accuracy. -/
def sampledZeroModulus (g : InversionSample → ℝ) : Prop :=
  ∀ k : ℕ, ∃ m : ℕ, ∀ q : InversionSample,
    (q.1 : ℝ) < 1 / (m + 1 : ℝ) → |g q| ≤ 1 / (k + 1 : ℝ)

theorem measurableSet_sampledZeroModulus : MeasurableSet {g | sampledZeroModulus g} := by
  simp only [sampledZeroModulus, Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iInter
  intro q
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le (measurable_pi_apply q).abs measurable_const

private theorem nnreal_dist_zero (t : ℝ≥0) : dist t 0 = (t : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  simp

theorem sampledZeroModulus_of_continuousAt {X : ℝ≥0 → ℝ}
    (hX : ContinuousAt X 0) (h0 : X 0 = 0) :
    sampledZeroModulus (fun q : InversionSample => X q.1) := by
  intro k
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hX
    (1 / (k + 1 : ℝ)) (by positivity)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun q hq => le_of_lt ?_⟩
  have ht := hnear (by simpa only [nnreal_dist_zero] using hq.trans hm)
  simpa [h0, Real.dist_eq] using ht

/-- A bound on dense sample times extends to a positive continuity point. -/
theorem abs_le_of_sampledZeroModulus {X : ℝ≥0 → ℝ} {t : ℝ≥0} {k m : ℕ}
    (hX : ContinuousAt X t)
    (hm : ∀ q : InversionSample, (q.1 : ℝ) < 1 / (m + 1 : ℝ) →
      |X q.1| ≤ 1 / (k + 1 : ℝ))
    (ht : (t : ℝ) < 1 / (m + 1 : ℝ)) :
    |X t| ≤ 1 / (k + 1 : ℝ) := by
  have : NeBot (𝓝[inversionSampleSet] t) :=
    mem_closure_iff_nhdsWithin_neBot.mp (inversionSampleSet_dense t)
  apply le_of_tendsto (hX.abs.continuousWithinAt (s := inversionSampleSet)).tendsto
  have hnear : ∀ᶠ u : ℝ≥0 in 𝓝 t, (u : ℝ) < 1 / (m + 1 : ℝ) :=
    (continuous_subtype_val : Continuous (fun u : ℝ≥0 => (u : ℝ))).continuousAt
      (isOpen_Iio.mem_nhds ht)
  filter_upwards [self_mem_nhdsWithin,
    hnear.filter_mono nhdsWithin_le_nhds] with u hu hsmall
  exact hm ⟨u, hu⟩ hsmall

/-- The full dense modulus and positive-time continuity imply continuity at zero. -/
theorem continuousAt_zero_of_sampledZeroModulus {X : ℝ≥0 → ℝ}
    (hX : ∀ t : ℝ≥0, t ≠ 0 → ContinuousAt X t) (h0 : X 0 = 0)
    (hm : sampledZeroModulus (fun q : InversionSample => X q.1)) :
    ContinuousAt X 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨m, hm⟩ := hm k
  refine ⟨1 / (m + 1 : ℝ), by positivity, fun {t} ht => ?_⟩
  by_cases ht0 : t = 0
  · simpa [ht0] using hε
  · have hbound := abs_le_of_sampledZeroModulus (hX t ht0) hm
      (by simpa only [nnreal_dist_zero] using ht)
    simpa [h0, Real.dist_eq] using hbound.trans_lt hk

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- Real Brownian time inversion, with its algebraic zero value at time zero. -/
def timeInvertedProcess (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  (t : ℝ) * B (1 / t) ω

omit [MeasurableSpace Ω] in
theorem timeInvertedProcess_zero (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    timeInvertedProcess B 0 ω = 0 := by
  simp [timeInvertedProcess]

omit [MeasurableSpace Ω] in
theorem continuousAt_timeInvertedProcess_of_ne_zero {ω : Ω}
    (hω : Continuous (B · ω)) {t : ℝ≥0} (ht : t ≠ 0) :
    ContinuousAt (timeInvertedProcess B · ω) t := by
  apply continuous_subtype_val.continuousAt.mul
  exact hω.continuousAt.comp (continuousAt_const.div continuousAt_id ht)

theorem ae_sampledZeroModulus_timeInvertedProcess (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, sampledZeroModulus
      (fun q : InversionSample => timeInvertedProcess B q.1 ω) := by
  have hlaw := identDistrib_countable_observations hB.toIsPreBrownianReal
    hB.toIsPreBrownianReal.inv (fun q : InversionSample => q.1)
  apply hlaw.ae_snd measurableSet_sampledZeroModulus
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hω h0
  exact sampledZeroModulus_of_continuousAt hω.continuousAt h0

/-- Time inversion preserves Brownian motion, including almost-sure continuity
at zero. No strong-law or continuity assumption on the inverted process is used. -/
theorem isBrownianReal_timeInversion (hB : IsBrownianReal B μ) :
    IsBrownianReal (timeInvertedProcess B) μ := by
  refine ⟨hB.toIsPreBrownianReal.inv, ?_⟩
  filter_upwards [hB.cont, ae_sampledZeroModulus_timeInvertedProcess hB] with ω hω hm
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t = 0
  · subst t
    exact continuousAt_zero_of_sampledZeroModulus
      (fun t ht => continuousAt_timeInvertedProcess_of_ne_zero hω ht)
      (timeInvertedProcess_zero B ω) hm
  · exact continuousAt_timeInvertedProcess_of_ne_zero hω ht

end BrownianAffine
