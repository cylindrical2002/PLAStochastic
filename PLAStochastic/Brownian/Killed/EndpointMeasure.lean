import PLAStochastic.Brownian.Killed.StoppedSineMoments

/-! The actual subprobability endpoint measure of Brownian motion before interval exit. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The endpoint pushforward of the actual survival event; no density is inserted into this definition. -/
def killedBrownianMeasure (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (x r : ℝ) (T : ℝ≥0) : Measure ℝ :=
  (μ.restrict {ω | boundedIntervalExit B x r T ω = T}).map (fun ω => x + B T ω)

instance killedBrownianMeasure_isFiniteMeasure [IsFiniteMeasure μ] (x r : ℝ) (T : ℝ≥0) :
    IsFiniteMeasure (killedBrownianMeasure B μ x r T) := by
  unfold killedBrownianMeasure
  infer_instance

theorem killedBrownianMeasure_le_gaussian (hB : IsBrownianReal B μ) (x r : ℝ) (T : ℝ≥0) :
    killedBrownianMeasure B μ x r T ≤ gaussianReal x T := by
  have hf : AEMeasurable (fun ω => x + B T ω) μ := (hB.aemeasurable T).const_add x
  have hX : HasLaw (fun ω => x + B T ω) (gaussianReal x T) μ := by
    simpa only [zero_add] using gaussianReal_const_add (hB.toIsPreBrownianReal.hasLaw_eval T) x
  unfold killedBrownianMeasure
  calc
    _ = (μ.restrict {ω | boundedIntervalExit B x r T ω = T}).map (hf.mk _) :=
      Measure.map_congr hf.ae_eq_mk.restrict
    _ ≤ μ.map (hf.mk _) := Measure.map_mono Measure.restrict_le_self hf.measurable_mk
    _ = μ.map (fun ω => x + B T ω) := Measure.map_congr hf.ae_eq_mk.symm
    _ = _ := hX.map_eq

theorem killedBrownianMeasure_absolutelyContinuous (hB : IsBrownianReal B μ)
    (x r : ℝ) {T : ℝ≥0} (hT : T ≠ 0) :
    killedBrownianMeasure B μ x r T ≪ volume :=
  (Measure.absolutelyContinuous_of_le (killedBrownianMeasure_le_gaussian hB x r T)).trans
    (gaussianReal_absolutelyContinuous x hT)

theorem killedBrownianMeasure_singleton (hB : IsBrownianReal B μ)
    (x r z : ℝ) {T : ℝ≥0} (hT : T ≠ 0) :
    killedBrownianMeasure B μ x r T {z} = 0 :=
  killedBrownianMeasure_absolutelyContinuous hB x r hT (by simp)

/-- Surviving paths have actual endpoints in the closed interval. -/
theorem killedBrownianMeasure_ae_mem (hB : IsBrownianReal B μ) {x r : ℝ}
    (hx : x ∈ Icc 0 r) (T : ℝ≥0) :
    ∀ᵐ z ∂killedBrownianMeasure B μ x r T, z ∈ Icc 0 r := by
  have hf : AEMeasurable (fun ω => x + B T ω) μ := (hB.aemeasurable T).const_add x
  unfold killedBrownianMeasure
  apply (ae_map_iff hf.restrict (p := fun z => z ∈ Icc 0 r) measurableSet_Icc).mpr
  rw [ae_restrict_iff'₀ (nullMeasurableSet_intervalSurvival hB x r T)]
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hω h0 hsurv
  have hstart : x + B 0 ω ∈ Icc (-(0 : ℝ)) r := by simpa [h0] using hx
  have hb := boundedOpenExitTime_mem_strip (X := fun t ω => x + B t ω)
    (a := r) (b := 0) (T := T) (hω.const_add x) hstart
  change boundedIntervalExit B x r T ω = T at hsurv
  change x + B (boundedIntervalExit B x r T ω) ω ∈ Icc (-0) r at hb
  simpa only [hsurv, neg_zero] using hb

theorem killedBrownianMeasure_compl_Icc (hB : IsBrownianReal B μ) {x r : ℝ}
    (hx : x ∈ Icc 0 r) (T : ℝ≥0) :
    killedBrownianMeasure B μ x r T (Icc 0 r)ᶜ = 0 :=
  ae_iff.mp (killedBrownianMeasure_ae_mem hB hx T)

/-- The genuine killed endpoint measure has the exact Dirichlet sine moments. -/
theorem integral_sine_killedBrownianMeasure (hB : IsBrownianReal B μ) {x r : ℝ}
    (hr : 0 < r) (hx : x ∈ Icc 0 r) (T : ℝ≥0) (n : ℕ) :
    (∫ z, Real.sin (heatFrequency r n * z) ∂killedBrownianMeasure B μ x r T) =
      Real.exp (-(heatFrequency r n ^ 2) * (T : ℝ) / 2) * Real.sin (heatFrequency r n * x) := by
  have hf : AEMeasurable (fun ω => x + B T ω) μ := (hB.aemeasurable T).const_add x
  unfold killedBrownianMeasure
  have hsin : AEStronglyMeasurable (fun z : ℝ => Real.sin (heatFrequency r n * z))
      ((μ.restrict {ω | boundedIntervalExit B x r T ω = T}).map (fun ω => x + B T ω)) := by
    fun_prop
  rw [integral_map hf.restrict hsin,
    ← integral_indicator₀ (nullMeasurableSet_intervalSurvival hB x r T)]
  convert integral_intervalKilledSine hB hr hx T n using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by simp [intervalKilledSine, Set.indicator]

end BrownianAffine
