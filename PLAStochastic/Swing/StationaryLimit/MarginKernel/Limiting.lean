import PLAStochastic.Swing.Ladder.Drift.LawFamily
import PLAStochastic.Swing.StationaryLimit.Slope.Kernel

/-! # The limiting margin kernel `eq:limitingmarginkernel`

Theorem 4.3 first samples the limiting slope `A_r` of `eq:leadingslope` and then,
at the realised drift, the equilibrium overshoot `O_a` of
`eq:equilibriumovershoot`; the new margin is `A_r - O_{A_r}`.  Both stages are
already available as measures.  This file turns the second stage into a genuine
probability kernel in the drift and composes the two, so that `K` becomes an
object of the library rather than a description.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The equilibrium overshoot density of `eq:equilibriumovershoot` at drift `a`
and level `o`. -/
def swingEquilibriumDensity (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a o : ℝ) : ℝ≥0∞ :=
  gaussianAscendingLadderLaw X μ a (Ioi o) / ladderMeanENN (gaussianAscendingLadderLaw X μ a)

theorem swingEquilibriumDensity_joint_measurable [SFinite μ] (hX : ∀ n, Measurable (X n)) :
    Measurable (fun q : ℝ × ℝ => swingEquilibriumDensity X μ q.1 q.2) :=
  (gaussianAscendingLadderLaw_tail_joint_measurable hX).div
    ((gaussianAscendingLadderLaw_mean_measurable hX).comp measurable_fst)

/-- The equilibrium overshoot law, read through the reflection `o ↦ a - o` that
turns an overshoot into the next margin. -/
def swingOvershootMeasure (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ) : Measure ℝ :=
  (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ a)).map (fun o => a - o)

omit [MeasurableSpace Ω] in
theorem measurable_const_sub_self (a : ℝ) : Measurable (fun o : ℝ => a - o) :=
  measurable_const.sub measurable_id

theorem swingOvershootMeasure_apply (X : ℕ → Ω → ℝ) (μ : Measure Ω) (a : ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    swingOvershootMeasure X μ a s =
      ∫⁻ o in ((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ), swingEquilibriumDensity X μ a o := by
  rw [swingOvershootMeasure, Measure.map_apply (measurable_const_sub_self a) hs,
    equilibriumOvershootLaw_apply _ (hs.preimage (measurable_const_sub_self a))]
  rfl

theorem swingOvershootMeasure_isProbability
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (swingOvershootMeasure X μ a) := by
  have := gaussianAscendingLadderEquilibrium_isProbability hX hi hG ha
  exact Measure.isProbabilityMeasure_map
    (measurable_const_sub_self a).aemeasurable

theorem swingOvershootMeasure_measurable [SFinite μ] (hX : ∀ n, Measurable (X n)) :
    Measurable (fun a : ℝ => swingOvershootMeasure X μ a) := by
  refine Measure.measurable_of_measurable_coe _ (fun s hs => ?_)
  set A : Set (ℝ × ℝ) := {q : ℝ × ℝ | q.1 - q.2 ∈ s ∧ 0 ≤ q.2} with hA
  have hAmeas : MeasurableSet A := by
    have h1 : MeasurableSet {q : ℝ × ℝ | q.1 - q.2 ∈ s} :=
      hs.preimage (measurable_fst.sub measurable_snd)
    have h2 : MeasurableSet {q : ℝ × ℝ | 0 ≤ q.2} :=
      measurableSet_le measurable_const measurable_snd
    exact h1.inter h2
  have hG : Measurable (fun q : ℝ × ℝ =>
      Set.indicator A (fun q => swingEquilibriumDensity X μ q.1 q.2) q) :=
    (swingEquilibriumDensity_joint_measurable hX).indicator hAmeas
  have heq : (fun a : ℝ => swingOvershootMeasure X μ a s) =
      fun a : ℝ => ∫⁻ o, Set.indicator A (fun q => swingEquilibriumDensity X μ q.1 q.2) (a, o) := by
    funext a
    rw [swingOvershootMeasure_apply X μ a hs]
    have hslice : ∀ o : ℝ,
        Set.indicator A (fun q => swingEquilibriumDensity X μ q.1 q.2) (a, o) =
          Set.indicator (((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ))
            (fun o => swingEquilibriumDensity X μ a o) o := by
      intro o
      by_cases hmem : (a, o) ∈ A
      · have hmem' : o ∈ ((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ) := ⟨hmem.1, hmem.2⟩
        rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem']
      · have hmem' : o ∉ ((fun o : ℝ => a - o) ⁻¹' s) ∩ Ici (0 : ℝ) := by
          intro hc
          exact hmem ⟨hc.1, hc.2⟩
        rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem']
    simp_rw [hslice]
    exact (lintegral_indicator
      ((hs.preimage (measurable_const_sub_self a)).inter measurableSet_Ici) _).symm
  rw [heq]
  exact hG.lintegral_prod_right'

/-- The second stage of `eq:limitingmarginkernel` as a probability kernel in the drift. -/
def swingOvershootKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) [SFinite μ] : Kernel ℝ ℝ :=
  if h : ∀ n, Measurable (X n) then
    { toFun := fun a => swingOvershootMeasure X μ a
      measurable' := swingOvershootMeasure_measurable h }
  else 0

theorem swingOvershootKernel_apply [SFinite μ] (hX : ∀ n, Measurable (X n)) (a : ℝ) :
    swingOvershootKernel X μ a = swingOvershootMeasure X μ a := by
  rw [swingOvershootKernel, dif_pos hX]
  rfl

/-- `eq:limitingmarginkernel`: the limiting margin kernel `K`. -/
def swingMarginKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) [SFinite μ] : Kernel ℝ ℝ :=
  swingOvershootKernel X μ ∘ₖ swingSlopeKernel X μ

theorem swingMarginKernel_apply [SFinite μ] (hX : ∀ n, Measurable (X n)) (r : ℝ)
    {s : Set ℝ} (hs : MeasurableSet s) :
    swingMarginKernel X μ r s = ∫⁻ a, swingOvershootMeasure X μ a s ∂swingSlopeKernel X μ r := by
  rw [swingMarginKernel, Kernel.comp_apply' _ _ _ hs]
  exact lintegral_congr fun a => by rw [swingOvershootKernel_apply hX a]

end SwingRepair
