import PLAStochastic.Brownian.Killed.KernelParts
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.DirichletHeatKernel.SineMomentUniqueness
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
Identification of the analytic Dirichlet series with the actual Brownian endpoint
measure restricted to interval survival. Positivity is a consequence of identification,
not an assumption or a definition of the killed endpoint law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem killedBrownianMeasure_ae_mem_Ioo (hB : IsBrownianReal B μ) {x r : ℝ}
    (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : T ≠ 0) :
    ∀ᵐ z ∂killedBrownianMeasure B μ x r T, z ∈ Ioo 0 r :=
  ae_mem_Ioo_of_ae_mem_Icc_of_ac (killedBrownianMeasure_ae_mem hB hx T)
    (killedBrownianMeasure_absolutelyContinuous hB x r hT)

/-- Equality of the actual endpoint measure plus the negative part with the positive part. -/
theorem killedBrownianMeasure_add_negative_eq_positive (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T) :
    killedBrownianMeasure B μ x r T + heatNegativeMeasure r T x = heatPositiveMeasure r T x := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (heatNegativeMeasure r T x) :=
    heatNegativeMeasure_isFiniteMeasure hr (show (0 : ℝ) < T from hT) x
  have : IsFiniteMeasure (heatPositiveMeasure r T x) :=
    heatPositiveMeasure_isFiniteMeasure hr (show (0 : ℝ) < T from hT) x
  refine measure_eq_of_sine_moments hr ?_ (heatPositiveMeasure_ae_mem_Ioo r T x) ?_
  · exact (ae_add_measure_iff).mpr ⟨killedBrownianMeasure_ae_mem_Ioo hB hx hT.ne',
      heatNegativeMeasure_ae_mem_Ioo r T x⟩
  · exact integral_sine_killed_add_negative_eq_positive hB hr hx hT

theorem heatNegativeMeasure_eq_zero (hB : IsBrownianReal B μ) {x r : ℝ}
    (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T) :
    heatNegativeMeasure r T x = 0 :=
  heatNegativeMeasure_eq_zero_of_add_eq hr (show (0 : ℝ) < T from hT)
    (killedBrownianMeasure_add_negative_eq_positive hB hr hx hT)

/-- The actual interval-survival endpoint distribution has the Dirichlet heat density. -/
theorem killedBrownianMeasure_eq_heatDensity (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T) :
    killedBrownianMeasure B μ x r T = (volume.restrict (Icc 0 r)).withDensity
      (fun z => ENNReal.ofReal (dirichletHeatKernel r T x z)) := by
  have h := killedBrownianMeasure_add_negative_eq_positive hB hr hx hT
  rw [heatNegativeMeasure_eq_zero hB hr hx hT, add_zero] at h
  exact h.trans (heatPositiveMeasure_eq_density r T x)

/-- The analytic series is nonnegative, deduced from its genuine killed-measure identity. -/
theorem dirichletHeatKernel_nonneg (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T)
    {z : ℝ} (hz : z ∈ Icc 0 r) : 0 ≤ dirichletHeatKernel r T x z := by
  have hzero := heatNegativeMeasure_eq_zero hB hr hx hT
  have hm := (continuous_heatNegativePart hr (show (0 : ℝ) < T from hT) x).measurable
  have hae : (fun z => ENNReal.ofReal (heatNegativePart r T x z)) =ᵐ[volume.restrict (Icc 0 r)] 0 :=
    (withDensity_eq_zero_iff hm.ennreal_ofReal.aemeasurable).mp hzero
  have hae' : heatNegativePart r T x =ᵐ[volume.restrict (Icc 0 r)] (fun _ => (0 : ℝ)) := by
    filter_upwards [hae] with z hz
    exact le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (heatNegativePart_nonneg r T x z)
  have hpoint := Measure.eqOn_Icc_of_ae_eq volume hr.ne hae'
    (continuous_heatNegativePart hr (show (0 : ℝ) < T from hT) x).continuousOn
    continuous_const.continuousOn hz
  have hle : -dirichletHeatKernel r T x z ≤ heatNegativePart r T x z := le_max_left _ _
  rw [hpoint] at hle
  linarith

/-- The survival subprobability, with no asserted sign or normalization supplied as input. -/
theorem killedBrownianMeasure_apply_eq_heatIntegral (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T)
    {s : Set ℝ} (hs : MeasurableSet s) :
    killedBrownianMeasure B μ x r T s =
      ∫⁻ z in s, ENNReal.ofReal (dirichletHeatKernel r T x z) ∂volume.restrict (Icc 0 r) := by
  rw [killedBrownianMeasure_eq_heatDensity hB hr hx hT, withDensity_apply _ hs]

end BrownianAffine
