import Mathlib.MeasureTheory.Integral.Indicator

/-! # Sign probabilities under almost sure convergence

If `J_E → I` almost surely, `P(I = 0) = 0` and the thresholds `c_E` tend to `0`, then

`P(J_E > c_E) → P(I > 0)`  and  `P(J_E < -c_E) → P(I < 0)`.

This turns the almost sure convergence of the discrete selection area at the cut and the
absence of Brownian ties into the two mixture weights `θ` and `1 - θ` of the entrance law. The
thresholds absorb the deterministic error between the area at the cut and the area at the end
of the segment.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SwingRepair

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {l : Filter ι} [l.IsCountablyGenerated]

/-- Measures of null-measurable sets whose indicators converge almost surely converge. -/
theorem tendsto_measure_of_ae_eventually_iff {As : ι → Set Ω} {A : Set Ω}
    (hAs : ∀ i, NullMeasurableSet (As i) μ) (hA : NullMeasurableSet A μ)
    (h : ∀ᵐ ω ∂μ, ∀ᶠ i in l, ω ∈ As i ↔ ω ∈ A) :
    Tendsto (fun i => μ (As i)) l (𝓝 (μ A)) := by
  simp_rw [← lintegral_indicator_one₀ (hAs _), ← lintegral_indicator_one₀ hA]
  refine tendsto_lintegral_filter_of_dominated_convergence' 1
    (Eventually.of_forall fun i => aemeasurable_const.indicator₀ (hAs i))
    (Eventually.of_forall fun i => ae_of_all _ fun ω =>
      Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => zero_le))
    (by simp) ?_
  filter_upwards [h] with ω hω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hω] with i hi
  by_cases hωA : ω ∈ A
  · rw [Set.indicator_of_mem hωA, Set.indicator_of_mem (hi.mpr hωA)]
  · rw [Set.indicator_of_notMem hωA, Set.indicator_of_notMem (fun h => hωA (hi.mp h))]

/-- **Sign weights.**  If `J_E → I` almost surely, `P(I = 0) = 0` and `c_E → 0`, then
`P(J_E > c_E) → P(I > 0)` and `P(J_E < -c_E) → P(I < 0)`. -/
theorem tendsto_measure_sign_of_ae {I : Ω → ℝ} {J : ι → Ω → ℝ} {c : ι → ℝ}
    (hI : AEMeasurable I μ) (hJ : ∀ i, AEMeasurable (J i) μ) (hc : Tendsto c l (𝓝 0))
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun i => J i ω) l (𝓝 (I ω))) (h0 : μ {ω | I ω = 0} = 0) :
    Tendsto (fun i => μ {ω | c i < J i ω}) l (𝓝 (μ {ω | 0 < I ω})) ∧
      Tendsto (fun i => μ {ω | J i ω < -c i}) l (𝓝 (μ {ω | I ω < 0})) := by
  have hne : ∀ᵐ ω ∂μ, I ω ≠ 0 := by
    rw [ae_iff]
    simpa only [ne_eq, not_not] using h0
  constructor
  · refine tendsto_measure_of_ae_eventually_iff
      (fun i => nullMeasurableSet_lt aemeasurable_const (hJ i))
      (nullMeasurableSet_lt aemeasurable_const hI) ?_
    filter_upwards [hconv, hne] with ω hω hω0
    rcases lt_or_gt_of_ne hω0 with hlt | hgt
    · have h1 : ∀ᶠ i in l, J i ω < I ω / 2 := hω.eventually (gt_mem_nhds (by linarith))
      have h2 : ∀ᶠ i in l, I ω / 2 < c i := hc.eventually (lt_mem_nhds (by linarith))
      filter_upwards [h1, h2] with i hi1 hi2
      constructor
      · intro h; exact absurd h (by simp only [not_lt]; linarith)
      · intro h; exact absurd h (by simp only [not_lt]; linarith)
    · have h1 : ∀ᶠ i in l, I ω / 2 < J i ω := hω.eventually (lt_mem_nhds (by linarith))
      have h2 : ∀ᶠ i in l, c i < I ω / 2 := hc.eventually (gt_mem_nhds (by linarith))
      filter_upwards [h1, h2] with i hi1 hi2
      constructor
      · intro _; exact hgt
      · intro _; show c i < J i ω; linarith
  · refine tendsto_measure_of_ae_eventually_iff
      (fun i => nullMeasurableSet_lt (hJ i) aemeasurable_const)
      (nullMeasurableSet_lt hI aemeasurable_const) ?_
    filter_upwards [hconv, hne] with ω hω hω0
    rcases lt_or_gt_of_ne hω0 with hlt | hgt
    · have h1 : ∀ᶠ i in l, J i ω < I ω / 2 := hω.eventually (gt_mem_nhds (by linarith))
      have h2 : ∀ᶠ i in l, c i < -(I ω / 2) := hc.eventually (gt_mem_nhds (by linarith))
      filter_upwards [h1, h2] with i hi1 hi2
      constructor
      · intro _; exact hlt
      · intro _; show J i ω < -c i; linarith
    · have h1 : ∀ᶠ i in l, I ω / 2 < J i ω := hω.eventually (lt_mem_nhds (by linarith))
      have h2 : ∀ᶠ i in l, -(I ω / 2) < c i := hc.eventually (lt_mem_nhds (by linarith))
      filter_upwards [h1, h2] with i hi1 hi2
      constructor
      · intro h; exact absurd h (by simp only [not_lt]; linarith)
      · intro h; exact absurd h (by simp only [not_lt]; linarith)

end SwingRepair
