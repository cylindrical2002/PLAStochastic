import PLAStochastic.Swing.SecondSegment.Coefficient.MarginLimit
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakLimit

/-! # A continuous window on a negative compact

`second-coefficient.md`, §3.  The transfer argument integrates over the
negative compact `[-M, -δ]` against varying entrance laws.  Instead of the
indicator of the compact, whose endpoints would need separate atom control, a
continuous window `ψ` equal to `1` on `[-M, -δ]` and vanishing outside
`(-M-1, -δ/2)` is used.  Then `ℓψ` is bounded and continuous, so weak
convergence applies to it directly, and the uniform convergence C2.2 on
`[-M-1, -δ/2]` controls `∫ (g_E/E - ℓ) ψ` uniformly in the law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open KernelLimit
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The window: `1` on `[-M,-δ]`, `0` outside `(-M-1,-δ/2)`, piecewise linear. -/
def secondSegmentWindow (δ M r : ℝ) : ℝ :=
  min (clamp01 (r + M + 1)) (clamp01 (-(2*r + δ)/δ))

theorem secondSegmentWindow_nonneg (δ M r : ℝ) : 0 ≤ secondSegmentWindow δ M r :=
  le_min (clamp01_nonneg _) (clamp01_nonneg _)

theorem secondSegmentWindow_le_one (δ M r : ℝ) : secondSegmentWindow δ M r ≤ 1 :=
  (min_le_left _ _).trans (clamp01_le_one _)

theorem continuous_secondSegmentWindow (δ M : ℝ) : Continuous (secondSegmentWindow δ M) :=
  (continuous_clamp01.comp ((continuous_id.add continuous_const).add continuous_const)).min
    (continuous_clamp01.comp
      (((continuous_const.mul continuous_id).add continuous_const).neg.div_const δ))

theorem secondSegmentWindow_eq_one {δ M r : ℝ} (hδ : 0 < δ) (h1 : -M ≤ r) (h2 : r ≤ -δ) :
    secondSegmentWindow δ M r = 1 := by
  unfold secondSegmentWindow
  rw [clamp01_eq_one (by linarith), clamp01_eq_one, min_self]
  rw [le_div_iff₀ hδ]
  linarith

theorem secondSegmentWindow_eq_zero_left {δ M r : ℝ} (h : r ≤ -M - 1) :
    secondSegmentWindow δ M r = 0 := by
  unfold secondSegmentWindow
  rw [clamp01_eq_zero (by linarith)]
  exact min_eq_left (clamp01_nonneg _)

theorem secondSegmentWindow_eq_zero_right {δ M r : ℝ} (hδ : 0 < δ) (h : -δ/2 ≤ r) :
    secondSegmentWindow δ M r = 0 := by
  unfold secondSegmentWindow
  rw [clamp01_eq_zero (t := -(2*r + δ)/δ)]
  · exact min_eq_right (clamp01_nonneg _)
  · apply div_nonpos_of_nonpos_of_nonneg _ hδ.le
    linarith

theorem secondSegmentWindow_eq_zero_of_notMem {δ M r : ℝ} (hδ : 0 < δ)
    (h : r ∉ Icc (-M-1) (-δ/2)) : secondSegmentWindow δ M r = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact secondSegmentWindow_eq_zero_left h.le
  · exact secondSegmentWindow_eq_zero_right hδ h.le

/-! ### The kernel times the window -/

theorem continuous_secondSegmentLimitKernel_mul_window
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {δ : ℝ} (hδ : 0 < δ) (M : ℝ) :
    Continuous (fun r => secondSegmentLimitKernel X μ r * secondSegmentWindow δ M r) := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : r < 0
  · have hℓ : ContinuousAt (secondSegmentLimitKernel X μ) r :=
      (secondSegmentLimitKernel_continuousOn hX hi hG).continuousAt (Iio_mem_nhds hr)
    exact hℓ.mul (continuous_secondSegmentWindow δ M).continuousAt
  · have hev : (fun r => secondSegmentLimitKernel X μ r * secondSegmentWindow δ M r) =ᶠ[𝓝 r]
        fun _ => (0 : ℝ) := by
      filter_upwards [Ioi_mem_nhds (show -δ/2 < r by linarith)] with s hs
      rw [secondSegmentWindow_eq_zero_right hδ (le_of_lt hs), mul_zero]
    exact continuousAt_const.congr hev.symm

theorem abs_secondSegmentLimitKernel_mul_window_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {δ : ℝ} (hδ : 0 < δ) (M r : ℝ) :
    |secondSegmentLimitKernel X μ r * secondSegmentWindow δ M r| ≤ 4/δ := by
  have h4 : 0 ≤ 4/δ := by positivity
  by_cases hr : -δ/2 ≤ r
  · rw [secondSegmentWindow_eq_zero_right hδ hr, mul_zero, abs_zero]
    exact h4
  · have hr' : r < -δ/2 := lt_of_not_ge hr
    have hneg : r < 0 := by linarith
    have hℓ0 := secondSegmentLimitKernel_nonneg hX hi hG r
    have hℓ := secondSegmentLimitKernel_le hX hi hG hneg
    have hψ0 := secondSegmentWindow_nonneg δ M r
    have hψ1 := secondSegmentWindow_le_one δ M r
    rw [abs_of_nonneg (mul_nonneg hℓ0 hψ0)]
    have habs : δ/2 ≤ |r| := by rw [abs_of_neg hneg]; linarith
    have h2 : 2/|r| ≤ 4/δ := by
      rw [div_le_div_iff₀ (abs_pos.mpr hneg.ne) hδ]
      nlinarith
    calc secondSegmentLimitKernel X μ r * secondSegmentWindow δ M r
        ≤ secondSegmentLimitKernel X μ r := mul_le_of_le_one_right hℓ0 hψ1
      _ ≤ 2/|r| := hℓ
      _ ≤ 4/δ := h2

/-- The window part of the transfer: uniform closeness on the support of `ψ`
controls the windowed integrals for every probability law. -/
theorem abs_integral_window_sub_le {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {f g : ℝ → ℝ} {δ M η : ℝ} (hδ : 0 < δ) (hη : 0 ≤ η)
    (hf : Integrable (fun r => f r * secondSegmentWindow δ M r) ρ)
    (hg : Integrable (fun r => g r * secondSegmentWindow δ M r) ρ)
    (hclose : ∀ r ∈ Icc (-M-1) (-δ/2), |f r - g r| ≤ η) :
    |(∫ r, f r * secondSegmentWindow δ M r ∂ρ) - ∫ r, g r * secondSegmentWindow δ M r ∂ρ| ≤ η := by
  rw [← integral_sub hf hg]
  have hpt : ∀ r, |f r * secondSegmentWindow δ M r - g r * secondSegmentWindow δ M r| ≤ η := by
    intro r
    rw [← sub_mul, abs_mul, abs_of_nonneg (secondSegmentWindow_nonneg δ M r)]
    by_cases hr : r ∈ Icc (-M-1) (-δ/2)
    · exact (mul_le_of_le_one_right (abs_nonneg _) (secondSegmentWindow_le_one δ M r)).trans
        (hclose r hr)
    · rw [secondSegmentWindow_eq_zero_of_notMem hδ hr, mul_zero]
      exact hη
  calc |∫ r, (f r * secondSegmentWindow δ M r - g r * secondSegmentWindow δ M r) ∂ρ|
      ≤ ∫ r, |f r * secondSegmentWindow δ M r - g r * secondSegmentWindow δ M r| ∂ρ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _r, η ∂ρ := integral_mono (hf.sub hg).abs (integrable_const _) hpt
    _ = η := by simp

end SwingRepair
