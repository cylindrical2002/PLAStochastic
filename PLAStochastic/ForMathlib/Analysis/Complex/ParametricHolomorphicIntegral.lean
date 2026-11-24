import PLAStochastic.ForMathlib.Analysis.Complex.Osgood
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Measurability and holomorphy of parameter integrals of holomorphic families

For a family `f a : ℂ → ℂ` of functions holomorphic on an open set `U` for almost every `a`:

* `aestronglyMeasurable_iteratedDeriv_of_ae_differentiableOn`: if every value `a ↦ f a t`
  (`t ∈ U`) is a.e. strongly measurable, so is every derivative `a ↦ (f a)⁽ⁿ⁾(t)` (limits of
  difference quotients);
* `differentiableOn_integral_of_dominated`: if moreover `‖f a z‖ ≤ g a W(z)` on `U` with `g`
  integrable and `W ≥ 0` continuous, then `z ↦ ∫ f a z` is holomorphic on `U` (Cauchy estimates
  dominate the derivatives on small discs).
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

/-- Iterated derivatives of a function holomorphic on an open set are holomorphic there. -/
theorem differentiableOn_iteratedDeriv_open {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv hU

/-- Derivatives of an a.e. holomorphic family with measurable values are measurable. -/
theorem aestronglyMeasurable_iteratedDeriv_of_ae_differentiableOn {Λ : Type*}
    [MeasurableSpace Λ] {μ : Measure Λ} {f : Λ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : ∀ᵐ a ∂μ, DifferentiableOn ℂ (f a) U)
    (hm : ∀ t ∈ U, AEStronglyMeasurable (fun a => f a t) μ) (n : ℕ) :
    ∀ t ∈ U, AEStronglyMeasurable (fun a => iteratedDeriv n (f a) t) μ := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hm
  | succ n ih =>
    intro t ht
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hU t ht
    obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ (half_pos hρ)
    set h : ℕ → ℂ := fun k => ((ρ / 2 / (k + 1) : ℝ) : ℂ) with hh
    have hmem : ∀ k, t + h k ∈ U := by
      intro k
      apply hball
      rw [mem_ball, dist_self_add_left, hh, Complex.norm_real, Real.norm_of_nonneg
        (by positivity)]
      calc ρ / 2 / ((k : ℝ) + 1) ≤ ρ / 2 :=
            div_le_self (by positivity) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
        _ < ρ := half_lt_self hρ
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun k a => (h k)⁻¹ • (iteratedDeriv n (f a) (t + h k) - iteratedDeriv n (f a) t))
      (fun k => by
        have h1 := ((ih _ (hmem k)).sub (ih t ht)).const_smul (h k)⁻¹
        exact h1) ?_
    filter_upwards [hd] with a ha
    have hdiff : DifferentiableAt ℂ (iteratedDeriv n (f a)) t :=
      ((differentiableOn_iteratedDeriv_open hU ha n) t ht).differentiableAt (hU.mem_nhds ht)
    rw [iteratedDeriv_succ]
    exact hdiff.hasDerivAt.tendsto_slope_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hne⟩)

/-- Integrability of a dominated family at one point of the domain. -/
theorem integrable_of_dominated_param {Λ : Type*} [MeasurableSpace Λ] {μ : Measure Λ}
    {f : Λ → ℂ → ℂ} {U : Set ℂ} {g : Λ → ℝ} (hg : Integrable g μ) {W : ℂ → ℝ}
    (hW0 : ∀ z ∈ U, 0 ≤ W z) (hm : ∀ z ∈ U, AEStronglyMeasurable (fun a => f a z) μ)
    (hb : ∀ᵐ a ∂μ, ∀ z ∈ U, ‖f a z‖ ≤ g a * W z) {z : ℂ} (hz : z ∈ U) :
    Integrable (fun a => f a z) μ := by
  refine Integrable.mono' (hg.abs.mul_const (W z)) (hm z hz) ?_
  filter_upwards [hb] with a ha
  exact (ha z hz).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (hW0 z hz))

/-- **Holomorphic parameter integrals.** A dominated integral of an a.e. holomorphic family with
measurable values is holomorphic. -/
theorem differentiableOn_integral_of_dominated {Λ : Type*} [MeasurableSpace Λ]
    {μ : Measure Λ} {f : Λ → ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) {g : Λ → ℝ}
    (hg : Integrable g μ) {W : ℂ → ℝ} (hW : ContinuousOn W U) (hW0 : ∀ z ∈ U, 0 ≤ W z)
    (hm : ∀ z ∈ U, AEStronglyMeasurable (fun a => f a z) μ)
    (hd : ∀ᵐ a ∂μ, DifferentiableOn ℂ (f a) U)
    (hb : ∀ᵐ a ∂μ, ∀ z ∈ U, ‖f a z‖ ≤ g a * W z) :
    DifferentiableOn ℂ (fun z => ∫ a, f a z ∂μ) U := by
  intro z₀ hz₀
  have hWc : ContinuousAt W z₀ := hW.continuousAt (hU.mem_nhds hz₀)
  have hev : ∀ᶠ z in 𝓝 z₀, z ∈ U ∧ W z < W z₀ + 1 :=
    Filter.Eventually.and (hU.mem_nhds hz₀ : ∀ᶠ z in 𝓝 z₀, z ∈ U)
      (hWc.eventually (Iio_mem_nhds (lt_add_one (W z₀))))
  obtain ⟨r2, hr2, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set B := W z₀ + 1
  have hfb : ∀ᵐ a ∂μ, ∀ w ∈ ball z₀ r2, ‖f a w‖ ≤ |g a| * B := by
    filter_upwards [hb] with a ha w hw
    obtain ⟨hwU, hwB⟩ := hball w hw
    calc ‖f a w‖ ≤ g a * W w := ha w hwU
      _ ≤ |g a| * W w := mul_le_mul_of_nonneg_right (le_abs_self _) (hW0 w hwU)
      _ ≤ |g a| * B := mul_le_mul_of_nonneg_left hwB.le (abs_nonneg _)
  have hder : ∀ᵐ a ∂μ, ∀ z ∈ ball z₀ (r2 / 2), ‖deriv (f a) z‖ ≤ 4 * B / r2 * |g a| := by
    filter_upwards [hd, hfb] with a hda hfa z hz
    have hdb : DifferentiableOn ℂ (f a) (ball z₀ r2) := hda.mono fun w hw => (hball w hw).1
    calc ‖deriv (f a) z‖ ≤ 4 * (|g a| * B) / r2 := norm_deriv_le_of_ball_half hr2 hdb hfa hz
      _ = 4 * B / r2 * |g a| := by ring
  have hdiff : ∀ᵐ a ∂μ, ∀ z ∈ ball z₀ (r2 / 2),
      HasDerivAt (fun z => f a z) (deriv (f a) z) z := by
    filter_upwards [hd] with a hda z hz
    have hzU : z ∈ U := (hball z (ball_subset_ball (by linarith) hz)).1
    exact ((hda z hzU).differentiableAt (hU.mem_nhds hzU)).hasDerivAt
  have hmeas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (fun a => f a z) μ :=
    Filter.eventually_of_mem (hU.mem_nhds hz₀) hm
  have hint : Integrable (fun a => f a z₀) μ :=
    integrable_of_dominated_param hg hW0 hm hb hz₀
  have hmeas' : AEStronglyMeasurable (fun a => deriv (f a) z₀) μ := by
    have h1 := aestronglyMeasurable_iteratedDeriv_of_ae_differentiableOn hU hd hm 1 z₀ hz₀
    simpa only [iteratedDeriv_one] using h1
  obtain ⟨-, hD⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun z a => f a z) (F' := fun z a => deriv (f a) z)
    (ball_mem_nhds z₀ (half_pos hr2)) hmeas hint hmeas' hder
    (hg.abs.const_mul (4 * B / r2)) hdiff
  exact hD.differentiableAt.differentiableWithinAt

end PGM
