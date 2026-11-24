import PLAStochastic.Swing.DenseSampling.PostFirst.DurationsAndMaxima
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Probability consequences of the post-first maximum estimate

These are implication lemmas. They do not assert the still separate maximum
estimate itself; that estimate must come from the conditional survival bounds.
-/
noncomputable section
open Classical MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- An indicator bound gives an L1 bound even for arbitrary underlying events. -/
theorem eLpNorm_one_le_of_indicator_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {E : Set Ω} {T : ℝ}
    (hX : ∀ ω, 0 ≤ X ω) (hbound : ∀ ω, X ω ≤ if ω ∈ E then T else 0) :
    eLpNorm X 1 μ ≤ ENNReal.ofReal T * μ E := by
  rw [eLpNorm_one_eq_lintegral_enorm]
  apply le_trans _ (lintegral_indicator_const_le E (ENNReal.ofReal T))
  apply lintegral_mono
  intro ω
  dsimp only
  rw [Real.enorm_eq_ofReal (hX ω)]
  by_cases hE : ω ∈ E
  · rw [Set.indicator_of_mem hE]
    exact ENNReal.ofReal_le_ofReal (by simpa only [if_pos hE] using hbound ω)
  · rw [Set.indicator_of_notMem hE]
    have hx : X ω ≤ 0 := by simpa only [if_neg hE] using hbound ω
    simp only [ENNReal.ofReal_eq_zero.mpr hx, le_refl]

/-- Fixed-threshold covered time converges in L1 once the actual maximum
converges in probability. -/
theorem eLpNorm_one_tendsto_zero_of_maximum {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} {M X : ι → Ω → ℝ} {T a : ℝ} (ha : 0 < a)
    (hM : ∀ i ω, 0 ≤ M i ω) (hX : ∀ i ω, 0 ≤ X i ω)
    (hbound : ∀ i ω, X i ω ≤ if a ≤ M i ω then T else 0)
    (hconv : TendstoInMeasure μ M l (fun _ => 0)) :
    Tendsto (fun i => eLpNorm (X i) 1 μ) l (𝓝 0) := by
  have hm := tendstoInMeasure_iff_norm.mp hconv a ha
  simp only [sub_zero, Real.norm_eq_abs, abs_of_nonneg (hM _ _)] at hm
  have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal T) hm (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro i
  exact eLpNorm_one_le_of_indicator_bound (hX i) (hbound i)

/-- The time-weighted corollary for the actual Brownian native output, awaiting
only the maximum theorem which is proved separately from local state estimates. -/
theorem brownian_native_timeweighted_of_maximum {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {ε H a : ℝ} (hε : 0 < ε) (hH : 0 ≤ H) (ha : 0 < a)
    {l : Filter ι} {h : ι → ℝ≥0} (hh : ∀ i, h i ≠ 0)
    (hmax : TendstoInMeasure μ (fun i => brownianNativePostFirstMaximum B ε H (h i))
      l (fun _ => 0)) :
    TendstoInMeasure μ (fun i => brownianNativePostFirstLongTime B ε H a (h i))
      l (fun _ => 0) ∧
    Tendsto (fun i => eLpNorm (brownianNativePostFirstLongTime B ε H a (h i)) 1 μ) l (𝓝 0) ∧
    Tendsto (fun i => ∫ ω, |brownianNativePostFirstLongTime B ε H a (h i) ω| ∂μ) l (𝓝 0) := by
  have hLp := eLpNorm_one_tendsto_zero_of_maximum ha
    (fun i ω => (brownianNativePostFirstMaximum_bounds B hε.le hH (hh i) ω).1)
    (fun i ω => (brownianNativePostFirstLongTime_bounds B hε.le hH a (hh i) ω).1)
    (fun i ω => (brownianNativePostFirstLongTime_bounds B hε.le hH a (hh i) ω).2) hmax
  have hA (i : ι) := (aemeasurable_brownianNativePostFirstLongTime hB ε H a (hh i)).aestronglyMeasurable
  refine ⟨?_, hLp, ?_⟩
  · apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero hA aestronglyMeasurable_const
    simpa only [← Pi.zero_def, sub_zero] using hLp
  · have hr := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hLp
    simpa only [Function.comp_def, eLpNorm_one_eq_lintegral_enorm, ENNReal.toReal_zero,
      ← integral_norm_eq_lintegral_enorm (hA _), Real.norm_eq_abs] using hr

end SwingRepair
