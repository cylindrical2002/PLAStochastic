import PLAStochastic.Swing.StationaryScale.MarginMomentsNat

/-! Real-order stationary margin moments for Theorem 4.2.

The paper states the margin estimate for every real `p > 0`.  The integer
moment chain is already proved in `StationaryMarginMomentPow`; this file
packages the elementary comparison `x^p ≤ 1 + x^⌈p⌉` for `x ≥ 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : ℕ → Ω → ℝ}

theorem stationary_margin_abs_pow_integrable [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun y : ℝ => |E - abs y| ^ k) π := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEpos : 0 < E := by
    have hEm : (5120000 : ℝ) ≤ E := by
      have h := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hE
      simpa [stationaryMarginThreshold] using h
    linarith
  have hmp_meas : Measurable (fun y : ℝ => nativeRestartMarginPos E y ^ k) :=
    (measurable_nativeRestartMarginPos E).pow_const k
  have hmp_nonneg : ∀ y : ℝ, 0 ≤ nativeRestartMarginPos E y ^ k :=
    fun y => pow_nonneg (le_max_right _ _) k
  have hmp_upper : ∀ y : ℝ, nativeRestartMarginPos E y ^ k ≤ E ^ k := by
    intro y
    exact pow_le_pow_left₀ (le_max_right _ _)
      (max_le (by linarith [abs_nonneg y]) hEpos.le) k
  have hmp_int : Integrable (fun y : ℝ => nativeRestartMarginPos E y ^ k) π :=
    Doeblin.integrable_bounded_reward π hmp_meas hmp_nonneg hmp_upper
  have hexc_int : Integrable (fun y : ℝ => nativeRestartExcess E y ^ k) π :=
    stationary_excess_pow_integrable hX hi hG hE hπ hk
  have hsum : Integrable (fun y : ℝ => nativeRestartMarginPos E y ^ k +
      nativeRestartExcess E y ^ k) π := hmp_int.add hexc_int
  refine hsum.congr ?_
  filter_upwards with y
  rw [abs_margin_pow_eq E y hk]

theorem nativeRestart_stationary_margin_rpow_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) {p : ℝ} (hp : 0 ≤ p) :
    (∫ y, |E - abs y| ^ p ∂π) ≤
      1 + stationaryMarginMomentBound (max 1 ⌈p⌉₊) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let k : ℕ := max 1 ⌈p⌉₊
  have hk : 1 ≤ k := by exact le_max_left _ _
  have hpk : p ≤ (k : ℝ) := by
    exact le_trans (Nat.le_ceil p) (by exact_mod_cast le_max_right 1 ⌈p⌉₊)
  have hbase : ∀ y : ℝ, 0 ≤ |E - abs y| := fun y => abs_nonneg _
  have hstep : ∀ y : ℝ, |E - abs y| ^ p ≤ 1 + |E - abs y| ^ k := by
    intro y
    set z : ℝ := |E - abs y|
    have hz : 0 ≤ z := abs_nonneg _
    rcases le_or_gt z 1 with hle | hgt
    · have hp1 : z ^ p ≤ 1 := Real.rpow_le_one hz hle hp
      have hk0 : 0 ≤ z ^ k := pow_nonneg hz k
      linarith
    · have h1 : 1 ≤ z := le_of_lt hgt
      have hpow : z ^ p ≤ z ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hpk
      rw [Real.rpow_natCast] at hpow
      have hk0 : 0 ≤ z ^ k := pow_nonneg hz k
      linarith
  have hintk : Integrable (fun y : ℝ => |E - abs y| ^ k) π :=
    stationary_margin_abs_pow_integrable hX hi hG hE hπ hk
  have hsum : Integrable (fun y : ℝ => 1 + |E - abs y| ^ k) π :=
    (integrable_const (1 : ℝ)).add hintk
  have hintp : Integrable (fun y : ℝ => |E - abs y| ^ p) π := by
    have hmeas : Measurable (fun y : ℝ => |E - abs y| ^ p) :=
      (Real.continuous_rpow_const hp).measurable.comp
        ((measurable_const.sub measurable_abs).abs)
    refine hsum.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hbase y) p)]
    exact hstep y
  have hmono : (∫ y, |E - abs y| ^ p ∂π) ≤
      ∫ y, (1 + |E - abs y| ^ k) ∂π :=
    integral_mono_ae hintp hsum (Eventually.of_forall hstep)
  rw [integral_add (integrable_const 1) hintk, integral_const] at hmono
  have hmono' : (∫ y, |E - abs y| ^ p ∂π) ≤
      1 + ∫ y, |E - abs y| ^ k ∂π := by simpa using hmono
  have hkm := nativeRestart_stationary_margin_pow_le hX hi hG hE hπ hk
  have hbound : (∫ y, |E - abs y| ^ k ∂π) ≤ stationaryMarginMomentBound k := hkm
  linarith

/-! Paper-level 4.2 entry with the real-order quantifier. -/
theorem theorem_4_2_stationary_scale_real [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) :
    (∀ p : ℝ, 0 < p → ∀ E : ℝ, stationaryScaleThreshold ≤ E →
        ∀ π : Measure ℝ, IsProbabilityMeasure π →
          (nativeRestartKernel X μ E).Invariant π →
            (∫ y, |E - abs y| ^ p ∂π) ≤
              1 + stationaryMarginMomentBound (max 1 ⌈p⌉₊)) ∧
      (∀ E : ℝ, stationaryScaleThreshold ≤ E →
        ∀ π : Measure ℝ, IsProbabilityMeasure π →
          (nativeRestartKernel X μ E).Invariant π →
            (∫ x, nativeRestartMean X μ E x ∂π) ≤
              stationaryScaleConstant * E * Real.log E) := by
  constructor
  · intro p hp E hE π hpπ hπ
    let : IsProbabilityMeasure π := hpπ
    exact nativeRestart_stationary_margin_rpow_le hX hi hG hE hπ hp.le
  · intro E hE π hpπ hπ
    let : IsProbabilityMeasure π := hpπ
    exact nativeRestart_stationary_mean_scale hX hi hG hE hπ

end SwingRepair
