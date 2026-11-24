import PLAStochastic.Swing.StationaryLimit.LowerBridge.UniformBudgetExistence

/-!
# Uniform bad-mass bound for the affine lower bridge

The deterministic affine bridge is now combined with the two already proved
localization cutoffs.  This file does not estimate the substitute law; it
proves the other half of `hinputs`: once the budget tends to infinity, the
random lower-bridge event has uniformly small complement on every fixed
incoming-margin compact set.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false

theorem exists_uniform_lower_bridge_bad_mass
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (J : ℕ) (δ M C q E₀ : ℝ),
      1 ≤ J ∧ 0 < δ ∧ 0 ≤ M ∧ 0 < C ∧ 0 < q ∧
      8 * q ≤ δ ∧ 0 ≤ E₀ ∧
      ∀ E : ℝ, E₀ ≤ E → ∀ r : ℝ, |r| ≤ K →
        μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤ ε := by
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hε3 : 0 < ε / 3 := by linarith
  obtain ⟨δ, M, J, hδ, hM, hJ, hgood⟩ :=
    exists_swingEarlySlopeGood_real_nonneg (μ := μ) hX hi hG hK hε3
  have hq : 0 < δ / 8 := by positivity
  let q : ℝ := δ / 8
  have hqpos : 0 < q := by simpa [q] using hq
  have hqsmall : 8 * q ≤ δ := by
    dsimp [q]
    ring_nf
    exact le_rfl
  obtain ⟨C, hC, henv⟩ :=
    exists_gaussianNegativeCarryAffineEnvelope_cutoff
      (μ := μ) hX hi hG (c := 2 * q) (ε := ε / 3)
      (by positivity) hε3
  have henv' :
      μ.real (gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) C)ᶜ ≤
      ε / 3 := by
    change μ.real {ω | ¬ (∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + ((2 * q) / 2) * ((n : ℝ) + 1))} ≤
      ε / 3
    simpa only [show (2 * q) / 2 = q by ring] using henv
  let E₀ : ℝ :=
    41 * K + 69 * C + 69 * q * (J : ℝ) +
      14 * M * (J : ℝ) + 7 * M + 21 * q
  have hE₀ : 0 ≤ E₀ := by
    dsimp [E₀]
    have hJr : (0 : ℝ) ≤ (J : ℝ) := by positivity
    have hMj : 0 ≤ M * (J : ℝ) := mul_nonneg (by linarith) hJr
    have hqj : 0 ≤ q * (J : ℝ) := mul_nonneg hqpos.le hJr
    nlinarith
  refine ⟨J, δ, M, C, q, E₀, hJ, hδ, hM, hC, hqpos, hqsmall, hE₀, ?_⟩
  · intro E hE r hr
    have hE0 : 0 ≤ E := hE₀.trans hE
    have hbudget :
        41 * K + 69 * C + 69 * q * (J : ℝ) +
            14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E := by
      simpa [E₀] using hE
    have hbad :=
      prefixCrossingUniformBudgetEvent_compl_measure_le_of_envelope_compl
        (μ := μ) (X := X) E r J (K := K) (δ := δ) (M := M)
        (C := C) (q := q) (α := ε / 3) (β := ε / 3)
        hX hJ hE0 hK hδ (by linarith) hC.le hqpos.le hqsmall hr
        hgood henv' hbudget
    linarith

/-! A filter-facing form for the budget sequences used by Theorem 4.3. -/
theorem eventually_uniform_lower_bridge_bad_mass
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget_top : Tendsto budget l atTop)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ K →
      μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ ε := by
  obtain ⟨J, δ, M, C, q, E₀, hJ, hδ, hM, hC, hq, hqsmall, hE₀, hbound⟩ :=
    exists_uniform_lower_bridge_bad_mass (μ := μ) hX hi hG hK hε
  refine ⟨J, ?_⟩
  filter_upwards [hbudget_top.eventually (eventually_ge_atTop E₀)] with i hi
  intro r hr
  exact hbound (budget i) hi r hr

theorem eventually_uniform_lower_bridge_bad_mass_with_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget_top : Tendsto budget l atTop)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ J : ℕ, ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ K →
      0 ≤ budget i ∧
      μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ ε := by
  obtain ⟨J, δ, M, C, q, E₀, hJ, hδ, hM, hC, hq, hqsmall, hE₀, hbound⟩ :=
    exists_uniform_lower_bridge_bad_mass (μ := μ) hX hi hG hK hε
  refine ⟨J, ?_⟩
  filter_upwards [hbudget_top.eventually (eventually_ge_atTop E₀)] with i hi
  intro r hr
  exact ⟨hE₀.trans hi, hbound (budget i) hi r hr⟩

end SwingRepair
