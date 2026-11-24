import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.UniformBudgetKernel
import PLAStochastic.Swing.Ladder.Blackwell.OvershootProvider
import PLAStochastic.Swing.StationaryLimit.Slope.EarlyLocalizationTarget
import PLAStochastic.Swing.StationaryLimit.LowerBridge.UniformProbability
import PLAStochastic.Swing.StationaryScale.SegmentMeanScale
import PLAStochastic.Swing.StationaryLimit.MarginKernel.NativeWeakLimit

/-!
# From the uniform overshoot limit to the native `hinputs` interface

This module performs the quantitative selector bookkeeping that sits between
the state-local substitute estimate and `Theorem43Native`.  Its only
probabilistic input is `UniformOvershootEquilibriumLimit`, the statement that
the actual walk's distant overshoot agrees with the equilibrium overshoot
against bounded Lipschitz test functions, uniformly over a positive compact
drift strip.  That predicate is exactly what the paper's proof consumes.

The Blanchet--Glynn renewal expansion is still available as an entry point:
`exists_eventually_prefixCrossing_hinputs_of_uniform_renewal` below routes it
through `uniformOvershootEquilibriumLimit_of_uniform_renewal`.  Both providers
remain hypotheses; neither is proved here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {Ω : Type*} [MeasurableSpace Ω]

theorem exists_eventually_prefixCrossing_hinputs_of_uniform_overshoot
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hGau : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget_top : Tendsto budget l atTop)
    (hover : UniformOvershootEquilibriumLimit X μ)
    (f : ℝ → ℝ) (L B : ℝ) (hf : KernelLimit.IsBddLip f L B)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ δ : ℝ,
      1 ≤ J ∧ 0 ≤ δ ∧ 2 * B * δ ≤ ε / 2 ∧
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ K →
        0 ≤ budget i ∧
        μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δ ∧
        |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
          ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2 := by
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hB : 0 ≤ B := le_trans (abs_nonneg (f 0)) (hf.bdd 0)
  have hL : 0 ≤ L := hf.const_nonneg
  let η : ℝ := ε / 4
  let p : ℝ := ε / (32 * (B + 1))
  have hη : 0 < η := by
    dsimp [η]
    linarith
  have hp : 0 < p := by
    dsimp [p]
    positivity
  obtain ⟨δ, M₀, J, hδ, _hδone, hM₀, hJ, hαbad₀⟩ :=
    exists_swingEarlySlopeGood_real_nonneg_le
      (μ := μ) hX hi hGau hK hp (by norm_num : (0 : ℝ) < 1)
  let M : ℝ := max M₀ δ
  have hM : 0 ≤ M := by
    dsimp [M]
    exact le_trans hM₀ (le_max_left _ _)
  have hδM : δ ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hgood_sub :
      swingEarlySlopeGood X K δ M₀ (J - 1) ⊆
        swingEarlySlopeGood X K δ M (J - 1) := by
    intro ω hω
    rcases hω with ⟨hlo, hupp, htail⟩
    exact ⟨hlo, hupp.trans (le_max_left _ _), htail⟩
  have hαbad : μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ p := by
    exact (measureReal_mono (Set.compl_subset_compl.mpr hgood_sub)
      (measure_ne_top μ _)).trans hαbad₀
  obtain ⟨Cenv, hCenv, hβraw⟩ :=
    exists_gaussianNegativeCarryAffineEnvelope_cutoff
      (μ := μ) hX hi hGau (c := 2 * (δ / 16)) (ε := p)
      (by positivity) hp
  have hβbad : μ.real
      (gaussianNegativeCarryAffineEnvelopeEvent X (2 * (δ / 16)) Cenv)ᶜ ≤ p := by
    change μ.real {ω | ¬ (∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ Cenv +
        ((2 * (δ / 16)) / 2) * ((n : ℝ) + 1))} ≤ p
    simpa only [show (2 * (δ / 16)) / 2 = δ / 16 by ring] using hβraw
  obtain ⟨b₀, hb₀, hfibre⟩ := hover δ M L B η hδ hM hL hB hη
  have hfibre' : ∀ a ∈ Icc δ M, ∀ b, b₀ ≤ b →
      |gaussianWalkReflectedReward X μ f a b -
        swingOvershootReward X μ f a| ≤ η := by
    intro a ha b hb
    exact hfibre a ha b hb f hf.lip hf.bdd
  let qenv : ℝ := δ / 16
  have hqenv : 0 < qenv := by
    dsimp [qenv]
    positivity
  have hqsmall : 8 * qenv ≤ δ := by
    dsimp [qenv]
    linarith
  let Ereq : ℝ := max stationaryScaleThreshold
    (max b₀
      (41 * K + 69 * Cenv + 69 * qenv * (J : ℝ) +
        14 * M * (J : ℝ) + 7 * M + 21 * qenv))
  have hEreq_budget :
      41 * K + 69 * Cenv + 69 * qenv * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * qenv ≤ Ereq := by
    dsimp [Ereq]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hEreq_b : b₀ ≤ Ereq := by
    dsimp [Ereq]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hEreq_stationary : stationaryScaleThreshold ≤ Ereq := by
    dsimp [Ereq]
    exact le_max_left _ _
  have hevE := hbudget_top.eventually (eventually_ge_atTop Ereq)
  let δerr : ℝ := 2 * p
  have hδerr : 0 ≤ δerr := by
    dsimp [δerr]
    linarith
  have hsplit : 2 * B * δerr ≤ ε / 2 := by
    dsimp [δerr, p]
    have hBp : 0 ≤ B + 1 := by linarith
    have hden : 0 < 32 * (B + 1) := by positivity
    have hfrac : 4 * B / (32 * (B + 1)) ≤ (1 : ℝ) / 8 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    have : 4 * B * (ε / (32 * (B + 1))) ≤ ε / 8 := by
      calc
        4 * B * (ε / (32 * (B + 1))) =
            ε * (4 * B / (32 * (B + 1))) := by ring
        _ ≤ ε * (1 / 8) :=
          mul_le_mul_of_nonneg_left hfrac hε.le
        _ = ε / 8 := by ring
    linarith
  refine ⟨J, δerr, hJ, hδerr, hsplit, ?_⟩
  filter_upwards [hevE] with i hiE
  intro r hr
  have hE : Ereq ≤ budget i := hiE
  have hE0 : 0 ≤ budget i := by
    have hthrpos : 0 < stationaryScaleThreshold := by
      have hexp : (0 : ℝ) < Real.exp (2 * stationaryAbsorptionConstant) :=
        Real.exp_pos _
      exact lt_of_lt_of_le hexp (le_max_right _ _)
    exact le_trans (le_of_lt hthrpos)
      (le_trans hEreq_stationary hE)
  have hbudget :
      41 * K + 69 * Cenv + 69 * qenv * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * qenv ≤ budget i :=
    le_trans hEreq_budget hE
  have hbridge :=
    prefixCrossingUniformBudgetEvent_compl_measure_le_of_envelope_compl
      (μ := μ) (X := X) (budget i) r J
      (K := K) (δ := δ) (M := M) (C := Cenv) (q := qenv)
      (α := p) (β := p) hX hJ hE0 hK hδ (by linarith) hCenv.le hqenv.le
      hqsmall hr hαbad hβbad hbudget
  have hsub :=
    prefixCrossingSubstitute_integral_sub_swingMarginKernel_of_uniform_budget_event
      (X := X) (μ := μ) hX hi hGau (budget i) r J
      (f := f) (K := K) (B := B) (η := η) (δ := δ) (M := M)
      (Cenv := Cenv) (q := qenv) (α := p) (β := p) hf.meas hB hη
      hδ hδM hM hCenv.le hqenv.le (by linarith) (by linarith)
      hf.bdd hJ hr hbudget hb₀ (le_trans hEreq_b hE) hfibre'
      hαbad hβbad
  have herr : η + 4 * B * (p + p) ≤ ε / 2 := by
    dsimp [η, p]
    have hden : 0 < 32 * (B + 1) := by positivity
    have hfrac : 8 * B / (32 * (B + 1)) ≤ (1 : ℝ) / 4 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    have hmul : 8 * B * (ε / (32 * (B + 1))) ≤ ε / 4 := by
      calc
        8 * B * (ε / (32 * (B + 1))) =
            ε * (8 * B / (32 * (B + 1))) := by ring
        _ ≤ ε * (1 / 4) :=
          mul_le_mul_of_nonneg_left hfrac hε.le
        _ = ε / 4 := by ring
    linarith
  have hbridge' :
      μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δerr := by
    simpa only [show p + p = 2 * p by ring, δerr] using hbridge
  have hsub' :
      |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
          ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2 :=
    hsub.trans herr
  exact ⟨hE0, hbridge', hsub'⟩

/-! The renewal-expansion form of the same selector step, kept so that the
Blanchet--Glynn provider remains a usable entry point. -/
theorem exists_eventually_prefixCrossing_hinputs_of_uniform_renewal
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hGau : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget_top : Tendsto budget l atTop)
    (hrenew : ∀ {δ M : ℝ}, 0 < δ → 0 ≤ M →
      ∃ Cexp c : ℝ,
        UniformLadderRenewalExpansion
          (gaussianAscendingLadderLaw X μ) (Icc δ M) Cexp c)
    (f : ℝ → ℝ) (L B : ℝ) (hf : KernelLimit.IsBddLip f L B)
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ δ : ℝ,
      1 ≤ J ∧ 0 ≤ δ ∧ 2 * B * δ ≤ ε / 2 ∧
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ K →
        0 ≤ budget i ∧
        μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δ ∧
        |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
          ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2 :=
  exists_eventually_prefixCrossing_hinputs_of_uniform_overshoot
    (X := X) (μ := μ) hX hi hGau hbudget_top
    (uniformOvershootEquilibriumLimit_of_uniform_renewal hX hi hGau hrenew)
    f L B hf hK hε

/-! The paper-facing closure conditional on the explicit renewal provider. -/
theorem theorem_4_3_margin_weak_limit_native_of_uniform_renewal
    {X : ℕ → Ω → ℝ} {μ : Measure Ω} [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hGau : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    {πs : ι → Measure ℝ} (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    (hrenew : ∀ {δ M : ℝ}, 0 < δ → 0 ≤ M →
      ∃ Cexp c : ℝ,
        UniformLadderRenewalExpansion
          (gaussianAscendingLadderLaw X μ) (Icc δ M) Cexp c) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l (𝓝 ν) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  apply theorem_4_3_margin_weak_limit_native_of_randomBridge
    (X := X) (μ := μ) hX hi hGau hbudget hπP hπinv
  intro f L B hf C ε hε
  obtain ⟨J, δ, hJ, hδ, hsplit, hinputs⟩ :=
    exists_eventually_prefixCrossing_hinputs_of_uniform_renewal
      (X := X) (μ := μ) hX hi hGau hbudget_top hrenew f L B hf
      (K := max C 0) (le_max_right _ _) hε
  refine ⟨J, δ, hJ, hδ, hsplit, ?_⟩
  filter_upwards [hinputs] with i hi'
  intro r hr
  exact hi' r (hr.trans (le_max_left _ _))

end SwingRepair
