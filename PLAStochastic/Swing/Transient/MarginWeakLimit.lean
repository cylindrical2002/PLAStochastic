import PLAStochastic.Swing.Transient.MarginLaw
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakPropagation
import PLAStochastic.Swing.StationaryLimit.MarginLawAndLeadingCoefficient

/-! # Subsequential weak limits of the transient margin laws

`eq:transient-subsequentiallaws` for the actual stream.  Three unconditional
inputs are combined:

* the compact-uniform convergence of the finite-budget margin kernel `K_E` to
  the limiting kernel `K` on bounded Lipschitz test functions, which follows
  from the uniform Blackwell renewal theorem exactly as in Theorem 4.3
  (`nativeFiniteMarginKernel_compact_uniform_gaussian`);
* the tightness of the first-restart margin laws `ρ_{1,E}`, from the uniform
  first moment of Lemma G.1 (`nativeTransientMarginProb_isTight`);
* the weak Feller property of `K`.

Along any budget filter on which `ρ_{1,E} ⇒ ν`, the `(m+1)`-st margin laws
converge weakly to `ν K^m`, for every fixed `m`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient KernelLimit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The unconditional compact-uniform kernel convergence -/

/-- `eq:marginkernellocalconvergence`, unconditional: along any budget filter
tending to `+∞`, the bounded Lipschitz test integrals of the finite-budget margin
kernel converge to those of `K` uniformly on bounded sets of margins. -/
theorem nativeFiniteMarginKernel_compact_uniform_gaussian [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget_top : Tendsto budget l atTop) :
    ∀ (f : ℝ → ℝ) (L B : ℝ), IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(nativeFiniteMarginKernel X μ (budget i) r)) -
          (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε := by
  have hover : UniformOvershootEquilibriumLimit X μ :=
    uniformOvershootEquilibriumLimit_of_tail_limit hX hi hG
      (uniformOvershootTailLimit_gaussian hX hi hG)
  apply nativeFiniteMarginKernel_compact_uniform_of_randomBridge (budget := budget) hX hi
  intro f L B hf C ε hε
  obtain ⟨J, δ, hJ, hδ, hsplit, hev⟩ :=
    exists_eventually_prefixCrossing_hinputs_of_uniform_overshoot
      (X := X) (μ := μ) hX hi hG hbudget_top hover f L B hf
      (K := max C 0) (le_max_right _ _) hε
  refine ⟨J, δ, hJ, hδ, hsplit, ?_⟩
  filter_upwards [hev] with i hi'
  intro r hr
  exact hi' r (hr.trans (le_max_left _ _))

/-! ### Tightness of the first-restart margin laws -/

/-- The family `{ρ_{1,E} : E ≥ E₀}` is tight. -/
theorem nativeTransientMarginProb_isTight [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i) :
    let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    IsTightMeasureSet {m : Measure ℝ | ∃ i, m = (nativeTransientMarginProb μ hX (budget i) 1 :
      Measure ℝ)} := by
  intro _
  refine isTightMeasureSet_of_measure_abs_gt
    (νs := fun i => nativeTransientMarginProb μ hX (budget i) 1) fun ε hε => ?_
  exact exists_measure_abs_gt_le_of_moment
    (νs := fun i => nativeTransientMarginProb μ hX (budget i) 1)
    (M := ENNReal.ofReal (transientMarginMomentBound 0 1)) ENNReal.ofReal_ne_top
    (fun i => nativeTransientMarginLaw_lintegral_abs_le hX hi hG (hbudget i) 0) hε

/-- Along any budget filter there is a cluster point of the first-restart margin
laws; the restricted filter converges to it and is still nontrivial. -/
theorem exists_clusterPt_nativeTransientMarginProb [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i) :
    let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    ∃ ν : ProbabilityMeasure ℝ,
      MapClusterPt ν l (fun i => nativeTransientMarginProb μ hX (budget i) 1) := by
  intro _
  set νs : ι → ProbabilityMeasure ℝ := fun i => nativeTransientMarginProb μ hX (budget i) 1
  have htight := nativeTransientMarginProb_isTight hX hi hG hbudget
  have hsets : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) | μ ∈ Set.range νs}
      = {m : Measure ℝ | ∃ i, m = (νs i : Measure ℝ)} := by
    ext m
    constructor
    · rintro ⟨μ, ⟨i, hi⟩, hμ⟩
      exact ⟨i, by rw [← hμ, hi]⟩
    · rintro ⟨i, hi⟩
      exact ⟨νs i, ⟨i, rfl⟩, hi.symm⟩
  have hcomp : IsCompact (closure (Set.range νs)) :=
    isCompact_closure_of_isTightMeasureSet (by rw [hsets]; exact htight)
  have hmem : ∀ᶠ i in l, νs i ∈ closure (Set.range νs) :=
    Eventually.of_forall (fun i => subset_closure ⟨i, rfl⟩)
  obtain ⟨ν, -, hνcl⟩ := hcomp.exists_clusterPt (f := map νs l) (le_principal_iff.mpr hmem)
  exact ⟨ν, hνcl⟩

/-! ### Propagation to every fixed segment index -/

/-- `ρ_{m+1,E}` as the `m`-fold transition of `ρ_{1,E}` under `K_E`, at the level
of probability measures. -/
theorem nativeTransientMarginProb_eq_compProbIter [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (m : ℕ) :
    let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    let _ : IsMarkovKernel (nativeFiniteMarginKernel X μ E) := nativeFiniteMarginKernel_isMarkov hX E
    nativeTransientMarginProb μ hX E (m+1) =
      compProbIter (nativeFiniteMarginKernel X μ E) m (nativeTransientMarginProb μ hX E 1) := by
  intro _ _
  apply ProbabilityMeasure.toMeasure_injective
  rw [compProbIter_coe, nativeTransientMarginProb_coe, nativeTransientMarginProb_coe]
  exact nativeTransientMarginLaw_eq_iterate hX hi hG hE m

/-- **`eq:transient-subsequentiallaws`.**  If `ρ_{1,E} ⇒ ν` along a countably
generated budget filter tending to `+∞`, then `ρ_{m+1,E} ⇒ ν K^m` for every `m`. -/
theorem nativeTransientMarginProb_tendsto [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop) {ν : ProbabilityMeasure ℝ}
    (hν : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) (m : ℕ) :
    let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
    let _ : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
    Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) (m+1)) l
      (𝓝 (compProbIter (swingMarginKernel X μ) m ν)) := by
  intro _ _
  have hEpos : ∀ i, 0 < budget i := fun i =>
    lt_of_lt_of_le stationaryScaleThreshold_pos (hbudget i)
  have hKs : ∀ i, IsMarkovKernel (nativeFiniteMarginKernel X μ (budget i)) := fun i =>
    nativeFiniteMarginKernel_isMarkov hX (budget i)
  have hrw : ∀ i, nativeTransientMarginProb μ hX (budget i) (m+1) =
      compProbIter (nativeFiniteMarginKernel X μ (budget i)) m
        (nativeTransientMarginProb μ hX (budget i) 1) := fun i =>
    nativeTransientMarginProb_eq_compProbIter hX hi hG (hEpos i) m
  simp_rw [hrw]
  exact tendsto_compProbIter hν (swingMarginKernel_bddLip_continuous hX hi hG)
    (nativeFiniteMarginKernel_compact_uniform_gaussian hX hi hG hbudget_top) m

end SwingRepair
