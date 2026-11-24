import PLAStochastic.Swing.StationaryLimit.MarginKernel.WeakFeller
import PLAStochastic.Swing.StationaryLimit.MarginKernel.InvariantUniqueness
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakLimit
import PLAStochastic.Swing.StationaryScale.MarginMomentsReal

/-! # Theorem 4.3 with existence and the weak limit `eq:marginweaklimit`

The limiting margin kernel `K` is already known to be weakly Feller, to have
Lebesgue-equivalent transitions and at most one invariant probability.  What was
missing is existence, which the paper obtains from the invariant laws `ν_E` of
the finite-budget reflected margin.  This file supplies that passage: given the
compact-uniform kernel convergence `eq:marginkernellocalconvergence` and the
tightness of `ν_E` provided by Theorem 4.2, the invariant probability of `K`
exists, is equivalent to Lebesgue measure, and is the weak limit of `ν_E`.

The uniform kernel convergence is a named hypothesis here; its proof needs the
substitute-output construction of `eq:prefixcrossinglevel` on top of the
Blanchet-Glynn uniform renewal expansion, neither of which is formalized.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The weak Feller property in the form the transfer needs. -/
theorem swingMarginKernel_bddLip_continuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (f : ℝ → ℝ) (L B : ℝ) (hf : KernelLimit.IsBddLip f L B) :
    Continuous (fun r : ℝ => ∫ y, f y ∂(swingMarginKernel X μ r)) :=
  swingMarginKernel_integral_continuous hX hi hG hf.meas hf.lip hf.bdd

/-- Any weak cluster point of invariant laws of kernels converging to `K`
uniformly on bounded sets of margins is *the* invariant law of `K`. -/
theorem swingMarginKernel_invariant_of_mapClusterPt [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {KE : ι → Kernel ℝ ℝ} (hKE : ∀ i, IsMarkovKernel (KE i))
    {νE : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hinv : ∀ i, (KE i).Invariant (νE i : Measure ℝ))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(KE i r)) - (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε)
    (hcl : MapClusterPt ν l νE) :
    (swingMarginKernel X μ).Invariant (ν : Measure ℝ) := by
  let : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  exact KernelLimit.invariant_of_mapClusterPt hKE hinv
    (swingMarginKernel_bddLip_continuous hX hi hG) hunif hcl

/-- Theorem 4.3 including existence and `eq:marginweaklimit`.  Under the
compact-uniform kernel convergence and the tightness of the finite-budget
invariant laws, the limiting margin kernel has a unique invariant probability,
it is equivalent to Lebesgue measure, and the finite-budget laws converge to it
weakly. -/
theorem theorem_4_3_margin_weak_limit [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {KE : ι → Kernel ℝ ℝ} (hKE : ∀ i, IsMarkovKernel (KE i))
    {νE : ι → ProbabilityMeasure ℝ}
    (hinv : ∀ i, (KE i).Invariant (νE i : Measure ℝ))
    (htight : IsTightMeasureSet {m : Measure ℝ | ∃ i, m = (νE i : Measure ℝ)})
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(KE i r)) - (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto νE l (𝓝 ν) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  let : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
  obtain ⟨ν, hinvν, htendν⟩ := KernelLimit.exists_invariant_tendsto hKE hinv htight
    (swingMarginKernel_bddLip_continuous hX hi hG) hunif
    (fun ν₁ ν₂ hp₁ hp₂ h₁ h₂ => by
      let : IsProbabilityMeasure ν₁ := hp₁
      let : IsProbabilityMeasure ν₂ := hp₂
      exact swingMarginKernel_invariant_unique hX hi hG h₁ h₂)
  refine ⟨ν, hinvν, swingMarginKernel_invariant_absolutelyContinuous hX hinvν, ?_, htendν,
    fun ν' hp' h' => ?_⟩
  · refine volume_absolutelyContinuous_swingMarginKernel_invariant hX hi hG ?_ hinvν
    intro hc
    have hone : (ν : Measure ℝ) univ = 1 := measure_univ
    simp [hc] at hone
  · let : IsProbabilityMeasure ν' := hp'
    exact swingMarginKernel_invariant_unique hX hi hG h' hinvν

/-- The form Theorem 4.2 can discharge: a uniform bound on the first absolute
margin moment replaces the tightness hypothesis. -/
theorem theorem_4_3_margin_weak_limit_of_moment [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {KE : ι → Kernel ℝ ℝ} (hKE : ∀ i, IsMarkovKernel (KE i))
    {νE : ι → ProbabilityMeasure ℝ}
    (hinv : ∀ i, (KE i).Invariant (νE i : Measure ℝ))
    {M : ℝ≥0∞} (hMtop : M ≠ ⊤)
    (hmoment : ∀ i, (∫⁻ x, ENNReal.ofReal |x| ∂(νE i : Measure ℝ)) ≤ M)
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(KE i r)) - (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto νE l (𝓝 ν) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) :=
  theorem_4_3_margin_weak_limit hX hi hG hKE hinv
    (KernelLimit.isTightMeasureSet_of_measure_abs_gt
      (fun _ hε => KernelLimit.exists_measure_abs_gt_le_of_moment hMtop hmoment hε))
    hunif

/-! ### The actual finite-budget margin law

Theorem 4.2 bounds every stationary margin moment uniformly in the budget, so
the tightness the transfer needs is available for the actual reflected margin
law and is not assumed below.
-/

theorem measurable_reflectedMargin (E : ℝ) : Measurable (fun y : ℝ => E - |y|) :=
  measurable_const.sub continuous_abs.measurable

/-- `ν_E`: the law of the reflected margin `R = E - |X|` under an invariant law
of the actual native restart chain. -/
def stationaryMarginLaw (E : ℝ) (π : Measure ℝ) : Measure ℝ := π.map (fun y => E - |y|)

theorem isProbabilityMeasure_stationaryMarginLaw (E : ℝ) (π : Measure ℝ)
    [IsProbabilityMeasure π] : IsProbabilityMeasure (stationaryMarginLaw E π) :=
  Measure.isProbabilityMeasure_map (measurable_reflectedMargin E).aemeasurable

/-- `ν_E` as a probability measure. -/
def stationaryMarginProb (E : ℝ) (π : Measure ℝ) (hπ : IsProbabilityMeasure π) :
    ProbabilityMeasure ℝ :=
  ⟨stationaryMarginLaw E π, @isProbabilityMeasure_stationaryMarginLaw E π hπ⟩

/-- The uniform first absolute moment of `ν_E` from Theorem 4.2: the bound does
not depend on the budget. -/
theorem lintegral_abs_stationaryMarginLaw_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E) {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (∫⁻ x, ENNReal.ofReal |x| ∂(stationaryMarginLaw E π))
      ≤ ENNReal.ofReal (stationaryMarginMomentBound 1) := by
  have hmap : (∫⁻ x, ENNReal.ofReal |x| ∂(stationaryMarginLaw E π))
      = ∫⁻ y, ENNReal.ofReal |E - abs y| ∂π := by
    rw [stationaryMarginLaw]
    exact lintegral_map (f := fun x : ℝ => ENNReal.ofReal |x|)
      (ENNReal.measurable_ofReal.comp continuous_abs.measurable)
      (measurable_reflectedMargin E)
  have hint : Integrable (fun y : ℝ => |E - abs y|) π := by
    simpa using stationary_margin_abs_pow_integrable hX hi hG hE hπ (le_refl 1)
  have hbd : (∫ y, |E - abs y| ∂π) ≤ stationaryMarginMomentBound 1 := by
    simpa using nativeRestart_stationary_margin_pow_le hX hi hG hE hπ (le_refl 1)
  have hofreal : ENNReal.ofReal (∫ y, |E - abs y| ∂π)
      = ∫⁻ y, ENNReal.ofReal |E - abs y| ∂π :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun y => abs_nonneg _))
  rw [hmap, ← hofreal]
  exact ENNReal.ofReal_le_ofReal hbd

/-- Theorem 4.3 for the actual reflected margin laws: tightness is supplied by
Theorem 4.2, so the only remaining input is the compact-uniform kernel
convergence `eq:marginkernellocalconvergence` together with the finite-budget
margin kernels it compares. -/
theorem theorem_4_3_margin_weak_limit_actual [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    {πs : ι → Measure ℝ} (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    {KE : ι → Kernel ℝ ℝ} (hKE : ∀ i, IsMarkovKernel (KE i))
    (hmarginv : ∀ i, (KE i).Invariant (stationaryMarginLaw (budget i) (πs i)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B → ∀ (C ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
        |(∫ y, f y ∂(KE i r)) - (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l (𝓝 ν) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  refine theorem_4_3_margin_weak_limit_of_moment hX hi hG hKE hmarginv
    (M := ENNReal.ofReal (stationaryMarginMomentBound 1)) ENNReal.ofReal_ne_top
    (fun i => ?_) hunif
  let : IsProbabilityMeasure (πs i) := hπP i
  exact lintegral_abs_stationaryMarginLaw_le hX hi hG (hbudget i) (hπinv i)

end SwingRepair
