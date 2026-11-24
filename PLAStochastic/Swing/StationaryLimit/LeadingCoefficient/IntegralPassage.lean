import PLAStochastic.Swing.StationaryLimit.MarginKernel.InvariantExistence
import PLAStochastic.Swing.FrozenCarry.MeanLimit.ConditionalLogMean
import PLAStochastic.Swing.SecondSegment.FrozenMeanBridge
import PLAStochastic.Swing.StationaryLimit.MarginKernel.NativeWeakLimit

/-!
# The final integral passage in Theorem 4.3

The margin-kernel part of Theorem 4.3 produces a weak limit
`ν_E ⇒ ν∞`.  The conditional mean theorem, on the other hand, is a
compact-uniform statement.  This file records the (deliberately separate)
functional-analytic interface which combines the two facts.  The reward has
a possible jump at zero, so the model-specific work is exposed as a bounded
continuous approximation hypothesis.  This prevents a weak-convergence
statement from being silently used for an unbounded/discontinuous reward.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The explicit remainder interface used by the final integral passage. -/
def IntegralTransferHypothesis
    {ι : Type*} {l : Filter ι} {νs : ι → ProbabilityMeasure ℝ}
    {ν : ProbabilityMeasure ℝ} (fs : ι → ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ (g : ℝ → ℝ) (B : ℝ),
      Continuous g ∧ (∀ x, |g x| ≤ B) ∧
      (∀ᶠ i in l,
        |(∫ x, fs i x ∂(νs i : Measure ℝ)) -
          ∫ x, g x ∂(νs i : Measure ℝ)| < ε) ∧
      |(∫ x, f x ∂(ν : Measure ℝ)) - ∫ x, g x ∂(ν : Measure ℝ)| < ε

/-! ### Generic bounded-continuous approximation lemma -/

/-
If the (possibly unbounded and discontinuous) integrands can be approximated
in integral by one bounded continuous test function, weak convergence of the
probability laws transfers the integral limit.  The approximation is stated
on both the approximating laws and the limit law; this is the exact place
where compact-uniform convergence, the zero-neighbourhood estimate, and the
uniform-integrability/tail estimate enter.
-/
theorem tendsto_integral_of_bddContinuous_approx
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {fs : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hν : Tendsto νs l (𝓝 ν))
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ (g : ℝ → ℝ) (B : ℝ),
        Continuous g ∧ (∀ x, |g x| ≤ B) ∧
        (∀ᶠ i in l,
          |(∫ x, fs i x ∂(νs i : Measure ℝ)) -
            ∫ x, g x ∂(νs i : Measure ℝ)| < ε) ∧
        |(∫ x, f x ∂(ν : Measure ℝ)) - ∫ x, g x ∂(ν : Measure ℝ)| < ε) :
    Tendsto (fun i => ∫ x, fs i x ∂(νs i : Measure ℝ)) l
      (𝓝 (∫ x, f x ∂(ν : Measure ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨g, B, hg, hgB, hsi, hsl⟩ := happrox (ε / 3) (by linarith)
  have hgi : Tendsto (fun i => ∫ x, g x ∂(νs i : Measure ℝ)) l
      (𝓝 (∫ x, g x ∂(ν : Measure ℝ))) :=
    KernelLimit.tendsto_integral_of_tendsto hν g B hg hgB
  have hge := hgi.eventually
    (Metric.ball_mem_nhds _ (by linarith : (0 : ℝ) < ε / 3))
  filter_upwards [hsi, hge] with i hi hi'
  have hi'' : |(∫ x, g x ∂(νs i : Measure ℝ)) -
      ∫ x, g x ∂(ν : Measure ℝ)| < ε / 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hi'
  have hsl' : |(∫ x, g x ∂(ν : Measure ℝ)) -
      ∫ x, f x ∂(ν : Measure ℝ)| < ε / 3 := by
    simpa only [abs_sub_comm] using hsl
  rw [Real.dist_eq]
  calc
    |(∫ x, fs i x ∂(νs i : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)|
        ≤ |(∫ x, fs i x ∂(νs i : Measure ℝ)) -
            ∫ x, g x ∂(νs i : Measure ℝ)| +
          |(∫ x, g x ∂(νs i : Measure ℝ)) -
            ∫ x, g x ∂(ν : Measure ℝ)| +
          |(∫ x, g x ∂(ν : Measure ℝ)) - ∫ x, f x ∂(ν : Measure ℝ)| := by
      exact (abs_sub_le _ _ _).trans (add_le_add (abs_sub_le _ _ _)
        (le_refl _))
    _ < ε := by linarith [hi, hi'', hsl']

/-! ### Names used by the leading-coefficient interface -/

/-- The limiting positive-margin reward. -/
def marginLeadingReward (X : ℕ → Ω → ℝ) (μ : Measure Ω) (r : ℝ) : ℝ :=
  if 0 < r then 4 * gaussianRenewalPotential X μ r else 0

/-- The normalized frozen conditional mean used in the stationary mixture. -/
def normalizedFrozenMean (X : ℕ → Ω → ℝ) (μ : Measure Ω)
    (E r : ℝ) : ℝ :=
  (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) / (E * Real.log E)

/-- The coefficient represented by a limiting margin law. -/
def stationaryLeadingCoefficient (X : ℕ → Ω → ℝ)
    (μ : Measure Ω) (ν : Measure ℝ) : ℝ :=
  ∫ r, marginLeadingReward X μ r ∂ν

theorem marginLeadingReward_measurable_of
    (X : ℕ → Ω → ℝ) (μ : Measure Ω)
    (hV : Measurable (gaussianRenewalPotential X μ)) :
    Measurable (marginLeadingReward X μ) := by
  unfold marginLeadingReward
  exact Measurable.ite measurableSet_Ioi
    (hV.const_mul 4) measurable_const

/-! ### The abstract leading-coefficient limit -/

/--
Abstract Theorem 4.3 final step.  No kernel convergence is hidden here: it is
consumed only through the supplied weak convergence `hν`.  The hypothesis
`happrox` is the explicit remainder interface for (i) compact-uniform
conditional means away from zero, (ii) the negative-carry estimate and the
zero neighbourhood, and (iii) the positive-moment tail bound.
-/
theorem leading_coefficient_integral_tendsto
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {fs : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hν : Tendsto νs l (𝓝 ν))
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ (g : ℝ → ℝ) (B : ℝ),
        Continuous g ∧ (∀ x, |g x| ≤ B) ∧
        (∀ᶠ i in l,
          |(∫ x, fs i x ∂(νs i : Measure ℝ)) -
            ∫ x, g x ∂(νs i : Measure ℝ)| < ε) ∧
        |(∫ x, f x ∂(ν : Measure ℝ)) - ∫ x, g x ∂(ν : Measure ℝ)| < ε) :
    Tendsto (fun i => ∫ x, fs i x ∂(νs i : Measure ℝ)) l
      (𝓝 (∫ x, f x ∂(ν : Measure ℝ))) :=
  tendsto_integral_of_bddContinuous_approx hν happrox

/-- Same transfer theorem using the named remainder interface. -/
theorem leading_coefficient_integral_tendsto_of_transfer
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {fs : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hν : Tendsto νs l (𝓝 ν))
    (htransfer : IntegralTransferHypothesis (l := l) (νs := νs) (ν := ν) fs f) :
    Tendsto (fun i => ∫ x, fs i x ∂(νs i : Measure ℝ)) l
      (𝓝 (∫ x, f x ∂(ν : Measure ℝ))) := by
  exact leading_coefficient_integral_tendsto hν htransfer

/--
The positive-margin compact-uniform part of the transfer is already a theorem:
Theorem 3.2 composes with any budget filter tending to `+∞`.
-/
theorem normalizedFrozenMean_tendstoUniformlyOn_of_tendsto_budget
    {ι : Type*} {l : Filter ι} {budget : ι → ℝ}
    (hbudget : Tendsto budget l atTop)
    {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    TendstoUniformlyOn
      (fun i r => normalizedFrozenMean X μ (budget i) r)
      (fun r => 4 * gaussianRenewalPotential X μ r) l K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hE := (Metric.tendstoUniformlyOn_iff.mp
    (frozenPrefixLength_mean_tendstoUniformlyOn hX hi hG hK hK0)) ε hε
  filter_upwards [hbudget.eventually hE] with i hi'
  intro r hr
  exact hi' r hr

/--
The normalized frozen mean is measurable for the reflected stationary margin
law.  Globally this is not immediate from the current frozen-prefix API.  On
the support `r ≤ E`, however, it agrees with the measurable function
`r ↦ nativeRestartMean E (E-r)/(E log E)` by the already proved reflection
bridge; the margin pushforward is supported on that half-line.
-/
theorem normalizedFrozenMean_aemeasurable_stationaryMarginLaw
    [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (E : ℝ) (π : Measure ℝ) :
    AEMeasurable (normalizedFrozenMean X μ E)
      (stationaryMarginLaw E π) := by
  let q : ℝ → ℝ := fun r =>
    nativeRestartMean X μ E (E - r) / (E * Real.log E)
  have hq : Measurable q :=
    ((nativeRestartMean_measurable hX E).comp
      (measurable_const.sub measurable_id)).div_const _
  have hsupp : ∀ᵐ r ∂stationaryMarginLaw E π, r ≤ E := by
    rw [stationaryMarginLaw,
      ae_map_iff (measurable_reflectedMargin E).aemeasurable measurableSet_Iic]
    exact Eventually.of_forall (fun x => sub_le_self E (abs_nonneg x))
  apply hq.aemeasurable.congr
  filter_upwards [hsupp] with r hr
  have hx : 0 ≤ E - r := sub_nonneg.mpr hr
  have hb := nativeRestartMean_eq_frozen_margin hX hi hG E (E - r)
  rw [abs_of_nonneg hx, show E - (E - r) = r by ring] at hb
  exact congrArg (fun z : ℝ => z / (E * Real.log E)) hb

/--
The exact stationary bridge.  The only extra input is measurability of the
normalized frozen mean under the reflected margin law; the pathwise bridge
`nativeRestartMean_eq_frozen_margin` is already proved in `SecondSegmentBridge`.
-/
theorem nativeRestart_normalizedMean_eq_margin_integral
    [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {E : ℝ} {π : Measure ℝ} [IsProbabilityMeasure π] :
    (∫ x, nativeRestartMean X μ E x ∂π) / (E * Real.log E) =
      ∫ r, normalizedFrozenMean X μ E r ∂stationaryMarginLaw E π := by
  have hgm := normalizedFrozenMean_aemeasurable_stationaryMarginLaw
    hX hi hG E π
  have hmap := MeasureTheory.integral_map
    (measurable_reflectedMargin E).aemeasurable hgm.aestronglyMeasurable
  have hmap' :
      (∫ r, normalizedFrozenMean X μ E r ∂stationaryMarginLaw E π) =
        ∫ x, normalizedFrozenMean X μ E (E - |x|) ∂π := by
    simpa [stationaryMarginLaw] using hmap
  have hpoint : ∀ x : ℝ,
      nativeRestartMean X μ E x / (E * Real.log E) =
        normalizedFrozenMean X μ E (E - |x|) := by
    intro x
    rw [nativeRestartMean_eq_frozen_margin hX hi hG E x]
    rfl
  calc
    (∫ x, nativeRestartMean X μ E x ∂π) / (E * Real.log E) =
        ∫ x, nativeRestartMean X μ E x / (E * Real.log E) ∂π := by
          rw [integral_div]
    _ = ∫ x, normalizedFrozenMean X μ E (E - |x|) ∂π :=
      integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∫ r, normalizedFrozenMean X μ E r ∂stationaryMarginLaw E π := hmap'.symm

/--
Actual Theorem 4.3 interface.  Once the kernel theorem supplies the weak
convergence of the stationary margin probabilities, the remaining
model-specific obligation is exactly `htransfer`; the conclusion is the
normalized stationary mean limit and its integral representation.
-/
theorem theorem_4_3_leading_coefficient_actual
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} {πs : ι → Measure ℝ}
    {ν : ProbabilityMeasure ℝ}
    (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hν : Tendsto
      (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l
      (𝓝 ν))
    (hbridge : ∀ i,
      (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
          (budget i * Real.log (budget i)) =
        ∫ r, normalizedFrozenMean X μ (budget i) r ∂
          (stationaryMarginLaw (budget i) (πs i)))
    (htransfer : IntegralTransferHypothesis (l := l)
      (νs := fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) (ν := ν)
      (fun i r => normalizedFrozenMean X μ (budget i) r)
      (marginLeadingReward X μ)) :
    Tendsto
      (fun i =>
        (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
          (budget i * Real.log (budget i))) l
      (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) := by
  have hν' : Tendsto
      (fun i => stationaryMarginProb (budget i) (πs i) (hπP i)) l
      (𝓝 ν) := hν
  have hlim := leading_coefficient_integral_tendsto_of_transfer
    (νs := fun i => stationaryMarginProb (budget i) (πs i) (hπP i))
    (ν := ν) hν' htransfer
  change Tendsto
    (fun i =>
      (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
        (budget i * Real.log (budget i))) l
    (𝓝 (∫ r, marginLeadingReward X μ r ∂(ν : Measure ℝ)))
  apply hlim.congr'
  exact Eventually.of_forall (fun i => by
    change (∫ r, normalizedFrozenMean X μ (budget i) r ∂
      stationaryMarginLaw (budget i) (πs i)) = _
    exact (hbridge i).symm)

/--
Fully wired Theorem 4.3 interface.  The preceding margin-limit theorem is
used as an entry point, so the kernel hypotheses and the moment-based
tightness argument remain visible.  The transfer hypothesis is quantified
over the limit law returned by that theorem; this makes the dependency on the
zero-neighbourhood and tail estimates explicit rather than existentially
hidden.
-/
theorem theorem_4_3_leading_coefficient_from_margin_limit_actual [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    {πs : ι → Measure ℝ} (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i, (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    {KE : ι → Kernel ℝ ℝ} (hKE : ∀ i, IsMarkovKernel (KE i))
    (hmarginv : ∀ i,
      (KE i).Invariant (stationaryMarginLaw (budget i) (πs i)))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
        ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
          |(∫ y, f y ∂(KE i r)) -
            (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε)
    (htransfer : ∀ ν : ProbabilityMeasure ℝ,
      IntegralTransferHypothesis (l := l)
        (νs := fun i => stationaryMarginProb (budget i) (πs i) (hπP i))
        (ν := ν)
        (fun i r => normalizedFrozenMean X μ (budget i) r)
        (marginLeadingReward X μ)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto
          (fun i =>
            (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
              (budget i * Real.log (budget i))) l
          (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  obtain ⟨ν, hinv, hac, hca, hν, huniq⟩ :=
    theorem_4_3_margin_weak_limit_actual hX hi hG hbudget hπP hπinv hKE
      hmarginv hunif
  have hbridge : ∀ i,
      (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
          (budget i * Real.log (budget i)) =
        ∫ r, normalizedFrozenMean X μ (budget i) r ∂
          (stationaryMarginLaw (budget i) (πs i)) := by
    intro i
    let : IsProbabilityMeasure (πs i) := hπP i
    exact nativeRestart_normalizedMean_eq_margin_integral hX hi hG
  have hmean := theorem_4_3_leading_coefficient_actual
    (X := X) (μ := μ) (hπP := hπP) hν hbridge (htransfer ν)
  exact ⟨ν, hinv, hac, hca, hmean, huniq⟩

/-!
The native entry point for the complete Theorem 4.3 chain.  Compared with
`theorem_4_3_leading_coefficient_from_margin_limit_actual`, this version does
not expose an abstract finite-budget kernel or its invariant margin law.  The
finite kernel is the one constructed from the native restart map, and its
invariance is discharged internally by `theorem_4_3_margin_weak_limit_native`.
The only remaining model-specific input at this layer is the compact-uniform
test-function convergence for that native kernel and the final integral
transfer remainder hypothesis.
-/
theorem theorem_4_3_leading_coefficient_native [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    {πs : ι → Measure ℝ} (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i,
      (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    (hunif : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
        ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
          |(∫ y, f y ∂(nativeFiniteMarginKernel X μ (budget i) r)) -
            (∫ y, f y ∂(swingMarginKernel X μ r))| ≤ ε)
    (htransfer : ∀ ν : ProbabilityMeasure ℝ,
      IntegralTransferHypothesis (l := l)
        (νs := fun i => stationaryMarginProb (budget i) (πs i) (hπP i))
        (ν := ν)
        (fun i r => normalizedFrozenMean X μ (budget i) r)
        (marginLeadingReward X μ)) :
    ∃ ν : ProbabilityMeasure ℝ,
      (swingMarginKernel X μ).Invariant (ν : Measure ℝ) ∧
        (ν : Measure ℝ) ≪ volume ∧ (volume : Measure ℝ) ≪ (ν : Measure ℝ) ∧
        Tendsto
          (fun i =>
            (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
              (budget i * Real.log (budget i))) l
          (𝓝 (stationaryLeadingCoefficient X μ (ν : Measure ℝ))) ∧
        ∀ ν' : Measure ℝ, IsProbabilityMeasure ν' →
          (swingMarginKernel X μ).Invariant ν' → ν' = (ν : Measure ℝ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  obtain ⟨ν, hinv, hac, hca, hν, huniq⟩ :=
    theorem_4_3_margin_weak_limit_native hX hi hG hbudget hπP hπinv hunif
  have hbridge : ∀ i,
      (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
          (budget i * Real.log (budget i)) =
        ∫ r, normalizedFrozenMean X μ (budget i) r ∂
          (stationaryMarginLaw (budget i) (πs i)) := by
    intro i
    let : IsProbabilityMeasure (πs i) := hπP i
    exact nativeRestart_normalizedMean_eq_margin_integral hX hi hG
  have hmean := theorem_4_3_leading_coefficient_actual
    (X := X) (μ := μ) (hπP := hπP) hν hbridge (htransfer ν)
  exact ⟨ν, hinv, hac, hca, hmean, huniq⟩

end LeadingCoefficient

end SwingRepair
