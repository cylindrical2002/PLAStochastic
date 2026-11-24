import PLAStochastic.Swing.Transient.MarginWeakLimit
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.IntegralTransfer
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ConcreteBounds
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.LimitRewardBounds

/-! # `eq:transient-subsequentialmeans`: the mean passage for the actual segments

Along a budget filter on which the first-restart margin laws converge weakly to
`ν`, the normalised mean of the `(m+3)`-rd actual segment converges to
`∫ v d(ν K^{m+1})`, where `v(r) = 4V(r) 1_{r>0}` is the limiting positive-margin
reward.  The abstract transfer theorem `tendsto_integral_of_transfer` is
instantiated with

* the margin laws `ρ_{m+2,E} ⇒ ν K^{m+1}` (`nativeTransientMarginProb_tendsto`);
* the uniform second moment of `eq:transient-fullmoments`
  (`nativeTransientMarginLaw_abs_pow_le`);
* the linear growth bound `g_E(r)/(E log E) ≤ 2F(1 + r_+)`
  (`normalizedFrozenMean_le_linear`) and its limiting analogue;
* compact-uniform convergence of the normalised frozen means on each side of
  zero (`normalizedFrozenMean_tendstoUniformlyOn_of_tendsto_budget`,
  `normalizedFrozenMean_negative_tendstoUniformlyOn`);
* the absence of an atom at `0` for `ν K^{m+1}`, from the Lebesgue density of
  every transition of `K` (`swingMarginKernel_absolutelyContinuous`).

The segment indices follow the Lean convention: `nativeRecordingDurationNat X E j`
is the length of the segment started from the margin law `ρ_{j,E}`, so the paper's
`L_{k,E}` with `k ≥ 3` is `nativeRecordingDurationNat X E (k-1)`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient KernelLimit
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### One transition of `K` has no atoms -/

/-- `K ∘ₘ ρ` is absolutely continuous for every input law `ρ`. -/
theorem swingMarginKernel_comp_absolutelyContinuous [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (ρ : Measure ℝ) :
    swingMarginKernel X μ ∘ₘ ρ ≪ volume := by
  refine Measure.AbsolutelyContinuous.mk (fun A hA hzero => ?_)
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  have hpoint : ∀ x : ℝ, swingMarginKernel X μ x A = 0 :=
    fun x => swingMarginKernel_absolutelyContinuous hX x hzero
  simp only [hpoint, lintegral_zero]

/-- `ν K^{m+1}` has no atom at `0`. -/
theorem compProbIter_swingMarginKernel_singleton_zero [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (ν : ProbabilityMeasure ℝ) (m : ℕ) :
    let _ : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
    (compProbIter (swingMarginKernel X μ) (m+1) ν : Measure ℝ) {0} = 0 := by
  intro _
  rw [compProbIter_succ, compProb_coe]
  exact swingMarginKernel_comp_absolutelyContinuous hX _ (by simp)

/-! ### The limiting reward -/

/-- `v` is continuous away from `0`. -/
theorem marginLeadingReward_continuousAt_of_ne_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt (marginLeadingReward X μ) r := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have hev : marginLeadingReward X μ =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      unfold marginLeadingReward
      rw [if_neg (not_lt.mpr (le_of_lt (mem_Iio.mp hs)))]
    exact continuousAt_const.congr hev.symm
  · have hev : marginLeadingReward X μ =ᶠ[𝓝 r]
        fun s => 4 * gaussianRenewalPotential X μ s := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      unfold marginLeadingReward
      rw [if_pos (mem_Ioi.mp hs)]
    have hV : ContinuousAt (gaussianRenewalPotential X μ) r :=
      (gaussianRenewalPotential_continuousOn hX hi hG).continuousAt (Ici_mem_nhds hpos)
    exact (hV.const_mul 4).congr hev.symm

/-- The common linear growth constant of `v` and of the normalised frozen means. -/
def transientRewardGrowthConstant : ℝ :=
  max (2 * frozenUniformMeanConstant) (4 * (gaussianExcessExpMomentBound 2 + 1))

theorem transientRewardGrowthConstant_nonneg : 0 ≤ transientRewardGrowthConstant :=
  le_max_of_le_left (by have := frozenUniformMeanConstant_pos; linarith)

theorem marginLeadingReward_le_growth
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    marginLeadingReward X μ r ≤ transientRewardGrowthConstant * (1 + |r|) := by
  have h1 := marginLeadingReward_le_linear hX hi hG (r := r)
  have hM := (gaussianExcessExpMomentBound_pos 2).le
  have hmax : max r 0 ≤ |r| := max_le (le_abs_self r) (abs_nonneg r)
  have hA : 4 * (gaussianExcessExpMomentBound 2 + 1) ≤ transientRewardGrowthConstant :=
    le_max_right _ _
  calc marginLeadingReward X μ r ≤ 4 * (max r 0 + gaussianExcessExpMomentBound 2) := h1
    _ ≤ 4 * (gaussianExcessExpMomentBound 2 + 1) * (1 + |r|) := by nlinarith [abs_nonneg r]
    _ ≤ transientRewardGrowthConstant * (1 + |r|) :=
        mul_le_mul_of_nonneg_right hA (by linarith [abs_nonneg r])

theorem normalizedFrozenMean_le_growth [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : Real.exp 1 ≤ E) (r : ℝ) :
    normalizedFrozenMean X μ E r ≤ transientRewardGrowthConstant * (1 + |r|) := by
  have h1 := normalizedFrozenMean_le_linear hX hi hG (E := E) (r := r) hE
  have hF := frozenUniformMeanConstant_pos
  have hmax : max r 0 ≤ |r| := max_le (le_abs_self r) (abs_nonneg r)
  have hA : 2 * frozenUniformMeanConstant ≤ transientRewardGrowthConstant := le_max_left _ _
  calc normalizedFrozenMean X μ E r ≤ 2 * frozenUniformMeanConstant * (1 + max r 0) := h1
    _ ≤ 2 * frozenUniformMeanConstant * (1 + |r|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ ≤ transientRewardGrowthConstant * (1 + |r|) :=
        mul_le_mul_of_nonneg_right hA (by linarith [abs_nonneg r])

/-! ### Measurability of the normalised frozen mean under the transient laws -/

theorem normalizedFrozenMean_aemeasurable_transientMarginLaw [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (E : ℝ) (j : ℕ) :
    AEMeasurable (normalizedFrozenMean X μ E) (nativeTransientMarginLaw X μ E j) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [nativeTransientMarginLaw_eq_stationaryMarginLaw]
  exact normalizedFrozenMean_aemeasurable_stationaryMarginLaw hX hi hG E _

/-! ### Compact-uniform convergence on both sides of zero -/

/-- Away from zero, the normalised frozen means converge to `v` uniformly on
bounded sets, along any budget filter tending to `+∞`. -/
theorem normalizedFrozenMean_eventually_close_annulus
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} {budget : ι → ℝ} (hbudget_top : Tendsto budget l atTop)
    {δ C : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ r : ℝ, δ ≤ |r| → |r| ≤ C →
      |normalizedFrozenMean X μ (budget i) r - marginLeadingReward X μ r| ≤ ε := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hC' : 0 ≤ max C 0 := le_max_right _ _
  -- positive side
  have hpos := normalizedFrozenMean_tendstoUniformlyOn_of_tendsto_budget
    (X := X) (μ := μ) hbudget_top (K := Icc 0 (max C 0)) isCompact_Icc
    (fun r hr => (mem_Icc.mp hr).1) hX hi hG
  have hpos_ev := (Metric.tendstoUniformlyOn_iff.mp hpos) ε hε
  -- negative side
  have hneg := normalizedFrozenMean_negative_tendstoUniformlyOn
    (X := X) (μ := μ) hX hi hG (δ := δ) (C := max C 0) hδ hC'
  have hneg_ev := hbudget_top.eventually ((Metric.tendstoUniformlyOn_iff.mp hneg) ε hε)
  filter_upwards [hpos_ev, hneg_ev] with i hposi hnegi
  intro r hrδ hrC
  have hr0 : r ≠ 0 := by
    intro h
    rw [h, abs_zero] at hrδ
    linarith
  rcases lt_or_gt_of_ne hr0 with hneg' | hpos'
  · have hr : r ∈ Icc (-(max C 0)) (-δ) := by
      rw [abs_of_neg hneg'] at hrδ hrC
      constructor <;> linarith [le_max_left C 0]
    have := hnegi r hr
    rw [Real.dist_eq] at this
    have hv : marginLeadingReward X μ r = 0 := by
      unfold marginLeadingReward
      rw [if_neg (not_lt.mpr hneg'.le)]
    rw [hv, sub_zero]
    rw [zero_sub, abs_neg] at this
    exact this.le
  · have hr : r ∈ Icc 0 (max C 0) := by
      rw [abs_of_pos hpos'] at hrC
      exact ⟨hpos'.le, hrC.trans (le_max_left C 0)⟩
    have := hposi r hr
    rw [Real.dist_eq] at this
    have hv : marginLeadingReward X μ r = 4 * gaussianRenewalPotential X μ r := by
      unfold marginLeadingReward
      rw [if_pos hpos']
    rw [hv]
    rw [abs_sub_comm] at this
    exact this.le

/-! ### The mean passage -/

/-- **`eq:transient-subsequentialmeans`.**  If `ρ_{1,E} ⇒ ν` along a countably
generated budget filter tending to `+∞`, then for every fixed `m`

`E N_{m+2,E} / (E log E) → ∫ v d(ν K^{m+1})`,

where `N_{m+2,E} = nativeRecordingDurationNat X E (m+2)` is the length of the
segment started from `ρ_{m+2,E}` (the paper's `L_{m+3,E}`). -/
theorem nativeRecordingDurationNat_normalizedMean_tendsto [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop) {ν : ProbabilityMeasure ℝ}
    (hν : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) (m : ℕ) :
    let _ : IsMarkovKernel (swingMarginKernel X μ) := swingMarginKernel_isMarkov hX hi hG
    Tendsto (fun i => (∫ ω, (nativeRecordingDurationNat X (budget i) (m+2) ω : ℝ) ∂μ) /
        (budget i * Real.log (budget i))) l
      (𝓝 (∫ r, marginLeadingReward X μ r ∂
        (compProbIter (swingMarginKernel X μ) (m+1) ν : Measure ℝ))) := by
  intro _
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hEpos : ∀ i, 0 < budget i := fun i =>
    lt_of_lt_of_le stationaryScaleThreshold_pos (hbudget i)
  have hEexp : ∀ i, Real.exp 1 ≤ budget i := fun i =>
    (le_max_right _ _).trans ((le_max_left _ _).trans (hbudget i))
  have hE1 : ∀ i, (1 : ℝ) ≤ budget i := fun i => by
    have : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    exact this.trans (hEexp i)
  -- rewrite the means as margin integrals
  have hrw : ∀ i, (∫ ω, (nativeRecordingDurationNat X (budget i) (m+2) ω : ℝ) ∂μ) /
      (budget i * Real.log (budget i)) =
      ∫ r, normalizedFrozenMean X μ (budget i) r ∂
        (nativeTransientMarginProb μ hX (budget i) (m+2) : Measure ℝ) := fun i => by
    rw [nativeTransientMarginProb_coe]
    exact nativeRecordingDurationNat_normalizedMean_eq_margin_integral hX hi hG (hEpos i) (m+2)
  simp_rw [hrw]
  -- the weak convergence of the margin laws
  have hweak := nativeTransientMarginProb_tendsto hX hi hG hbudget hbudget_top hν (m+1)
  -- the uniform second moments
  have hsq : ∀ i, Integrable (fun r : ℝ => |r|^2)
      (nativeTransientMarginProb μ hX (budget i) (m+2) : Measure ℝ) := fun i =>
    (nativeTransientMarginLaw_abs_pow_le hX hi hG (hbudget i) (m+1) (k := 2) (by norm_num)).1
  have hM : ∀ i, (∫ r, |r|^2 ∂(nativeTransientMarginProb μ hX (budget i) (m+2) : Measure ℝ)) ≤
      transientMarginMomentBound (m+1) 2 := fun i =>
    (nativeTransientMarginLaw_abs_pow_le hX hi hG (hbudget i) (m+1) (k := 2) (by norm_num)).2
  refine tendsto_integral_of_transfer hweak transientRewardGrowthConstant_nonneg
    (fun i => (normalizedFrozenMean_aemeasurable_transientMarginLaw hX hi hG (budget i)
      (m+2)).aestronglyMeasurable)
    (fun i r => normalizedFrozenMean_nonneg hX hi hG (hE1 i))
    (fun i r => normalizedFrozenMean_le_growth hX hi hG (hEexp i) r)
    (marginLeadingReward_measurable_actual hX hi hG)
    (fun r => marginLeadingReward_nonneg hX hi hG)
    (marginLeadingReward_le_growth hX hi hG)
    (fun r hr => marginLeadingReward_continuousAt_of_ne_zero hX hi hG hr)
    (compProbIter_swingMarginKernel_singleton_zero hX hi hG ν m)
    hsq hM ?_
  intro δ C hδ ε hε
  exact normalizedFrozenMean_eventually_close_annulus hX hi hG hbudget_top hδ hε

end SwingRepair
