import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.CentralCutoff
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.Transfer

/-!
# Local pieces for the concrete leading-coefficient transfer

This file is kept separate from `PLAStochastic/Swing/StationaryLimit/LeadingCoefficient/Transfer.lean` while the
final theorem is assembled.  It contains the positive compact-annulus step in
a form that can be inserted into the four-region decomposition without any
extra measurability assumptions.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- Compact-uniform conditional means give the positive-annulus estimate after
the same compact cutoff is applied to the finite and limiting rewards. -/
theorem eventually_compactCutoff_positive_uniform_error
    {ι : Type*} {l : Filter ι} {budget : ι → ℝ}
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    (hbudget_top : Tendsto budget l atTop)
    {δ C ε : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ r ∈ Ioc δ (C + 1),
      |normalizedFrozenMean X μ (budget i) r * compactCutoff C r -
        marginLeadingReward_continuousCutoff X μ δ C r| < ε := by
  have hunif := normalizedFrozenMean_tendstoUniformlyOn_of_tendsto_budget
    (X := X) (μ := μ) hbudget_top (K := Icc 0 (C + 1))
      isCompact_Icc (by
        intro r hr
        exact (mem_Icc.mp hr).1) hX hi hG
  have hev := (Metric.tendstoUniformlyOn_iff.mp hunif) ε hε
  filter_upwards [hev] with i hi'
  intro r hr
  have hrδ : δ ≤ r := le_of_lt (mem_Ioc.mp hr).1
  have hr0 : 0 ≤ r := le_trans hδ.le hrδ
  have hrC : r ≤ C + 1 := (mem_Ioc.mp hr).2
  have hdiff :
      |normalizedFrozenMean X μ (budget i) r -
        4 * gaussianRenewalPotential X μ r| < ε := by
    simpa only [Real.dist_eq, abs_sub_comm] using hi' r (mem_Icc.mpr ⟨hr0, hrC⟩)
  have hRone : positiveMarginRamp δ r = 1 :=
    positiveMarginRamp_eq_one_of_ge hδ hrδ
  have hcut0 : 0 ≤ compactCutoff C r := compactCutoff_nonneg C r
  have hcut1 : compactCutoff C r ≤ 1 := compactCutoff_le_one C r
  have hq :
      marginLeadingReward_continuousCutoff X μ δ C r =
        (4 * gaussianRenewalPotential X μ r) * compactCutoff C r := by
    unfold marginLeadingReward_continuousCutoff
    rw [hRone, max_eq_left hr0]
    ring
  rw [hq]
  calc
    |normalizedFrozenMean X μ (budget i) r * compactCutoff C r -
        (4 * gaussianRenewalPotential X μ r) * compactCutoff C r| =
        |(normalizedFrozenMean X μ (budget i) r -
          4 * gaussianRenewalPotential X μ r) * compactCutoff C r| := by
      ring_nf
    _ = |normalizedFrozenMean X μ (budget i) r -
          4 * gaussianRenewalPotential X μ r| *
          |compactCutoff C r| := abs_mul _ _
    _ ≤ |normalizedFrozenMean X μ (budget i) r -
          4 * gaussianRenewalPotential X μ r| := by
      have hmul := mul_le_mul_of_nonneg_left hcut1
        (abs_nonneg (normalizedFrozenMean X μ (budget i) r -
          4 * gaussianRenewalPotential X μ r))
      simpa [abs_of_nonneg hcut0] using hmul
    _ < ε := hdiff

/-! A small region-reduction wrapper used on the limiting compact cutoff.  The
pointwise hypotheses are intentionally explicit: this keeps the proof
independent of any particular version of the cutoff API and is useful while
assembling the four-region estimate. -/
theorem integral_sub_le_of_compact_cutoff_regions
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    {f g : ℝ → ℝ} (hf : Integrable f ν) (hg : Integrable g ν)
    {δ C e : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) (hδC : δ ≤ C + 1)
    (he : 0 ≤ e)
    (hf0 : ∀ x, 0 ≤ f x)
    (hcentral :
      |(∫ x in Icc (-δ) δ, f x ∂ν) -
        ∫ x in Icc (-δ) δ, g x ∂ν| ≤ e)
    (hneg_f : ∀ x ∈ Iio (-δ), f x = 0)
    (hneg_g : ∀ x ∈ Iio (-δ), g x = 0)
    (hpos : ∀ x ∈ Ioc δ (C + 1), f x = g x)
    (hfar_f : ∀ x ∈ Ioi (C + 1), f x = 0)
    (hfar_g : ∀ x ∈ Ioi (C + 1), g x = 0) :
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| ≤ e := by
  have hfour := abs_integral_sub_le_of_central_negative_positive_far
    (ν := ν) (δ := δ) (R := C + 1) hδ.le hδC hf hg hf0
    (ec := e) (en := 0) (ep := 0) (ef := 0) he (by norm_num) (by norm_num)
    (by norm_num)
    hcentral hneg_g
    (by
      have hEq : (∫ x in Iio (-δ), f x ∂ν) =
          ∫ x in Iio (-δ), (fun _ : ℝ => (0 : ℝ)) x ∂ν :=
        setIntegral_congr_fun (μ := ν) measurableSet_Iio hneg_f
      rw [hEq]
      simp)
    (by
      intro x hx
      rw [hpos x hx]
      simp)
    hfar_g
    (by
      have hEq : (∫ x in Ioi (C + 1), f x ∂ν) =
          ∫ x in Ioi (C + 1), (fun _ : ℝ => (0 : ℝ)) x ∂ν :=
        setIntegral_congr_fun (μ := ν) measurableSet_Ioi hfar_f
      rw [hEq]
      simp)
  simpa using hfour

/-! A fully wired leading-coefficient entry point.  The only probabilistic
input left at this boundary is the explicit random-bridge estimate used by
the native margin-law limit theorem; the integral transfer itself is now
proved above from the actual stationary laws and their moment bounds. -/

theorem theorem_4_3_leading_coefficient_native_concrete [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    {πs : ι → Measure ℝ}
    (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i,
      (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    (hinputs : ∀ (f : ℝ → ℝ) (L B : ℝ), KernelLimit.IsBddLip f L B →
      ∀ (C ε : ℝ), 0 < ε →
        ∃ J : ℕ, ∃ δ : ℝ,
          1 ≤ J ∧ 0 ≤ δ ∧ 2 * B * δ ≤ ε / 2 ∧
          ∀ᶠ i in l, ∀ r : ℝ, |r| ≤ C →
            0 ≤ budget i ∧
            μ.real (prefixCrossingLowerBridgeEventRandom X (budget i) r J)ᶜ ≤ δ ∧
            |(∫ ω, f (prefixCrossingSubstitute X (budget i) r J ω) ∂μ) -
              ∫ y, f y ∂(swingMarginKernel X μ r)| ≤ ε / 2) :
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
  let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  obtain ⟨ν, hinv, hac, hca, hν, huniq⟩ :=
    theorem_4_3_margin_weak_limit_native_of_randomBridge
      (X := X) (μ := μ) hX hi hG hbudget hπP hπinv hinputs
  have htransfer := leadingCoefficient_integralTransfer_actual
    (X := X) (μ := μ) hX hi hG hbudget hbudget_top hπP hπinv hν hac
  have hbridge : ∀ i,
      (∫ x, nativeRestartMean X μ (budget i) x ∂(πs i)) /
          (budget i * Real.log (budget i)) =
        ∫ r, normalizedFrozenMean X μ (budget i) r ∂
          (stationaryMarginLaw (budget i) (πs i)) := by
    intro i
    let _ : IsProbabilityMeasure (πs i) := hπP i
    exact nativeRestart_normalizedMean_eq_margin_integral hX hi hG
  have hmean := theorem_4_3_leading_coefficient_actual
    (X := X) (μ := μ) (hπP := hπP) hν hbridge htransfer
  exact ⟨ν, hinv, hac, hca, hmean, huniq⟩

end LeadingCoefficient
end SwingRepair
