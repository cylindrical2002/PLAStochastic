import PLAStochastic.Affine.Process.IntervalExit.Continuation

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem lintegral_indicator_comp_aemeasurable {X : Type*} [MeasurableSpace X]
    {f : Ω → X} (hf : AEMeasurable f μ) {S : Set X} (hS : MeasurableSet S) :
    (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (f ω) ∂μ) = μ (f ⁻¹' S) := by
  have he : (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (f ω)) =
      (f ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases h : f ω ∈ S <;> simp [indicator,h]
  rw [he,lintegral_indicator_const₀ (hf.nullMeasurableSet_preimage hS),one_mul]

/-- The true domain-survival increment is integrated over the genuine upper exit-time
law. The inner probability is a measurable test on a fresh Brownian path. -/
theorem measure_new_survival_eq_continuation_integral (hB : IsBrownianReal B μ)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {T : ℝ≥0} (hT : 0 < T) {S : Set ℝ} (hS : MeasurableSet S) :
    μ {ω | (T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S} =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryRight r s x/2)*
        μ {ω | ((s,r),unitPath (processPath B ω) T) ∈ upperContinuationSet T r R S} := by
  let G := (upperContinuationSet T r R S).indicator (fun _ => (1 : ℝ≥0∞))
  have hU := measurableSet_upperContinuationSet (T : ℝ) r R hS
  have hmJ := ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk
    (intervalTouchEndpoint_aemeasurable hB hr hx)
  have hmP := aemeasurable_brownianUnitPath (isBrownianReal_restart_intervalTouch hB x hr) T
  have h := lintegral_intervalTouch_futurePath_boundary hB hr hx T (G := G) (measurable_const.indicator hU)
  have hleft (s : ℝ) : (∫⁻ ω, G ((s,0),unitPath (processPath B ω) T) ∂μ)=0 := by
    simp [G,upperContinuationSet,ne_of_lt hr]
  have hright (s : ℝ) : (∫⁻ ω, G ((s,r),unitPath (processPath B ω) T) ∂μ)=
      μ {ω | ((s,r),unitPath (processPath B ω) T) ∈ upperContinuationSet T r R S} :=
    lintegral_indicator_comp_aemeasurable
      (aemeasurable_const.prodMk (aemeasurable_brownianUnitPath hB T)) hU
  change (∫⁻ ω, G _ ∂μ) = _ at h
  rw [lintegral_indicator_comp_aemeasurable (hmJ.prodMk hmP) hU] at h
  simp_rw [hleft,hright,mul_zero,lintegral_zero,zero_add] at h
  have he : μ {ω | (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T) ∈
        upperContinuationSet T r R S} =
      μ {ω | (T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S} :=
    measure_congr ((upperContinuationSet_actual_ae_iff hB hr hx hrR hT S).mono
      (fun _ hi => propext hi))
  exact he.symm.trans h

/-- A genuine domain-variation convolution: the new survival probability equals
upper first-contact density times the actual remaining-time killed endpoint law. -/
theorem measure_new_survival_eq_killed_convolution (hB : IsBrownianReal B μ)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {T : ℝ≥0} (hT : 0 < T) {S : Set ℝ} (hS : MeasurableSet S) :
    μ {ω | (T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S} =
      ∫⁻ s in Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (heatBoundaryRight r s x/2)*
        killedBrownianMeasure B μ r R (T-Real.toNNReal s) S := by
  rw [measure_new_survival_eq_continuation_integral hB hr hx hrR hT hS]
  have hi : Iio (T : ℝ) ∩ Ioi (0 : ℝ) = Ioo (0 : ℝ) (T : ℝ) := by
    ext s
    simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo,and_comm]
  rw [← hi,← setLIntegral_indicator measurableSet_Iio]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae (volume.ae_ne (T : ℝ))] with s hs hne
  by_cases hsT : s < (T : ℝ)
  · rw [indicator_of_mem (show s ∈ Iio (T : ℝ) from hsT)]
    congr 1
    have hsN : Real.toNNReal s < T := by
      exact_mod_cast (show (Real.toNNReal s : ℝ) < (T : ℝ) by
        rwa [Real.coe_toNNReal _ hs.le])
    simpa only [Real.coe_toNNReal _ hs.le] using
      upperContinuationSet_fixed_time_measure hB hr hrR hT hsN hS
  · have hgt : (T : ℝ) < s := lt_of_le_of_ne (le_of_not_gt hsT) hne.symm
    have hm : μ {ω | ((s,r),unitPath (processPath B ω) T) ∈ upperContinuationSet T r R S}=0 := by
      simp [upperContinuationSet,not_le.mpr hgt]
    rw [hm,mul_zero,indicator_of_notMem (show s ∉ Iio (T : ℝ) from hsT)]

end BrownianAffine
