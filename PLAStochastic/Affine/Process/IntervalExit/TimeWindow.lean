import PLAStochastic.Affine.Process.IntervalExit.KilledConvolution

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem indicator_test_integral {X : Type*} [MeasurableSpace X]
    {f : Ω → X} (hf : AEMeasurable f μ) {S : Set X} (hS : MeasurableSet S) :
    (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (f ω) ∂μ) = μ (f ⁻¹' S) := by
  have he : (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (f ω)) =
      (f ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases h : f ω ∈ S <;> simp [indicator,h]
  rw [he,lintegral_indicator_const₀ (hf.nullMeasurableSet_preimage hS),one_mul]

/-- The actual domain increment retains its first-exit time on every Borel time set. -/
theorem measure_new_survival_timeSet_eq_continuation (hB : IsBrownianReal B μ)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {T : ℝ≥0} (hT : 0 < T) {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) :
    μ {ω | ((T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S) ∧
        (intervalTouchClock B x r ω : ℝ) ∈ D} =
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryRight r s x/2)*
        D.indicator (fun s => μ {ω | ((s,r),unitPath (processPath B ω) T) ∈
          upperContinuationSet T r R S}) s := by
  let V : Set ((ℝ × ℝ) × Path 1) := upperContinuationSet T r R S ∩
    (fun p => p.1.1) ⁻¹' D
  let G := V.indicator (fun _ => (1 : ℝ≥0∞))
  have hV : MeasurableSet V := (measurableSet_upperContinuationSet (T : ℝ) r R hS).inter
    (hD.preimage (measurable_fst.comp measurable_fst))
  have hmJ := ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk
    (intervalTouchEndpoint_aemeasurable hB hr hx)
  have hmP := aemeasurable_brownianUnitPath (isBrownianReal_restart_intervalTouch hB x hr) T
  have h := lintegral_intervalTouch_futurePath_boundary hB hr hx T (G := G) (measurable_const.indicator hV)
  have hleft (s : ℝ) : (∫⁻ ω, G ((s,0),unitPath (processPath B ω) T) ∂μ)=0 := by
    simp [G,V,upperContinuationSet,ne_of_lt hr]
  have hright (s : ℝ) : (∫⁻ ω, G ((s,r),unitPath (processPath B ω) T) ∂μ)=
      D.indicator (fun s => μ {ω | ((s,r),unitPath (processPath B ω) T) ∈
        upperContinuationSet T r R S}) s := by
    rw [indicator_test_integral (aemeasurable_const.prodMk (aemeasurable_brownianUnitPath hB T)) hV]
    by_cases hs : s ∈ D
    · rw [indicator_of_mem hs]
      congr 1
      ext ω
      simp only [V,mem_preimage,mem_inter_iff,hs,and_true,mem_ofPred_eq]
    · rw [indicator_of_notMem hs]
      have he : (fun ω => ((s,r),unitPath (processPath B ω) T)) ⁻¹' V = ∅ := by
        ext ω
        simp [V,hs]
      rw [he,measure_empty]
  change (∫⁻ ω, G _ ∂μ) = _ at h
  rw [indicator_test_integral (hmJ.prodMk hmP) hV] at h
  simp_rw [hleft,hright,mul_zero,lintegral_zero,zero_add] at h
  have he : μ {ω | (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T) ∈ V} =
      μ {ω | ((T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S) ∧
        (intervalTouchClock B x r ω : ℝ) ∈ D} := by
    apply measure_congr
    filter_upwards [upperContinuationSet_actual_ae_iff hB hr hx hrR hT S] with ω hi
    apply propext
    exact and_congr_left (fun _ => hi)
  exact he.symm.trans h

/-- Time-window-resolved first-exit decomposition, with the true remaining-time
killed law, for every Borel time window and every Borel endpoint test. -/
theorem measure_new_survival_timeSet_eq_killed_convolution (hB : IsBrownianReal B μ)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {T : ℝ≥0} (hT : 0 < T) {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) :
    μ {ω | ((T : ℝ≥0∞) < intervalTouchTime B x R ω ∧
        intervalTouchTime B x r ω ≤ T ∧ x+B T ω ∈ S) ∧
        (intervalTouchClock B x r ω : ℝ) ∈ D} =
      ∫⁻ s in D ∩ Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (heatBoundaryRight r s x/2)*
        killedBrownianMeasure B μ r R (T-Real.toNNReal s) S := by
  rw [measure_new_survival_timeSet_eq_continuation hB hr hx hrR hT hS hD]
  calc
    _ = ∫⁻ s in D ∩ Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryRight r s x/2)*
        μ {ω | ((s,r),unitPath (processPath B ω) T) ∈ upperContinuationSet T r R S} := by
      rw [← setLIntegral_indicator hD]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ D <;> simp [hs]
    _ = _ := by
      have hi : Iio (T : ℝ) ∩ (D ∩ Ioi (0 : ℝ)) = D ∩ Ioo (0 : ℝ) (T : ℝ) := by
        ext s
        simp only [mem_inter_iff,mem_Iio,mem_Ioi,mem_Ioo]
        tauto
      rw [← hi,← setLIntegral_indicator measurableSet_Iio]
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hD.inter measurableSet_Ioi),
        ae_restrict_of_ae (volume.ae_ne (T : ℝ))] with s hs hne
      by_cases hsT : s < (T : ℝ)
      · rw [indicator_of_mem (show s ∈ Iio (T : ℝ) from hsT)]
        congr 1
        have hsN : Real.toNNReal s < T := by
          exact_mod_cast (show (Real.toNNReal s : ℝ) < (T : ℝ) by
            rwa [Real.coe_toNNReal _ hs.2.le])
        simpa only [Real.coe_toNNReal _ hs.2.le] using
          upperContinuationSet_fixed_time_measure hB hr hrR hT hsN hS
      · have hgt : (T : ℝ) < s := lt_of_le_of_ne (le_of_not_gt hsT) hne.symm
        have hm : μ {ω | ((s,r),unitPath (processPath B ω) T) ∈ upperContinuationSet T r R S}=0 := by
          simp [upperContinuationSet,not_le.mpr hgt]
        rw [hm,mul_zero,indicator_of_notMem (show s ∉ Iio (T : ℝ) from hsT)]

end BrownianAffine
