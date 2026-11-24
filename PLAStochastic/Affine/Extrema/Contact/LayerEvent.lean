import PLAStochastic.Affine.Process.IntervalExit.SecondExit

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A true two-contact boundary layer: the path first exits (0,r) at zero, then
its future exits (-e,r) at r, and finally survives in (-e,r+d). Both contact-time
windows and the terminal-position test are retained. The second time is a lag. -/
def orderedContactLayerEvent {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (x r e d : ℝ) (T : ℝ≥0) (S D₁ D₂ : Set ℝ) (ω : Ω) : Prop :=
  let s := intervalTouchClock B x r ω
  let W := brownianRestartAt B (intervalTouchTime B x r)
  (s : ℝ) ∈ D₁ ∩ Ioo (0 : ℝ) (T : ℝ) ∧ intervalTouchEndpoint B x r ω=0 ∧
    ((((T-s : ℝ≥0) : ℝ≥0∞) < intervalTouchTime W e (r+e+d) ω ∧
      intervalTouchTime W e (r+e) ω ≤ (T-s : ℝ≥0) ∧
      e+W (T-s) ω ∈ (fun z => z-e) ⁻¹' S) ∧
      (intervalTouchClock W e (r+e) ω : ℝ) ∈ D₂)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

private theorem integral_indicator_reading {X : Type*} [MeasurableSpace X]
    {f : Ω → X} (hf : AEMeasurable f μ) {A : Set X} (hA : MeasurableSet A) :
    (∫⁻ ω, A.indicator (fun _ => (1 : ℝ≥0∞)) (f ω) ∂μ)=μ (f ⁻¹' A) := by
  have he : (fun ω => A.indicator (fun _ => (1 : ℝ≥0∞)) (f ω)) =
      (f ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext ω
    by_cases h : f ω ∈ A <;> simp [indicator,h]
  rw [he,lintegral_indicator_const₀ (hf.nullMeasurableSet_preimage hA),one_mul]

/-- Strong Markov at the first lower contact, followed by the actual second-contact
path test; no conditional exit law is supplied as an assumption. -/
theorem measure_orderedContactLayer_eq_first_integral (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d)
    {T : ℝ≥0} (hT : 0 < T) {S D₁ D₂ : Set ℝ}
    (hS : MeasurableSet S) (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) :
    μ {ω | orderedContactLayerEvent B x r e d T S D₁ D₂ ω} =
      ∫⁻ s in D₁ ∩ Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (heatBoundaryLeft r s x/2)*
        μ {ω | (s,unitPath (processPath B ω) T) ∈
          newSurvivalPathSet T e (r+e) (r+e+d) ((fun z => z-e) ⁻¹' S) D₂} := by
  let D := D₁ ∩ Ioo (0 : ℝ) (T : ℝ)
  let A := newSurvivalPathSet T e (r+e) (r+e+d) ((fun z => z-e) ⁻¹' S) D₂
  let V : Set ((ℝ × ℝ) × Path 1) := {p | p.1.1 ∈ D ∧ p.1.2=0 ∧ (p.1.1,p.2) ∈ A}
  let G := V.indicator (fun _ => (1 : ℝ≥0∞))
  have hD : MeasurableSet D := hD₁.inter measurableSet_Ioo
  have hA : MeasurableSet A := measurableSet_newSurvivalPathSet T e
    (by linarith) (by linarith) (hS.preimage (by fun_prop)) hD₂
  have hV : MeasurableSet V :=
    (hD.preimage (measurable_fst.comp measurable_fst)).inter
      ((measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).inter
        (hA.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  have hmJ := ((intervalTouchClock_aemeasurable hB hr x).coe_nnreal_real).prodMk
    (intervalTouchEndpoint_aemeasurable hB hr hx)
  have hmP := aemeasurable_brownianUnitPath (isBrownianReal_restart_intervalTouch hB x hr) T
  have h := lintegral_intervalTouch_futurePath_boundary hB hr hx T (G := G) (measurable_const.indicator hV)
  have hright (s : ℝ) : (∫⁻ ω, G ((s,r),unitPath (processPath B ω) T) ∂μ)=0 := by
    simp [G,V,hr.ne']
  have hleft (s : ℝ) : (∫⁻ ω, G ((s,0),unitPath (processPath B ω) T) ∂μ)=
      D.indicator (fun s => μ {ω | (s,unitPath (processPath B ω) T) ∈ A}) s := by
    rw [integral_indicator_reading (aemeasurable_const.prodMk (aemeasurable_brownianUnitPath hB T)) hV]
    by_cases hs : s ∈ D
    · rw [indicator_of_mem hs]
      congr 1
      ext ω
      simp only [V,mem_preimage,mem_ofPred_eq,hs,true_and]
    · rw [indicator_of_notMem hs]
      have hz : (fun ω => ((s,0),unitPath (processPath B ω) T)) ⁻¹' V=∅ := by
        ext ω
        simp [V,hs]
      rw [hz,measure_empty]
  change (∫⁻ ω, G _ ∂μ)=_ at h
  rw [integral_indicator_reading (hmJ.prodMk hmP) hV] at h
  simp_rw [hleft,hright,mul_zero,lintegral_zero,add_zero] at h
  have hactual : μ {ω | (((intervalTouchClock B x r ω : ℝ),intervalTouchEndpoint B x r ω),
      unitPath (processPath (brownianRestartAt B (intervalTouchTime B x r)) ω) T) ∈ V} =
      μ {ω | orderedContactLayerEvent B x r e d T S D₁ D₂ ω} := by
    apply measure_congr
    filter_upwards [(isBrownianReal_restart_intervalTouch hB x hr).cont] with ω hc
    have hi := newSurvivalPathSet_actual_iff hc hT e (by linarith : 0 < r+e)
      (by linarith : 0 < r+e+d) ((fun z => z-e) ⁻¹' S) D₂ (intervalTouchClock B x r ω : ℝ)
    simp only [Real.toNNReal_coe] at hi
    apply propext
    exact and_congr_right (fun _ => and_congr_right (fun _ => hi))
  refine hactual.symm.trans (h.trans ?_)
  have hI : D ∩ Ioi (0 : ℝ)=D := inter_eq_left.mpr (fun _ hs => hs.2.1)
  calc
    _ = ∫⁻ s in Ioi (0 : ℝ), D.indicator
        (fun s => ENNReal.ofReal (heatBoundaryLeft r s x/2)*
          μ {ω | (s,unitPath (processPath B ω) T) ∈ A}) s := by
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ D <;> simp [hs]
    _ = ∫⁻ s in D ∩ Ioi (0 : ℝ), ENNReal.ofReal (heatBoundaryLeft r s x/2)*
        μ {ω | (s,unitPath (processPath B ω) T) ∈ A} := setLIntegral_indicator hD _
    _ = _ := by rw [hI]

/-- The actual two-contact layer has the exact iterated boundary-density law,
with both time windows and arbitrary Borel endpoint observations. -/
theorem measure_orderedContactLayer_eq_double_convolution (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d)
    {T : ℝ≥0} (hT : 0 < T) {S D₁ D₂ : Set ℝ}
    (hS : MeasurableSet S) (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) :
    μ {ω | orderedContactLayerEvent B x r e d T S D₁ D₂ ω} =
      ∫⁻ s in D₁ ∩ Ioo (0 : ℝ) (T : ℝ), ENNReal.ofReal (heatBoundaryLeft r s x/2)*
        ∫⁻ v in D₂ ∩ Ioo (0 : ℝ) ((T-Real.toNNReal s : ℝ≥0) : ℝ),
          ENNReal.ofReal (heatBoundaryRight (r+e) v e/2)*
            killedBrownianMeasure B μ (r+e) (r+e+d)
              ((T-Real.toNNReal s)-Real.toNNReal v) ((fun z => z-e) ⁻¹' S) := by
  rw [measure_orderedContactLayer_eq_first_integral hB hr hx he hd hT hS hD₁ hD₂]
  apply setLIntegral_congr_fun (hD₁.inter measurableSet_Ioo)
  intro s hs
  dsimp only
  congr 1
  exact measure_newSurvivalPathSet_eq_convolution hB (by linarith : 0 < r+e)
    (show e ∈ Ioo 0 (r+e) from ⟨he,by linarith⟩) (by linarith)
    hT hs.2 (hS.preimage (by fun_prop)) hD₂

end BrownianAffine
