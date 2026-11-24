import PLAStochastic.Affine.Extrema.Contact.Observable
import PLAStochastic.Affine.Extrema.Contact.HeatIntegral
import PLAStochastic.Affine.Extrema.Contact.HeatLayerMeasure

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The actual first time, second lag, and terminal point measured from the old lower boundary. -/
def orderedContactMark {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (x r e : ℝ) (ω : Ω) : ℝ × ℝ × ℝ :=
  ((intervalTouchClock B x r ω : ℝ),(orderedContactLag B x r e ω : ℝ),x+B 1 ω)

/-- All marked-window tests are restrictions of the same actual layer and its
three actual observations. -/
theorem orderedContactLayer_iff_mark {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {x r e d : ℝ} (hr : 0 < r) (he : 0 < e) (hd : 0 < d)
    (S D₁ D₂ : Set ℝ) :
    orderedContactLayerEvent B x r e d 1 S D₁ D₂ ω ↔
      orderedContactLayerEvent B x r e d 1 univ univ univ ω ∧
        orderedContactMark B x r e ω ∈ D₁ ×ˢ D₂ ×ˢ S := by
  constructor
  · intro hE
    refine ⟨⟨⟨mem_univ _,hE.1.2⟩,hE.2.1,
      ⟨hE.2.2.1.1,hE.2.2.1.2.1,mem_univ _⟩,mem_univ _⟩,?_,?_,?_⟩
    · exact hE.1.1
    · exact hE.2.2.2
    · exact (orderedContactLayer_geometry hc hr he hd hE).2.2
  · rintro ⟨hE,hD₁,hD₂,hS⟩
    let s := intervalTouchClock B x r ω
    have hs : s < 1 := by exact_mod_cast hE.1.2.2
    have hz : x+B s ω=0 := hE.2.1
    have hrec : brownianRestartAt B (intervalTouchTime B x r) (1-s) ω=x+B 1 ω := by
      change B (s+(1-s)) ω-B s ω=x+B 1 ω
      rw [add_tsub_cancel_of_le hs.le]
      linarith
    refine ⟨⟨hD₁,hE.1.2⟩,hE.2.1,⟨hE.2.2.1.1,hE.2.2.1.2.1,?_⟩,hD₂⟩
    change e+brownianRestartAt B (intervalTouchTime B x r) (1-s) ω-e ∈ S
    rw [add_sub_cancel_left,hrec]
    exact hS

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem aemeasurable_orderedContactVector (hB : IsBrownianReal B μ) (x r e : ℝ) :
    AEMeasurable (orderedContactVector B x r e) μ := by
  apply (measurable_orderedContactVector_comp (measurable_continuousBrownianPath hB)
    measurable_const measurable_const measurable_const).aemeasurable.congr
  filter_upwards [continuousBrownianPath_all_times_ae_eq hB] with ω hω
  exact orderedContactVector_congr_paths (B := continuousPathProcess) (C := B)
    (ω := continuousBrownianPath hB ω) (ξ := ω) hω x r e

theorem aemeasurable_orderedContactMark (hB : IsBrownianReal B μ) (x r e : ℝ) :
    AEMeasurable (orderedContactMark B x r e) μ := by
  have hv := aemeasurable_orderedContactVector hB x r e
  have hmark := hv.snd.snd.fst.prodMk
    ((hv.snd.snd.snd.fst.sub hv.snd.snd.fst).prodMk ((aemeasurable_const (b := x)).add hv.snd.snd.snd.snd))
  convert hmark using 1
  funext ω
  simp only [orderedContactMark,orderedContactVector,Pi.sub_apply,Pi.add_apply,add_sub_cancel_left]

theorem nullMeasurableSet_orderedContactLayer (hB : IsBrownianReal B μ) (x r e d : ℝ) :
    NullMeasurableSet {ω | orderedContactLayerEvent B x r e d 1 univ univ univ ω} μ := by
  have hm := aemeasurable_orderedContactTest_comp (B := B) (f := processPath B)
    (x := fun _ => x) (r := fun _ => r) (e := fun _ => e) (d := fun _ => d)
    (aemeasurable_processPath hB)
    (hB.cont.mono (fun ω hc t => processPath_apply_of_continuous hc t))
    aemeasurable_const aemeasurable_const aemeasurable_const aemeasurable_const
    (φ := fun _ => 1) measurable_const
  have hn := hm.nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ))
  convert hn using 1
  ext ω
  simp only [mem_ofPred_eq,mem_preimage,mem_singleton_iff,orderedContactTest]
  split_ifs <;> simp_all

/-- The actual marked-layer law, with its terminal observation restricted to the
old interval as required by the interior heat representation. -/
def orderedContactMarkMeasure (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (x r e d : ℝ) :
    Measure (ℝ × ℝ × ℝ) :=
  (μ.restrict {ω | orderedContactLayerEvent B x r e d 1 (Icc 0 r) univ univ ω}).map
    (orderedContactMark B x r e)

/-- Every Borel rectangle of the actual marked law is exactly its true layer probability. -/
theorem orderedContactMarkMeasure_apply_rectangle (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (he : 0 < e) (hd : 0 < d)
    {S D₁ D₂ : Set ℝ} (hS : MeasurableSet S) (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) :
    orderedContactMarkMeasure B μ x r e d (D₁ ×ˢ D₂ ×ˢ S)=
      μ {ω | orderedContactLayerEvent B x r e d 1 (S ∩ Icc 0 r) D₁ D₂ ω} := by
  rw [orderedContactMarkMeasure,Measure.map_apply_of_aemeasurable
    (aemeasurable_orderedContactMark hB x r e).restrict (hD₁.prod (hD₂.prod hS)),
    Measure.restrict_apply₀ ((aemeasurable_orderedContactMark hB x r e).restrict.nullMeasurableSet_preimage
      (hD₁.prod (hD₂.prod hS)))]
  apply measure_congr
  filter_upwards [hB.cont] with ω hc
  apply propext
  change (orderedContactMark B x r e ω ∈ D₁ ×ˢ D₂ ×ˢ S ∧
    orderedContactLayerEvent B x r e d 1 (Icc 0 r) univ univ ω) ↔
      orderedContactLayerEvent B x r e d 1 (S ∩ Icc 0 r) D₁ D₂ ω
  rw [orderedContactLayer_iff_mark hc hr he hd (Icc 0 r) univ univ,
    orderedContactLayer_iff_mark hc hr he hd (S ∩ Icc 0 r) D₁ D₂]
  simp only [orderedContactMark,mem_prod,mem_univ,true_and,mem_inter_iff]
  tauto

/-- The real Brownian marked-contact measure equals the analytic three-kernel
measure. This is identification of an actual stopped-path distribution. -/
theorem orderedContactMarkMeasure_eq_heatLayer (hB : IsBrownianReal B μ)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d) :
    orderedContactMarkMeasure B μ x r e d = orderedHeatLayerMeasure r e d 1 x := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (orderedContactMarkMeasure B μ x r e d) := by
    unfold orderedContactMarkMeasure
    infer_instance
  apply Measure.ext_prod₃
  intro D₁ D₂ S hD₁ hD₂ hS
  rw [orderedContactMarkMeasure_apply_rectangle hB hr he hd hS hD₁ hD₂,
    measure_orderedContactLayer_eq_heat_integral hB hr hx he hd (by norm_num : (0 : ℝ≥0) < 1)
      (hS.inter measurableSet_Icc) inter_subset_right hD₁ hD₂,
    orderedHeatLayerMeasure_apply_prod hr hx he hD₁ hD₂ hS]
  rfl

end BrownianAffine
