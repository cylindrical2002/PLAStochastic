import PLAStochastic.Affine.Extrema.Contact.ContinuousTouch
import PLAStochastic.Affine.Extrema.Contact.ClockLocalization

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Contact times depend on the actual sample path alone. -/
theorem intervalTouchTime_congr_paths {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (h : ∀ t, B t ω=C t ξ) (x r : ℝ) :
    intervalTouchTime B x r ω=intervalTouchTime C x r ξ := by
  unfold intervalTouchTime
  apply iInf_congr
  intro t
  rw [h t]

theorem restartAtTouch_congr_paths {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (h : ∀ t, B t ω=C t ξ) (x r : ℝ) (t : ℝ≥0) :
    brownianRestartAt B (intervalTouchTime B x r) t ω =
      brownianRestartAt C (intervalTouchTime C x r) t ξ := by
  simp only [brownianRestartAt,brownianRestart,intervalTouchTime_congr_paths h,h]

theorem orderedContactLayer_congr_paths {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (h : ∀ t, B t ω=C t ξ) (x r e d : ℝ) (T : ℝ≥0) (S D₁ D₂ : Set ℝ) :
    orderedContactLayerEvent B x r e d T S D₁ D₂ ω ↔
      orderedContactLayerEvent C x r e d T S D₁ D₂ ξ := by
  simp only [orderedContactLayerEvent,intervalTouchEndpoint,intervalTouchClock,
    intervalTouchTime_congr_paths h,intervalTouchTime_congr_paths (restartAtTouch_congr_paths h x r),
    restartAtTouch_congr_paths h,h]

/-- The observable has the same coordinate order as the actual extrema vector;
the fourth coordinate is the absolute second contact time. -/
def orderedContactVector {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (x r e : ℝ) (ω : Ω) : ExtremaVector :=
  (-x,r-x,(intervalTouchClock B x r ω : ℝ),
    (intervalTouchClock B x r ω : ℝ)+(orderedContactLag B x r e ω : ℝ),B 1 ω)

def orderedContactTest {Ω : Type*} (φ : ExtremaVector → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (x r e d : ℝ) (ω : Ω) : ℝ := by
  classical
  exact if orderedContactLayerEvent B x r e d 1 univ univ univ ω then
    φ (orderedContactVector B x r e ω) else 0

theorem measurable_orderedContactVector_comp {α : Type*} [MeasurableSpace α]
    {f : α → C(ℝ,ℝ)} {x r e : α → ℝ}
    (hf : Measurable f) (hx : Measurable x) (hr : Measurable r) (he : Measurable e) :
    Measurable (fun a => orderedContactVector continuousPathProcess (x a) (r a) (e a) (f a)) := by
  have hs := measurable_continuousPathClock_comp hf hx hr
  have hF := continuous_restartContinuousPath.measurable.comp (hf.prodMk hs.coe_nnreal_real)
  have hv := measurable_continuousPathClock_comp hF he (hr.add he)
  exact hx.neg.prodMk ((hr.sub hx).prodMk (hs.coe_nnreal_real.prodMk
    ((hs.coe_nnreal_real.add hv.coe_nnreal_real).prodMk
      ((continuous_eval_const (1 : ℝ)).measurable.comp hf))))

theorem measurable_orderedContactTest_comp {α : Type*} [MeasurableSpace α]
    {f : α → C(ℝ,ℝ)} {x r e d : α → ℝ}
    (hf : Measurable f) (hx : Measurable x) (hr : Measurable r)
    (he : Measurable e) (hd : Measurable d) {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    Measurable (fun a => orderedContactTest φ continuousPathProcess
      (x a) (r a) (e a) (d a) (f a)) := by
  exact (hφ.comp (measurable_orderedContactVector_comp hf hx hr he)).ite
    (measurableSet_continuousPath_orderedContactLayer hf hx hr he hd 1
      MeasurableSet.univ MeasurableSet.univ MeasurableSet.univ) measurable_const

theorem orderedContactVector_congr_paths {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (h : ∀ t, B t ω=C t ξ) (x r e : ℝ) :
    orderedContactVector B x r e ω=orderedContactVector C x r e ξ := by
  simp only [orderedContactVector,orderedContactLag,intervalTouchClock,
    intervalTouchTime_congr_paths h,intervalTouchTime_congr_paths (restartAtTouch_congr_paths h x r),h]

/-- Joint AE measurability of the actual layer observable from one measurable
continuous-path representative, uniform over all measurable level choices. -/
theorem aemeasurable_orderedContactTest_of_path_representation {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {B : ℝ≥0 → α → ℝ} {f : α → C(ℝ,ℝ)} {x r e d : α → ℝ}
    (hf : Measurable f) (hrep : ∀ᵐ a ∂ν, ∀ t : ℝ≥0, f a t=B t a)
    (hx : Measurable x) (hr : Measurable r) (he : Measurable e) (hd : Measurable d)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    AEMeasurable (fun a => orderedContactTest φ B (x a) (r a) (e a) (d a) a) ν := by
  apply (measurable_orderedContactTest_comp hf hx hr he hd hφ).aemeasurable.congr
  filter_upwards [hrep] with a ha
  have hpath : ∀ t, continuousPathProcess t (f a)=B t a := ha
  simp only [orderedContactTest,orderedContactVector_congr_paths hpath]
  rw [propext (orderedContactLayer_congr_paths hpath (x a) (r a) (e a) (d a)
    1 univ univ univ)]

theorem norm_orderedContactTest_le {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (x r e d : ℝ) (ω : Ω) {φ : ExtremaVector → ℝ} {M : ℝ}
    (hM : ∀ p, ‖φ p‖ ≤ M) : ‖orderedContactTest φ B x r e d ω‖ ≤ M := by
  have h0 : 0 ≤ M := (norm_nonneg (φ (0,0,0,0,0))).trans (hM _)
  unfold orderedContactTest
  split_ifs
  · exact hM _
  · simpa using h0

/-- The same joint observable theorem for AE measurable parameters. -/
theorem aemeasurable_orderedContactTest_comp {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {B : ℝ≥0 → α → ℝ} {f : α → C(ℝ,ℝ)} {x r e d : α → ℝ}
    (hf : AEMeasurable f ν) (hrep : ∀ᵐ a ∂ν, ∀ t : ℝ≥0, f a t=B t a)
    (hx : AEMeasurable x ν) (hr : AEMeasurable r ν)
    (he : AEMeasurable e ν) (hd : AEMeasurable d ν)
    {φ : ExtremaVector → ℝ} (hφ : Measurable φ) :
    AEMeasurable (fun a => orderedContactTest φ B (x a) (r a) (e a) (d a) a) ν := by
  have hrep' : ∀ᵐ a ∂ν, ∀ t : ℝ≥0, hf.mk f a t=B t a := by
    filter_upwards [hrep,hf.ae_eq_mk] with a ha hfa
    rwa [←hfa]
  apply (aemeasurable_orderedContactTest_of_path_representation hf.measurable_mk hrep'
    hx.measurable_mk hr.measurable_mk he.measurable_mk hd.measurable_mk hφ).congr
  filter_upwards [hx.ae_eq_mk,hr.ae_eq_mk,he.ae_eq_mk,hd.ae_eq_mk] with a hxa hra hea hda
  rw [hxa,hra,hea,hda]

/-- A continuous test of the layer is also invariant under sample-path equality. -/
theorem orderedContactTest_congr_paths {Ω Ξ : Type*}
    {B : ℝ≥0 → Ω → ℝ} {C : ℝ≥0 → Ξ → ℝ} {ω : Ω} {ξ : Ξ}
    (h : ∀ t, B t ω=C t ξ) (x r e d : ℝ) (φ : ExtremaVector → ℝ) :
    orderedContactTest φ B x r e d ω=orderedContactTest φ C x r e d ξ := by
  unfold orderedContactTest
  rw [propext (orderedContactLayer_congr_paths h x r e d 1 univ univ univ),
    orderedContactVector_congr_paths h]

end BrownianAffine
