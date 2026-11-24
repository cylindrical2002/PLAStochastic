import PLAStochastic.Affine.Process.IntervalExit.JointLaw
import PLAStochastic.Affine.Extrema.Interior

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The actual minimum and maximum remain strictly between the prescribed levels. -/
def brownianExtremaBox {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (l h : ℝ) (ω : Ω) : Prop :=
  l < slopeLower (unitPath (processPath B ω) 1) 0 ∧
    slopeUpper (unitPath (processPath B ω) 1) 0 < h

private theorem extremaBox_iff_path_range (g : Path 1) (l h : ℝ) :
    (l < slopeLower g 0 ∧ slopeUpper g 0 < h) ↔ ∀ t : RangeTime, g t ∈ Ioo l h := by
  constructor
  · intro hg t
    have hl := slopeLower_le_residual g 0 t
    have hu := slopeResidual_le_upper g 0 t
    simp only [slopeResidual,zero_mul,sub_zero] at hl hu
    exact ⟨hg.1.trans_le hl,hu.trans_lt hg.2⟩
  · intro hg
    have hl := hg (lowerTime g 0)
    have hu := hg (upperTime g 0)
    have hla := lowerTime_attains g 0
    have hua := upperTime_attains g 0
    simp only [slopeResidual,zero_mul,sub_zero] at hla hua
    exact ⟨by rw [← hla]; exact hl.1,by rw [← hua]; exact hu.2⟩

private theorem unitPath_eval_nnreal {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (t : RangeTime) :
    unitPath (processPath B ω) 1 t = B (⟨t,t.property.1⟩ : ℝ≥0) ω := by
  have h := slopeResidual_actual_unit B hc 0 (⟨t,t.property.1⟩ : ℝ≥0)
    (by exact_mod_cast t.property.2)
  have he : nnrealRangeTime (⟨t,t.property.1⟩ : ℝ≥0) (by exact_mod_cast t.property.2) = t := Subtype.ext rfl
  simpa only [slopeResidual,zero_mul,sub_zero,he] using h

/-- Path extrema and the continuously observed interval-survival event are identical. -/
theorem brownianExtremaBox_iff_all_times {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (l h : ℝ) :
    brownianExtremaBox B l h ω ↔ ∀ t : ℝ≥0, t ≤ 1 → B t ω ∈ Ioo l h := by
  rw [brownianExtremaBox,extremaBox_iff_path_range]
  constructor
  · intro hb t ht
    have hv := hb (nnrealRangeTime t ht)
    rwa [unitPath_eval_nnreal hc] at hv
  · intro hb t
    rw [unitPath_eval_nnreal hc]
    exact hb _ (by exact_mod_cast t.property.2)

theorem brownianExtremaBox_iff_touch_gt {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {l h : ℝ} (hlh : l < h) :
    brownianExtremaBox B l h ω ↔ (1 : ℝ≥0∞) < intervalTouchTime B (-l) (h-l) ω := by
  have ht : (1 : ℝ≥0∞) < intervalTouchTime B (-l) (h-l) ω ↔
      ∀ t : ℝ≥0, t ≤ 1 → -l+B t ω ∈ Ioo 0 (h-l) := by
    have hl := intervalTouchTime_le_iff hc (sub_pos.mpr hlh) (1 : ℝ≥0) (x := -l)
    simp only [ENNReal.coe_one] at hl
    rw [← not_le,hl]
    push Not
    rfl
  rw [ht,brownianExtremaBox_iff_all_times hc]
  constructor
  · intro hb t ht
    have h := hb t ht
    constructor <;> linarith [h.1,h.2]
  · intro hb t ht
    have h := hb t ht
    constructor <;> linarith [h.1,h.2]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem brownianExtremaBox_nullMeasurableSet (hB : IsBrownianReal B μ) (l h : ℝ) :
    NullMeasurableSet {ω | brownianExtremaBox B l h ω} μ := by
  have hl : AEMeasurable (fun ω => slopeLower (unitPath (processPath B ω) 1) 0) μ :=
    ((slopeLower_joint_lipschitz.continuous.measurable).comp (f := fun g : Path 1 => (g,0)) (by fun_prop)).comp_aemeasurable
      (aemeasurable_brownianUnitPath hB 1)
  have hh : AEMeasurable (fun ω => slopeUpper (unitPath (processPath B ω) 1) 0) μ :=
    ((slopeUpper_joint_lipschitz.continuous.measurable).comp (f := fun g : Path 1 => (g,0)) (by fun_prop)).comp_aemeasurable
      (aemeasurable_brownianUnitPath hB 1)
  exact (nullMeasurableSet_lt aemeasurable_const hl).inter (nullMeasurableSet_lt hh aemeasurable_const)

/-- This is a joint minimum/maximum/terminal-position sublaw of the actual path,
with the interval restriction expressed directly through its true extrema. -/
theorem brownianExtremaBox_endpoint_eq_heatDensity (hB : IsBrownianReal B μ)
    {l h : ℝ} (hl : l < 0) (hh : 0 < h) :
    (μ.restrict {ω | brownianExtremaBox B l h ω}).map (B 1) =
      ((volume.restrict (Icc (0 : ℝ) (h-l))).withDensity
        (fun z => ENNReal.ofReal (dirichletHeatKernel (h-l) 1 (-l) z))).map (fun z => l+z) := by
  have hr : 0 < h-l := by linarith
  have hx : -l ∈ Ioo 0 (h-l) := by constructor <;> linarith
  have he : {ω | (1 : ℝ≥0∞) < intervalTouchTime B (-l) (h-l) ω} =ᵐ[μ]
      {ω | brownianExtremaBox B l h ω} := by
    filter_upwards [hB.cont] with ω hc
    exact propext (brownianExtremaBox_iff_touch_gt hc (by linarith)).symm
  have hk := killedBrownianMeasure_eq_heatDensity hB hr (Ioo_subset_Icc_self hx) (by norm_num : (0 : ℝ≥0) < 1)
  simp only [NNReal.coe_one] at hk
  rw [← hk,
    killedBrownianMeasure_eq_touch_survival hB hr hx (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [ENNReal.coe_one]
  rw [Measure.restrict_congr_set he]
  rw [AEMeasurable.map_map_of_aemeasurable (by fun_prop) ((hB.aemeasurable 1).const_add (-l)).restrict]
  apply Measure.map_congr
  filter_upwards [] with ω
  dsimp only [Function.comp_def]
  ring

end BrownianAffine
