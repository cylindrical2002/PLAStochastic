import PLAStochastic.Affine.Moments.Optimal.Width.MomentCoordinates
import PLAStochastic.Affine.Process.Killed.WidthScaling

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem map_volume_prod_scale {α β : Type*} [MeasureSpace α] [MeasureSpace β]
    [SFinite (volume : Measure α)] [SFinite (volume : Measure β)]
    {f : α→α} {g : β→β} {a b : ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (ha : Measure.map f volume=a • volume) (hb : Measure.map g volume=b • volume) :
    Measure.map (Prod.map f g) volume=(a*b) • volume := by
  change Measure.map (Prod.map f g) (volume.prod volume)=_
  rw [←Measure.map_prod_map volume volume hf hg,ha,hb,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rfl

abbrev UnitWidthCoordinates := ℝ × ℝ × ℝ × ℝ

def unitWidthScale (r : ℝ) (p : UnitWidthCoordinates) : UnitWidthCoordinates :=
  (r*p.1,r^2*p.2.1,r^2*p.2.2.1,r*p.2.2.2)

theorem continuous_unitWidthScale (r : ℝ) : Continuous (unitWidthScale r) := by
  unfold unitWidthScale
  fun_prop

theorem unitWidthScale_injective {r : ℝ} (hr : r≠0) : Function.Injective (unitWidthScale r) := by
  intro p q h
  have h1 := congrArg (fun p : UnitWidthCoordinates => p.1) h
  have h2 := congrArg (fun p : UnitWidthCoordinates => p.2.1) h
  have h3 := congrArg (fun p : UnitWidthCoordinates => p.2.2.1) h
  have h4 := congrArg (fun p : UnitWidthCoordinates => p.2.2.2) h
  exact Prod.ext (mul_left_cancel₀ hr h1) (Prod.ext (mul_left_cancel₀ (pow_ne_zero _ hr) h2)
    (Prod.ext (mul_left_cancel₀ (pow_ne_zero _ hr) h3) (mul_left_cancel₀ hr h4)))

/-- The four spatial/time coordinates have combined Jacobian r^6. -/
theorem map_volume_unitWidthScale {r : ℝ} (hr : 0<r) :
    Measure.map (unitWidthScale r) volume=(ENNReal.ofReal (r^6))⁻¹ • volume := by
  have h1 := Real.map_volume_mul_left hr.ne'
  have h2 := Real.map_volume_mul_left (pow_ne_zero 2 hr.ne')
  have h12 := map_volume_prod_scale (by fun_prop) (by fun_prop) h2 h1
  have h212 := map_volume_prod_scale (by fun_prop) (by fun_prop) h2 h12
  have h := map_volume_prod_scale (by fun_prop) (by fun_prop) h1 h212
  change Measure.map (unitWidthScale r) volume=_ at h
  rw [h]
  congr 1
  simp only [abs_inv,abs_of_pos hr,abs_of_pos (pow_pos hr 2)]
  rw [←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_mul (by positivity),
    ←ENNReal.ofReal_mul (by positivity),←ENNReal.ofReal_inv_of_pos (pow_pos hr 6)]
  congr 1
  field_simp

theorem setLIntegral_unitWidthScale {r : ℝ} (hr : 0<r)
    (F : UnitWidthCoordinates→ℝ≥0∞) (S : Set UnitWidthCoordinates) :
    (∫⁻ p in unitWidthScale r ⁻¹' S, F (unitWidthScale r p))=
      (∫⁻ p in S, F p)/ENNReal.ofReal (r^6) := by
  have he := (continuous_unitWidthScale r).measurableEmbedding (unitWidthScale_injective hr.ne')
  have h : (∫⁻ p in S, F p ∂Measure.map (unitWidthScale r) volume)=
      ∫⁻ p in unitWidthScale r ⁻¹' S, F (unitWidthScale r p) := by
    rw [he.restrict_map,he.lintegral_map]
  rw [map_volume_unitWidthScale hr,Measure.restrict_smul,lintegral_smul_measure] at h
  simpa only [smul_eq_mul,ENNReal.div_eq_inv_mul] using h.symm

def fixedWidthMomentDomain (r : ℝ) : Set UnitWidthCoordinates :=
  {p | p.1∈Ioo 0 r ∧ p.2.2.2∈Ioo 0 r ∧ 0<p.2.1 ∧ 0<p.2.2.1 ∧ p.2.1+p.2.2.1<1}

def unitWidthMomentDomain (T : ℝ) : Set UnitWidthCoordinates :=
  {p | p.1∈Ioo 0 1 ∧ p.2.2.2∈Ioo 0 1 ∧ 0<p.2.1 ∧ 0<p.2.2.1 ∧ p.2.1+p.2.2.1<T}

theorem unitWidthScale_preimage_domain {r : ℝ} (hr : 0<r) :
    unitWidthScale r ⁻¹' fixedWidthMomentDomain r=unitWidthMomentDomain (1/r^2) := by
  ext p
  have hr2 : 0<r^2 := pow_pos hr 2
  simp only [mem_preimage,unitWidthScale,fixedWidthMomentDomain,unitWidthMomentDomain,
    mem_ofPred_eq,mem_Ioo]
  rw [mul_pos_iff_of_pos_left hr,mul_lt_iff_lt_one_right hr,
    mul_pos_iff_of_pos_left hr,mul_lt_iff_lt_one_right hr,
    mul_pos_iff_of_pos_left hr2,mul_pos_iff_of_pos_left hr2,←mul_add,
    ←lt_div_iff₀' hr2]

end BrownianAffine
