import PLAStochastic.Affine.Process.IntervalExit.MarkovIntegral

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Restriction of a unit path to a prefix, reparametrized onto the unit interval. -/
def prefixPath (f : Path 1) (v : Icc (0 : ℝ) 1) : Path 1 :=
  ⟨fun u => f ⟨(v : ℝ)*(u : ℝ),mul_nonneg v.property.1 u.property.1,
      (mul_le_mul_of_nonneg_left u.property.2 v.property.1).trans (by simpa using v.property.2)⟩,
    f.continuous.comp ((continuous_const.mul continuous_subtype_val).subtype_mk _)⟩

theorem continuous_prefixPath :
    Continuous (fun p : Path 1 × Icc (0 : ℝ) 1 => prefixPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (Path 1 × Icc (0 : ℝ) 1) × Icc (0 : ℝ) 1 =>
    p.1.1 ⟨(p.1.2 : ℝ)*(p.2 : ℝ),mul_nonneg p.1.2.property.1 p.2.property.1,
      (mul_le_mul_of_nonneg_left p.2.property.2 p.1.2.property.1).trans
        (by simpa using p.1.2.property.2)⟩)
  exact continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
    ((((continuous_subtype_val.comp continuous_snd).comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _))

/-- A norm test of open-interval survival on a variable path prefix. -/
def prefixSurvival (f : Path 1) (v : Icc (0 : ℝ) 1) (y R : ℝ) : Prop :=
  ‖prefixPath f v + ContinuousMap.const _ (y-R/2)‖ < R/2

theorem prefixSurvival_iff (f : Path 1) (v : Icc (0 : ℝ) 1) (y : ℝ)
    {R : ℝ} (hR : 0 < R) :
    prefixSurvival f v y R ↔ ∀ u : Icc (0 : ℝ) 1,
      y+prefixPath f v u ∈ Ioo 0 R := by
  rw [prefixSurvival,ContinuousMap.norm_lt_iff _ (by positivity)]
  apply forall_congr'
  intro u
  simp only [ContinuousMap.add_apply,ContinuousMap.const_apply,Real.norm_eq_abs,abs_lt,mem_Ioo]
  constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith

/-- Clipped remaining fraction, defined measurably for all real exit times. -/
def remainingFraction (T s : ℝ) : Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 ((T-s)/T)),le_max_left _ _,
    max_le (by norm_num) (min_le_left _ _)⟩

theorem continuous_remainingFraction (T : ℝ) : Continuous (remainingFraction T) := by
  apply Continuous.subtype_mk
  exact continuous_const.max (continuous_const.min ((continuous_const.sub continuous_id).div_const T))

theorem remainingFraction_coe {T s : ℝ} (hT : 0 < T) (hs : s ∈ Icc 0 T) :
    (remainingFraction T s : ℝ) = (T-s)/T := by
  have ha : 0 ≤ (T-s)/T := div_nonneg (sub_nonneg.mpr hs.2) hT.le
  have hb : (T-s)/T ≤ 1 := (div_le_one hT).mpr (sub_le_self _ hs.1)
  simp only [remainingFraction,min_eq_right hb,max_eq_right ha]

/-- The remaining prefix of a path observed to T is exactly its prefix to T-s. -/
theorem prefixPath_unitPath (f : C(ℝ,ℝ)) {T s : ℝ≥0} (hT : 0 < T) (hs : s ≤ T) :
    prefixPath (unitPath f T) (remainingFraction T s) =
      unitPath f (T-s : ℝ≥0) := by
  apply DFunLike.ext
  intro u
  change f ((T : ℝ)*((remainingFraction T s : ℝ)*(u : ℝ))) =
    f (((T-s : ℝ≥0) : ℝ)*(u : ℝ))
  rw [NNReal.coe_sub hs,
    remainingFraction_coe (T := (T : ℝ)) (s := (s : ℝ)) (by exact_mod_cast hT) ⟨s.property,by exact_mod_cast hs⟩]
  congr 1
  field_simp

/-- The continuous norm test agrees with the actual first-contact event. -/
theorem unitPath_norm_survival_iff_touch {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (y : ℝ) {R : ℝ} (hR : 0 < R) (U : ℝ≥0) :
    ‖unitPath (processPath B ω) U + ContinuousMap.const _ (y-R/2)‖ < R/2 ↔
      (U : ℝ≥0∞) < intervalTouchTime B y R ω := by
  rw [intervalTouchTime_repr (processPath B ω) (processPath_apply_of_continuous hc),
    pathClosedHit_eq_firstReach _ (by positivity)]
  conv_rhs => rw [← not_le,firstReach_le_iff (monotone_prefixNorm _) (continuous_prefixNorm _),not_le]
  rfl

theorem prefixSurvival_unitPath_iff_touch {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (y : ℝ) {R : ℝ} (hR : 0 < R)
    {T s : ℝ≥0} (hT : 0 < T) (hs : s ≤ T) :
    prefixSurvival (unitPath (processPath B ω) T) (remainingFraction T s) y R ↔
      ((T-s : ℝ≥0) : ℝ≥0∞) < intervalTouchTime B y R ω := by
  rw [prefixSurvival,prefixPath_unitPath _ hT hs]
  exact unitPath_norm_survival_iff_touch hc y hR _

theorem unitPath_remainingFraction_apply (f : C(ℝ,ℝ))
    {T s : ℝ≥0} (hT : 0 < T) (hs : s ≤ T) :
    unitPath f T (remainingFraction T s) = f ((T-s : ℝ≥0) : ℝ) := by
  change f ((T : ℝ)*(remainingFraction T s : ℝ)) = f ((T-s : ℝ≥0) : ℝ)
  rw [NNReal.coe_sub hs,
    remainingFraction_coe (T := (T : ℝ)) (s := (s : ℝ)) (by exact_mod_cast hT)
      ⟨s.property,by exact_mod_cast hs⟩]
  congr 1
  field_simp

/-- A measurable test for exit at the upper endpoint followed by interval survival
and an endpoint observation at the original terminal time. -/
def upperContinuationSet (T r R : ℝ) (S : Set ℝ) : Set ((ℝ × ℝ) × Path 1) :=
  {p | p.1.1 ∈ Icc 0 T ∧ p.1.2=r ∧
    prefixSurvival p.2 (remainingFraction T p.1.1) r R ∧
    r+p.2 (remainingFraction T p.1.1) ∈ S}

theorem measurableSet_upperContinuationSet (T r R : ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) : MeasurableSet (upperContinuationSet T r R S) := by
  have hf : Continuous (fun p : (ℝ × ℝ) × Path 1 => remainingFraction T p.1.1) :=
    (continuous_remainingFraction T).comp (continuous_fst.comp continuous_fst)
  have hp := continuous_prefixPath.comp (continuous_snd.prodMk hf)
  have hn : Continuous (fun p : (ℝ × ℝ) × Path 1 =>
      ‖prefixPath p.2 (remainingFraction T p.1.1)+ContinuousMap.const _ (r-R/2)‖) :=
    (hp.add continuous_const).norm
  have he : Continuous (fun p : (ℝ × ℝ) × Path 1 =>
      r+p.2 (remainingFraction T p.1.1)) :=
    continuous_const.add (continuous_eval.comp (continuous_snd.prodMk hf))
  exact ((measurableSet_Icc.preimage (measurable_fst.comp measurable_fst)).inter
    ((isClosed_eq (continuous_snd.comp continuous_fst) continuous_const).measurableSet.inter
      ((isOpen_lt hn continuous_const).measurableSet.inter (hS.preimage he.measurable))))

end BrownianAffine
