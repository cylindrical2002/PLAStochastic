import PLAStochastic.Affine.Pinch.StoppingTime
import PLAStochastic.Brownian.Killed.StoppedSineMoments

/-! First endpoint contact of a continuous path, with infinity retained. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The maximum absolute displacement on a prefix, represented on a fixed unit interval. -/
def prefixNorm (f : C(ℝ, ℝ)) (T : ℝ≥0) : ℝ := ‖unitPath f T‖

private theorem unitInterval_scaling_surjective (T : ℝ≥0) {t : ℝ≥0} (ht : t ≤ T) :
    ∃ u : Icc (0 : ℝ) 1, (T : ℝ) * (u : ℝ) = (t : ℝ) := by
  by_cases hT : T = 0
  · have ht0 : t = 0 := le_antisymm (ht.trans_eq hT) bot_le
    exact ⟨⟨0, by norm_num⟩, by simp [hT, ht0]⟩
  · have hTp : 0 < (T : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr hT
    refine ⟨⟨(t : ℝ) / T, div_nonneg t.property T.property,
      (div_le_one hTp).mpr (by exact_mod_cast ht)⟩, ?_⟩
    field_simp

theorem prefixNorm_le_iff (f : C(ℝ, ℝ)) (T : ℝ≥0) {ε : ℝ} (hε : 0 ≤ ε) :
    prefixNorm f T ≤ ε ↔ ∀ t : ℝ≥0, t ≤ T → |f t| ≤ ε := by
  rw [prefixNorm, ContinuousMap.norm_le _ hε]
  constructor
  · intro h t ht
    obtain ⟨u, hu⟩ := unitInterval_scaling_surjective T ht
    simpa only [unitPath, ContinuousMap.coe_mk, hu, Real.norm_eq_abs] using h u
  · intro h u
    have ht : T * ⟨u.1, u.property.1⟩ ≤ T := mul_le_of_le_one_right T.property u.property.2
    simpa only [unitPath, ContinuousMap.coe_mk, NNReal.coe_mul, NNReal.coe_mk, Real.norm_eq_abs] using!
      h (T * ⟨u.1, u.property.1⟩) ht

theorem prefixNorm_lt_iff (f : C(ℝ, ℝ)) (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    prefixNorm f T < ε ↔ ∀ t : ℝ≥0, t ≤ T → |f t| < ε := by
  rw [prefixNorm, ContinuousMap.norm_lt_iff _ hε]
  constructor
  · intro h t ht
    obtain ⟨u, hu⟩ := unitInterval_scaling_surjective T ht
    simpa only [unitPath, ContinuousMap.coe_mk, hu, Real.norm_eq_abs] using h u
  · intro h u
    have ht : T * ⟨u.1, u.property.1⟩ ≤ T := mul_le_of_le_one_right T.property u.property.2
    simpa only [unitPath, ContinuousMap.coe_mk, NNReal.coe_mul, NNReal.coe_mk, Real.norm_eq_abs] using!
      h (T * ⟨u.1, u.property.1⟩) ht

theorem continuous_prefixNorm (f : C(ℝ, ℝ)) : Continuous (prefixNorm f) :=
  ((continuous_unitPath f).comp continuous_subtype_val).norm

theorem monotone_prefixNorm (f : C(ℝ, ℝ)) : Monotone (prefixNorm f) := by
  intro S T hST
  apply (prefixNorm_le_iff f S (norm_nonneg _)).mpr
  intro t ht
  exact (prefixNorm_le_iff f T (norm_nonneg _)).mp le_rfl t (ht.trans hST)

/-- First contact with the complement of an open symmetric band. -/
def pathClosedHit (f : C(ℝ, ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if ε ≤ |f t| then (t : ℝ≥0∞) else ⊤

theorem pathClosedHit_le_of_hit {f : C(ℝ, ℝ)} {ε : ℝ} {t : ℝ≥0} (ht : ε ≤ |f t|) :
    pathClosedHit f ε ≤ (t : ℝ≥0∞) := (iInf_le _ t).trans_eq (if_pos ht)

theorem pathClosedHit_eq_firstReach (f : C(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    pathClosedHit f ε = firstReach (prefixNorm f) ε := by
  apply le_antisymm
  · apply le_iInf
    intro T
    split_ifs with hT
    · have ht : ∃ t : ℝ≥0, t ≤ T ∧ ε ≤ |f t| := by
        by_contra hn
        push Not at hn
        exact hT.not_gt ((prefixNorm_lt_iff f T hε).mpr hn)
      obtain ⟨t, ht, he⟩ := ht
      exact (pathClosedHit_le_of_hit he).trans (by exact_mod_cast ht)
    · exact le_top
  · apply le_iInf
    intro t
    split_ifs with ht
    · apply firstReach_le_of_reaches
      exact ht.trans ((prefixNorm_le_iff f t (norm_nonneg _)).mp le_rfl t le_rfl)
    · exact le_top

theorem pathClosedHit_le_iff (f : C(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) :
    pathClosedHit f ε ≤ (T : ℝ≥0∞) ↔ ∃ t : ℝ≥0, t ≤ T ∧ ε ≤ |f t| := by
  rw [pathClosedHit_eq_firstReach f hε,
    firstReach_le_iff (monotone_prefixNorm f) (continuous_prefixNorm f)]
  rw [← not_lt, prefixNorm_lt_iff f T hε]
  push Not
  rfl

theorem pathClosedHit_terminal {f : C(ℝ, ℝ)} {ε : ℝ} (hε : 0 < ε)
    (hz : |f 0| < ε) {σ : ℝ≥0} (hσ : pathClosedHit f ε = σ) : |f σ| = ε := by
  obtain ⟨t, ht, he⟩ := (pathClosedHit_le_iff f hε σ).mp hσ.le
  have htσ : t = σ := by
    apply le_antisymm ht
    exact_mod_cast (hσ ▸ pathClosedHit_le_of_hit he)
  subst t
  have herr := error_at_firstReach (monotone_prefixNorm f) (continuous_prefixNorm f)
    (show prefixNorm f 0 < ε by
      apply (prefixNorm_lt_iff f 0 hε).mpr
      intro t ht
      simpa only [show t = 0 from le_antisymm ht bot_le, NNReal.coe_zero] using hz)
    ((pathClosedHit_eq_firstReach f hε).symm.trans hσ)
  exact le_antisymm (herr ▸ (prefixNorm_le_iff f σ (norm_nonneg _)).mp le_rfl σ le_rfl) he

/-- The actual first contact with either endpoint, with infinity retained. -/
def intervalTouchTime {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (x r : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if x + B t ω ∉ Ioo 0 r then (t : ℝ≥0∞) else ⊤

def centeredIntervalPath (f : C(ℝ, ℝ)) (x r : ℝ) : C(ℝ, ℝ) :=
  f + ContinuousMap.const ℝ (x - r / 2)

private theorem mem_interval_iff_centered_abs_lt (y r : ℝ) :
    y ∈ Ioo 0 r ↔ |y - r / 2| < r / 2 := by
  rw [abs_lt, mem_Ioo]
  constructor <;> rintro ⟨ha, hb⟩ <;> constructor <;> linarith

theorem intervalTouchTime_repr {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (f : C(ℝ, ℝ)) (hf : ∀ t : ℝ≥0, f t = B t ω) (x r : ℝ) :
    intervalTouchTime B x r ω = pathClosedHit (centeredIntervalPath f x r) (r / 2) := by
  apply iInf_congr
  intro t
  have he : (x + B t ω ∉ Ioo 0 r) ↔ r / 2 ≤ |centeredIntervalPath f x r t| := by
    rw [mem_interval_iff_centered_abs_lt, not_lt]
    simp only [centeredIntervalPath, ContinuousMap.add_apply, ContinuousMap.const_apply, hf, ← add_sub_assoc, add_comm (B t ω) x]
  simp only [he]

theorem intervalTouchTime_le_of_outside {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    {x r : ℝ} {t : ℝ≥0} (ht : x + B t ω ∉ Ioo 0 r) :
    intervalTouchTime B x r ω ≤ (t : ℝ≥0∞) := (iInf_le _ t).trans_eq (if_pos ht)

theorem intervalTouchTime_le_iff {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {x r : ℝ} (hr : 0 < r) (T : ℝ≥0) :
    intervalTouchTime B x r ω ≤ (T : ℝ≥0∞) ↔ ∃ t : ℝ≥0, t ≤ T ∧ x + B t ω ∉ Ioo 0 r := by
  rw [intervalTouchTime_repr (processPath B ω) (processPath_apply_of_continuous hc),
    pathClosedHit_le_iff _ (by positivity)]
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  rw [mem_interval_iff_centered_abs_lt, not_lt]
  simp only [centeredIntervalPath, ContinuousMap.add_apply, ContinuousMap.const_apply,
    processPath_apply_of_continuous hc, ← add_sub_assoc, add_comm (B t ω) x]

theorem intervalTouchTime_terminal {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (hz : B 0 ω = 0) {x r : ℝ}
    (hr : 0 < r) (hx : x ∈ Ioo 0 r) {σ : ℝ≥0}
    (hσ : intervalTouchTime B x r ω = σ) : x + B σ ω = 0 ∨ x + B σ ω = r := by
  have heq := intervalTouchTime_repr (processPath B ω) (processPath_apply_of_continuous hc) x r
  have hzero : |centeredIntervalPath (processPath B ω) x r 0| < r / 2 := by
    have hp : processPath B ω 0 = 0 := by
      simpa only [NNReal.coe_zero, hz] using processPath_apply_of_continuous hc 0
    simpa only [centeredIntervalPath, ContinuousMap.add_apply, ContinuousMap.const_apply,
      hp, zero_add] using (mem_interval_iff_centered_abs_lt x r).mp hx
  have hbd := pathClosedHit_terminal (by positivity : 0 < r / 2) hzero (heq.symm.trans hσ)
  simp only [centeredIntervalPath, ContinuousMap.add_apply, ContinuousMap.const_apply,
    processPath_apply_of_continuous hc] at hbd
  rcases (abs_eq (by positivity : 0 ≤ r / 2)).mp hbd with h | h
  · right; linarith
  · left; linarith

theorem boundedIntervalExit_eq_min_touch_of_crossing {Ω : Type*}
    {B : ℝ≥0 → Ω → ℝ} {ω : Ω} {x r : ℝ} {σ : ℝ≥0}
    (hσ : intervalTouchTime B x r ω = σ)
    (hcross : ∀ δ : ℝ≥0, 0 < δ → ∃ u : ℝ≥0, 0 < u ∧ u < δ ∧
      (x + B (σ + u) ω < 0 ∨ r < x + B (σ + u) ω)) (T : ℝ≥0) :
    boundedIntervalExit B x r T ω = min σ T := by
  apply le_antisymm
  · apply le_min _ (boundedOpenExitTime_le _ _ _ _)
    by_contra h
    have hlt : σ < boundedIntervalExit B x r T ω := lt_of_not_ge h
    obtain ⟨u, _, hu, hout⟩ := hcross (boundedIntervalExit B x r T ω - σ)
      (tsub_pos_iff_lt.mpr hlt)
    have hearly : σ + u < boundedIntervalExit B x r T ω := by
      calc
        σ + u < σ + (boundedIntervalExit B x r T ω - σ) := by gcongr
        _ = boundedIntervalExit B x r T ω := add_tsub_cancel_of_le hlt.le
    have hn := before_boundedOpenExitTime_notMem (X := fun t ω => x + B t ω)
      (S := driftBarrierSet r 0) hearly
    apply hn
    simpa only [driftBarrierSet, mem_union, mem_Iio, mem_Ioi, neg_zero] using hout
  · apply le_csInf (insert_nonempty _ _)
    intro s hs
    rcases mem_insert_iff.mp hs with rfl | hs
    · exact min_le_right _ _
    · have hout : x + B s ω ∉ Ioo 0 r := by
        intro hin
        rcases hs.2 with hlo | hhi
        · exact hin.1.not_gt (by simpa only [mem_Iio, neg_zero] using hlo)
        · exact hin.2.not_gt hhi
      have hle := intervalTouchTime_le_of_outside hout
      rw [hσ] at hle
      exact (min_le_left _ _).trans (ENNReal.coe_le_coe.mp hle)

end BrownianAffine
