import PLAStochastic.Affine.Extrema.Contact.LayerEvent
import PLAStochastic.Affine.Extrema.TouchLocalization

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem touch_eq_coe_clock_of_finite {Ω : Type*} {B : ℝ≥0 → Ω → ℝ}
    {x r : ℝ} {ω : Ω} (hf : intervalTouchTime B x r ω ≠ ⊤) :
    intervalTouchTime B x r ω=(intervalTouchClock B x r ω : ℝ≥0∞) := by
  obtain ⟨u,hu⟩ := WithTop.ne_top_iff_exists.mp hf
  rw [intervalTouchClock,← hu]
  rfl

/-- The probabilistic two-contact event is a true boundary layer of the entire
original path, with ordered contacts and the original terminal-position test. -/
theorem orderedContactLayer_geometry {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {x r e d : ℝ} (hr : 0 < r) (he : 0 < e) (hd : 0 < d)
    {T : ℝ≥0} {S D₁ D₂ : Set ℝ} (hE : orderedContactLayerEvent B x r e d T S D₁ D₂ ω) :
    (∀ t : ℝ≥0, t ≤ T → x+B t ω ∈ Ioo (-e) (r+d)) ∧
      (∃ s v : ℝ≥0, 0 < s ∧ s < v ∧ v ≤ T ∧ x+B s ω=0 ∧ x+B v ω=r ∧
        (s : ℝ) ∈ D₁ ∧ ((v-s : ℝ≥0) : ℝ) ∈ D₂) ∧ x+B T ω ∈ S := by
  let s := intervalTouchClock B x r ω
  let W := brownianRestartAt B (intervalTouchTime B x r)
  change (s : ℝ) ∈ D₁ ∩ Ioo (0 : ℝ) (T : ℝ) ∧ intervalTouchEndpoint B x r ω=0 ∧
    ((((T-s : ℝ≥0) : ℝ≥0∞) < intervalTouchTime W e (r+e+d) ω ∧
      intervalTouchTime W e (r+e) ω ≤ (T-s : ℝ≥0) ∧
      e+W (T-s) ω ∈ (fun z => z-e) ⁻¹' S) ∧
      (intervalTouchClock W e (r+e) ω : ℝ) ∈ D₂) at hE
  have hs0 : 0 < s := by exact_mod_cast hE.1.2.1
  have hsT : s < T := by exact_mod_cast hE.1.2.2
  have hsf : intervalTouchTime B x r ω ≠ ⊤ := by
    intro hf
    have hz : s=0 := by dsimp [s,intervalTouchClock]; rw [hf]; rfl
    exact hs0.ne' hz
  have hst : intervalTouchTime B x r ω=(s : ℝ≥0∞) := touch_eq_coe_clock_of_finite hsf
  have hz : x+B s ω=0 := hE.2.1
  have hcW : Continuous (W · ω) :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hW0 : W 0 ω=0 := by simp [W,brownianRestartAt,brownianRestart]
  have hrec (u : ℝ≥0) : x+B (s+u) ω=W u ω := by
    change x+B (s+u) ω=B (s+u) ω-B s ω
    linarith
  have hsurv := (intervalTouchTime_gt_iff hcW (by linarith : 0 < r+e+d) (T-s)).mp hE.2.2.1.1
  let u := intervalTouchClock W e (r+e) ω
  have huf : intervalTouchTime W e (r+e) ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hE.2.2.1.2.1
  have hut : intervalTouchTime W e (r+e) ω=(u : ℝ≥0∞) := touch_eq_coe_clock_of_finite huf
  have huT : u ≤ T-s := by
    have h := hE.2.2.1.2.1
    rw [hut] at h
    exact_mod_cast h
  have hterm := intervalTouchTime_terminal hcW hW0 (by linarith : 0 < r+e)
    (show e ∈ Ioo 0 (r+e) from ⟨he,by linarith⟩) hut
  have hupper : e+W u ω=r+e := hterm.resolve_left (ne_of_gt (hsurv u huT).1)
  have hWu : W u ω=r := by linarith
  have hu0 : 0 < u := by
    apply pos_iff_ne_zero.mpr
    intro hu
    rw [hu,hW0] at hWu
    exact hr.ne hWu
  have hsvT : s+u ≤ T := by
    calc s+u ≤ s+(T-s) := add_le_add le_rfl huT
         _ = T := add_tsub_cancel_of_le hsT.le
  refine ⟨?_,⟨s,s+u,hs0,lt_add_of_pos_right s hu0,hsvT,hz,?_,hE.1.1,?_⟩,?_⟩
  · intro t ht
    by_cases hts : t < s
    · have hi : x+B t ω ∈ Ioo 0 r := by
        by_contra hout
        have h := intervalTouchTime_le_of_outside hout
        rw [hst] at h
        exact hts.not_ge (by exact_mod_cast h)
      constructor <;> linarith [hi.1,hi.2]
    · have hst : s ≤ t := le_of_not_gt hts
      have hh := hsurv (t-s) (tsub_le_tsub_right ht s)
      have heq := hrec (t-s)
      rw [add_tsub_cancel_of_le hst] at heq
      constructor <;> linarith [hh.1,hh.2]
  · rw [hrec,hWu]
  · simpa only [add_tsub_cancel_left] using hE.2.2.2
  · have hh := hE.2.2.1.2.2
    change e+W (T-s) ω-e ∈ S at hh
    rw [add_sub_cancel_left] at hh
    have heq := hrec (T-s)
    rw [add_tsub_cancel_of_le hsT.le] at heq
    rwa [heq]

/-- Every actual two-contact layer lies in the claimed small minimum-maximum rectangle. -/
theorem orderedContactLayer_extrema_rectangle {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {x r e d : ℝ} (hr : 0 < r) (he : 0 < e) (hd : 0 < d)
    {S D₁ D₂ : Set ℝ} (hE : orderedContactLayerEvent B x r e d 1 S D₁ D₂ ω) :
    -e < x+slopeLower (unitPath (processPath B ω) 1) 0 ∧
      x+slopeLower (unitPath (processPath B ω) 1) 0 ≤ 0 ∧
      r ≤ x+slopeUpper (unitPath (processPath B ω) 1) 0 ∧
      x+slopeUpper (unitPath (processPath B ω) 1) 0 < r+d := by
  let g := unitPath (processPath B ω) 1
  have hg := orderedContactLayer_geometry hc hr he hd hE
  have hval (u : RangeTime) : g u=B (⟨(u : ℝ),u.property.1⟩ : ℝ≥0) ω := by
    simpa only [NNReal.coe_one,one_mul] using unitPath_processPath_apply hc 1 u
  have hl := lowerTime_attains g 0
  have hu := upperTime_attains g 0
  simp only [slopeResidual,zero_mul,sub_zero,hval] at hl hu
  have hlow := hg.1 (⟨(lowerTime g 0 : ℝ),(lowerTime g 0).property.1⟩ : ℝ≥0)
    (by exact_mod_cast (lowerTime g 0).property.2)
  have hupp := hg.1 (⟨(upperTime g 0 : ℝ),(upperTime g 0).property.1⟩ : ℝ≥0)
    (by exact_mod_cast (upperTime g 0).property.2)
  rw [hl] at hlow
  rw [hu] at hupp
  obtain ⟨s,v,_,hsv,hv,hs0,hvr,_,_⟩ := hg.2.1
  have hmin := slopeLower_le_residual g 0 (nnrealRangeTime s (hsv.le.trans hv))
  have hmax := slopeResidual_le_upper g 0 (nnrealRangeTime v hv)
  rw [slopeResidual_actual_unit B hc 0 s (hsv.le.trans hv)] at hmin
  rw [slopeResidual_actual_unit B hc 0 v hv] at hmax
  simp only [zero_mul,sub_zero] at hmin hmax
  exact ⟨hlow.1,by linarith,by linarith,hupp.2⟩

end BrownianAffine
