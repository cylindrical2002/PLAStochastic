import PLAStochastic.Affine.Extrema.TimeLocalization
import PLAStochastic.Affine.Process.IntervalExit.JointLaw

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- With the lower boundary strictly below the path, every level below its maximum
is first reached at the upper endpoint before the observation horizon. -/
theorem intervalTouch_upper_level_before_one {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω=0) {x r : ℝ}
    (hp : ∀ t : ℝ≥0, t ≤ 1 → 0 < x+B t ω) (hxr : x < r)
    (hrM : r < x+slopeUpper (unitPath (processPath B ω) 1) 0) :
    intervalTouchClock B x r ω ≤ 1 ∧ intervalTouchEndpoint B x r ω=r := by
  let g := unitPath (processPath B ω) 1
  let v := upperTime g 0
  let t : ℝ≥0 := ⟨(v : ℝ),v.property.1⟩
  have ht1 : t ≤ 1 := by exact_mod_cast v.property.2
  have htv : nnrealRangeTime t ht1=v := Subtype.ext rfl
  have hv := upperTime_attains g 0
  change slopeResidual g 0 v=slopeUpper g 0 at hv
  rw [← htv,slopeResidual_actual_unit B hc 0 t ht1] at hv
  simp only [zero_mul,sub_zero] at hv
  have hout : x+B t ω ∉ Ioo 0 r := by
    intro hi
    change r < x+slopeUpper g 0 at hrM
    linarith [hi.2]
  have ht := intervalTouchTime_le_of_outside hout
  have hf : intervalTouchTime B x r ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have hτ : intervalTouchTime B x r ω=(intervalTouchClock B x r ω : ℝ≥0∞) := by
    obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hf
    rw [intervalTouchClock,← hs]
    rfl
  have hclock : intervalTouchClock B x r ω ≤ 1 := by
    rw [hτ] at ht
    exact (show intervalTouchClock B x r ω ≤ t by exact_mod_cast ht).trans ht1
  have hx : 0 < x := by simpa only [h0,add_zero] using hp 0 (by simp)
  have hb := intervalTouchTime_terminal hc h0 (hx.trans hxr) ⟨hx,hxr⟩ hτ
  refine ⟨hclock,?_⟩
  exact hb.resolve_left (ne_of_gt (hp _ hclock))

/-- First contacts of levels tending to the actual maximum localize at its unique
maximizer. This links the retained exit-time windows to the genuine extremum time. -/
theorem tendsto_intervalTouchClock_to_upperTime {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    (hu : DifferentiableAt ℝ (slopeUpper (unitPath (processPath B ω) 1)) 0)
    {x : ℝ} (hp : ∀ t : ℝ≥0, t ≤ 1 → 0 < x+B t ω)
    {R : ℕ → ℝ} (hR : ∀ n, x < R n ∧ R n < x+slopeUpper (unitPath (processPath B ω) 1) 0)
    (hlim : Tendsto R atTop (𝓝 (x+slopeUpper (unitPath (processPath B ω) 1) 0))) :
    Tendsto (fun n => (intervalTouchClock B x (R n) ω : ℝ)) atTop
      (𝓝 (upperTime (unitPath (processPath B ω) 1) 0 : ℝ)) := by
  have hh (n : ℕ) := intervalTouch_upper_level_before_one hc h0 hp (hR n).1 (hR n).2
  let u : ℕ → RangeTime := fun n => nnrealRangeTime (intervalTouchClock B x (R n) ω) (hh n).1
  have he (n : ℕ) : slopeResidual (unitPath (processPath B ω) 1) 0 (u n)=R n-x := by
    rw [slopeResidual_actual_unit B hc 0 _ (hh n).1]
    have hv := (hh n).2
    dsimp only [intervalTouchEndpoint] at hv
    simp only [zero_mul,sub_zero]
    linarith
  have hv : Tendsto (fun n => slopeResidual (unitPath (processPath B ω) 1) 0 (u n)) atTop
      (𝓝 (slopeUpper (unitPath (processPath B ω) 1) 0)) := by
    simp_rw [he]
    simpa only [add_sub_cancel_left] using hlim.sub_const x
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_upperTime_of_residual_values _ hu hv)

/-- The corresponding first contact from above reaches the lower level, because
the fixed upper boundary remains strictly above the entire observed path. -/
theorem intervalTouch_lower_level_before_one {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω=0) {l h : ℝ}
    (hp : ∀ t : ℝ≥0, t ≤ 1 → B t ω < h) (hl : l < 0)
    (hmL : slopeLower (unitPath (processPath B ω) 1) 0 < l) :
    intervalTouchClock B (-l) (h-l) ω ≤ 1 ∧
      B (intervalTouchClock B (-l) (h-l) ω) ω=l := by
  let g := unitPath (processPath B ω) 1
  let v := lowerTime g 0
  let t : ℝ≥0 := ⟨(v : ℝ),v.property.1⟩
  have ht1 : t ≤ 1 := by exact_mod_cast v.property.2
  have htv : nnrealRangeTime t ht1=v := Subtype.ext rfl
  have hv := lowerTime_attains g 0
  change slopeResidual g 0 v=slopeLower g 0 at hv
  rw [← htv,slopeResidual_actual_unit B hc 0 t ht1] at hv
  simp only [zero_mul,sub_zero] at hv
  have hout : -l+B t ω ∉ Ioo 0 (h-l) := by
    intro hi
    change slopeLower g 0 < l at hmL
    linarith [hi.1]
  have ht := intervalTouchTime_le_of_outside hout
  have hf : intervalTouchTime B (-l) (h-l) ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have hτ : intervalTouchTime B (-l) (h-l) ω=
      (intervalTouchClock B (-l) (h-l) ω : ℝ≥0∞) := by
    obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hf
    rw [intervalTouchClock,← hs]
    rfl
  have hclock : intervalTouchClock B (-l) (h-l) ω ≤ 1 := by
    rw [hτ] at ht
    exact (show intervalTouchClock B (-l) (h-l) ω ≤ t by exact_mod_cast ht).trans ht1
  have hh : 0 < h := by simpa only [h0] using hp 0 (by simp)
  have hb := intervalTouchTime_terminal hc h0 (by linarith : 0 < h-l)
    (show -l ∈ Ioo 0 (h-l) from ⟨by linarith,by linarith⟩) hτ
  refine ⟨hclock,?_⟩
  have he := hb.resolve_right (by have := hp _ hclock; linarith)
  linarith

theorem tendsto_intervalTouchClock_to_lowerTime {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    (hl : DifferentiableAt ℝ (slopeLower (unitPath (processPath B ω) 1)) 0)
    {h : ℝ} (hp : ∀ t : ℝ≥0, t ≤ 1 → B t ω < h)
    {L : ℕ → ℝ} (hL : ∀ n, L n < 0 ∧ slopeLower (unitPath (processPath B ω) 1) 0 < L n)
    (hlim : Tendsto L atTop (𝓝 (slopeLower (unitPath (processPath B ω) 1) 0))) :
    Tendsto (fun n => (intervalTouchClock B (-L n) (h-L n) ω : ℝ)) atTop
      (𝓝 (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) := by
  have hh (n : ℕ) := intervalTouch_lower_level_before_one hc h0 hp (hL n).1 (hL n).2
  let u : ℕ → RangeTime := fun n => nnrealRangeTime (intervalTouchClock B (-L n) (h-L n) ω) (hh n).1
  have he (n : ℕ) : slopeResidual (unitPath (processPath B ω) 1) 0 (u n)=L n := by
    rw [slopeResidual_actual_unit B hc 0 _ (hh n).1]
    simpa only [zero_mul,sub_zero] using (hh n).2
  have hv : Tendsto (fun n => slopeResidual (unitPath (processPath B ω) 1) 0 (u n)) atTop
      (𝓝 (slopeLower (unitPath (processPath B ω) 1) 0)) := by
    simpa only [he] using hlim
  exact continuous_subtype_val.continuousAt.tendsto.comp
    (tendsto_lowerTime_of_residual_values _ hl hv)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The preceding level-to-time localization holds for actual Brownian paths on one
full-measure set, simultaneously for every lower boundary and every approximating sequence. -/
theorem brownian_intervalTouchClock_upper_localization_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ x : ℝ, (∀ t : ℝ≥0, t ≤ 1 → 0 < x+B t ω) →
      ∀ R : ℕ → ℝ,
        (∀ n, x < R n ∧ R n < x+slopeUpper (unitPath (processPath B ω) 1) 0) →
        Tendsto R atTop (𝓝 (x+slopeUpper (unitPath (processPath B ω) 1) 0)) →
        Tendsto (fun n => (intervalTouchClock B x (R n) ω : ℝ)) atTop
          (𝓝 (upperTime (unitPath (processPath B ω) 1) 0 : ℝ)) := by
  filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,brownian_upper_lower_differentiable_ae hB 0]
    with ω hc h0 hu
  exact fun _ hp _ hR hlim => tendsto_intervalTouchClock_to_upperTime hc h0 hu.1 hp hR hlim

theorem brownian_intervalTouchClock_lower_localization_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, ∀ h : ℝ, (∀ t : ℝ≥0, t ≤ 1 → B t ω < h) →
      ∀ L : ℕ → ℝ,
        (∀ n, L n < 0 ∧ slopeLower (unitPath (processPath B ω) 1) 0 < L n) →
        Tendsto L atTop (𝓝 (slopeLower (unitPath (processPath B ω) 1) 0)) →
        Tendsto (fun n => (intervalTouchClock B (-L n) (h-L n) ω : ℝ)) atTop
          (𝓝 (lowerTime (unitPath (processPath B ω) 1) 0 : ℝ)) := by
  filter_upwards [hB.cont,hB.eval_zero_ae_eq_zero,brownian_upper_lower_differentiable_ae hB 0]
    with ω hc h0 hl
  exact fun _ hp _ hL hlim => tendsto_intervalTouchClock_to_lowerTime hc h0 hl.2 hp hL hlim

end BrownianAffine
