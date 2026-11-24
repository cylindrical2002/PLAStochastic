import PLAStochastic.Affine.Extrema.Contact.Geometry

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A separated lower observation followed by an upper observation constructs the
actual ordered layer, provided the entire path stays in the enlarged interval. -/
theorem orderedContactLayer_of_separated_contacts {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω=0)
    {x r e d : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (he : 0 < e) (hd : 0 < d)
    {q v T : ℝ≥0} (hqv : q < v) (hvT : v ≤ T)
    (hqlow : x+B q ω < 0) (hprefix : ∀ t : ℝ≥0, t ≤ q → x+B t ω < r)
    (hvhigh : r < x+B v ω)
    (hfull : ∀ t : ℝ≥0, t ≤ T → x+B t ω ∈ Ioo (-e) (r+d))
    {S : Set ℝ} (hend : x+B T ω ∈ S) :
    orderedContactLayerEvent B x r e d T S univ univ ω := by
  let s := intervalTouchClock B x r ω
  let W := brownianRestartAt B (intervalTouchTime B x r)
  have hout : x+B q ω ∉ Ioo 0 r := fun hi => hi.1.not_ge hqlow.le
  have htq := intervalTouchTime_le_of_outside hout
  have hf : intervalTouchTime B x r ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top htq
  have hst : intervalTouchTime B x r ω=(s : ℝ≥0∞) := by
    obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp hf
    dsimp only [s]
    rw [intervalTouchClock,← ha]
    rfl
  have hsq : s ≤ q := by rw [hst] at htq; exact_mod_cast htq
  have hsT : s < T := (hsq.trans_lt hqv).trans_le hvT
  have hterm := intervalTouchTime_terminal hc h0 hr hx hst
  have hz : x+B s ω=0 := hterm.resolve_right (ne_of_lt (hprefix s hsq))
  have hs0 : 0 < s := by
    apply pos_iff_ne_zero.mpr
    intro hs
    rw [hs,h0,add_zero] at hz
    exact hx.1.ne' hz
  have hcW : Continuous (W · ω) :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  have hrec (u : ℝ≥0) : x+B (s+u) ω=W u ω := by
    change x+B (s+u) ω=B (s+u) ω-B s ω
    linarith
  have hsurv : ((T-s : ℝ≥0) : ℝ≥0∞) < intervalTouchTime W e (r+e+d) ω := by
    apply (intervalTouchTime_gt_iff hcW (by linarith : 0 < r+e+d) (T-s)).mpr
    intro u hu
    have hsu : s+u ≤ T := by
      calc s+u ≤ s+(T-s) := add_le_add le_rfl hu
           _ = T := add_tsub_cancel_of_le hsT.le
    have hh := hfull (s+u) hsu
    rw [hrec] at hh
    constructor <;> linarith [hh.1,hh.2]
  have hsecond : intervalTouchTime W e (r+e) ω ≤ (T-s : ℝ≥0) := by
    have heq := hrec (v-s)
    rw [add_tsub_cancel_of_le (hsq.trans hqv.le)] at heq
    have hout : e+W (v-s) ω ∉ Ioo 0 (r+e) := by
      intro hi
      linarith [hi.2]
    exact (intervalTouchTime_le_of_outside hout).trans
      (by exact_mod_cast tsub_le_tsub_right hvT s)
  have hend' : e+W (T-s) ω ∈ (fun z => z-e) ⁻¹' S := by
    change e+W (T-s) ω-e ∈ S
    rw [add_sub_cancel_left,← hrec,add_tsub_cancel_of_le hsT.le]
    exact hend
  exact ⟨⟨mem_univ _,by exact_mod_cast hs0,by exact_mod_cast hsT⟩,
    hz,⟨hsurv,hsecond,hend'⟩,mem_univ _⟩

end BrownianAffine
