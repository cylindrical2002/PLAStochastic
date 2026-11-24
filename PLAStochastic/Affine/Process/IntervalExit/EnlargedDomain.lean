import PLAStochastic.Affine.Process.IntervalExit.RestartPath

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Strict first-contact survival is precisely membership of the entire time prefix. -/
theorem intervalTouchTime_gt_iff {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) {x r : ℝ} (hr : 0 < r) (T : ℝ≥0) :
    (T : ℝ≥0∞) < intervalTouchTime B x r ω ↔
      ∀ t : ℝ≥0, t ≤ T → x+B t ω ∈ Ioo 0 r := by
  rw [← not_le,intervalTouchTime_le_iff hc hr]
  push Not
  rfl

/-- Enlarging the upper boundary adds only paths that first exit at the old upper
boundary and then survive for the actual remaining duration. -/
theorem intervalTouch_enlarged_survival_after_exit
    {Ω : Type*} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (h0 : B 0 ω = 0)
    {x r R : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) (hrR : r < R)
    {σ T : ℝ≥0} (hσ : intervalTouchTime B x r ω = σ) (hσT : σ ≤ T) :
    (T : ℝ≥0∞) < intervalTouchTime B x R ω ↔
      x+B σ ω=r ∧ ((T-σ : ℝ≥0) : ℝ≥0∞) <
        intervalTouchTime (brownianRestart B (fun _ => σ)) r R ω := by
  have hcR : Continuous (brownianRestart B (fun _ => σ) · ω) :=
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const
  rw [intervalTouchTime_gt_iff hc (hr.trans hrR),intervalTouchTime_gt_iff hcR (hr.trans hrR)]
  constructor
  · intro h
    have hb := intervalTouchTime_terminal hc h0 hr hx hσ
    have he : x+B σ ω=r := hb.resolve_left (ne_of_gt (h σ hσT).1)
    refine ⟨he,?_⟩
    intro u hu
    have hsu : σ+u ≤ T := by
      calc σ+u ≤ σ+(T-σ) := add_le_add le_rfl hu
           _ = T := add_tsub_cancel_of_le hσT
    have hv := h (σ+u) hsu
    have heq : r+brownianRestart B (fun _ => σ) u ω=x+B (σ+u) ω := by
      dsimp [brownianRestart]
      linarith
    rwa [heq]
  · rintro ⟨he,h⟩ t ht
    by_cases htσ : t < σ
    · have hin : x+B t ω ∈ Ioo 0 r := by
        by_contra hout
        have hn := intervalTouchTime_le_of_outside hout
        rw [hσ] at hn
        exact htσ.not_ge (by exact_mod_cast hn)
      exact ⟨hin.1,hin.2.trans hrR⟩
    · have hσt : σ ≤ t := le_of_not_gt htσ
      have hv := h (t-σ) (tsub_le_tsub_right ht σ)
      have heq : r+brownianRestart B (fun _ => σ) (t-σ) ω=x+B t ω := by
        dsimp [brownianRestart]
        rw [add_tsub_cancel_of_le hσt]
        linarith
      rwa [heq] at hv

end BrownianAffine
