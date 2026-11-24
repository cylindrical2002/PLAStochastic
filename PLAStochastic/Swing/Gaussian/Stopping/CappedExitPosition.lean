import PLAStochastic.Swing.Gaussian.StripExit.Overshoot
import PLAStochastic.Swing.Gaussian.Stopping.StoppedQuadraticDrift

/-! # Pathwise bounds at the actual capped Gaussian exit time -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Once an actual finite exit has happened, the capped time equals that exit. -/
theorem capDiscreteTime_eq_of_le {τ : WithTop ℕ} {m : ℕ} (h : τ ≤ (m : WithTop ℕ)) :
    capDiscreteTime τ m = τ.untopD 0 := by
  cases τ using WithTop.recTopCoe with
  | top => exact False.elim ((not_le_of_gt (WithTop.coe_lt_top m)) h)
  | coe k =>
    have hk : k ≤ m := WithTop.coe_le_coe.mp h
    exact min_eq_right hk

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

/-- Every capped position lies between minus the selected overshoot and R plus it,
including paths for which the actual exit time is infinite. -/
theorem gaussianStrip_capped_position_bounds {x a R : ℝ} (m : ℕ) (ω : Ω) :
    -gaussianStripOvershoot X x a R ω ≤
      gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω ∧
    gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω ≤
      R + gaussianStripOvershoot X x a R ω := by
  have ho := gaussianStripOvershoot_nonneg X x a R ω
  by_cases hm : (m : WithTop ℕ) < gaussianStripExit X x a R ω
  · rw [capDiscreteTime_eq_of_lt hm]
    have hu := ((lt_gaussianStripExit_iff X x a R m ω).mp hm) m le_rfl
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  · rw [capDiscreteTime_eq_of_le (le_of_not_gt hm)]
    change -gaussianStripOvershoot X x a R ω ≤ gaussianStripExitPosition X x a R ω ∧
      gaussianStripExitPosition X x a R ω ≤ R + gaussianStripOvershoot X x a R ω
    have ht : gaussianStripExit X x a R ω ≠ ⊤ :=
      ne_top_of_le_ne_top WithTop.coe_ne_top (le_of_not_gt hm)
    rw [gaussianStripOvershoot, if_neg ht]
    have h₁ := (le_max_left (-gaussianStripExitPosition X x a R ω) (gaussianStripExitPosition X x a R ω-R)).trans (le_max_right 0 _)
    have h₂ := (le_max_right (-gaussianStripExitPosition X x a R ω) (gaussianStripExitPosition X x a R ω-R)).trans (le_max_right 0 _)
    constructor <;> linarith

/-- This lower bound holds before exit as well as after either exit direction. -/
theorem gaussianStrip_capped_potential_lower {x a R : ℝ} (m : ℕ) (ω : Ω) :
    -R * gaussianStripOvershoot X x a R ω - (gaussianStripOvershoot X x a R ω)^2 ≤
      stripPotential R (gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω) := by
  have hb := gaussianStrip_capped_position_bounds (X := X) (x := x) (a := a) (R := R) m ω
  have hp := mul_nonneg (sub_nonneg.mpr hb.1) (sub_nonneg.mpr hb.2)
  unfold stripPotential
  nlinarith

/-- A single integrable overshoot will dominate all stopped positions. -/
theorem gaussianStrip_capped_position_norm_le {x a R : ℝ} (hR : 0 ≤ R) (m : ℕ) (ω : Ω) :
    ‖gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω‖ ≤
      R + gaussianStripOvershoot X x a R ω := by
  have hb := gaussianStrip_capped_position_bounds (X := X) (x := x) (a := a) (R := R) m ω
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [hb.1], hb.2⟩

/-- A single exponential of the selected overshoot dominates every stopped exponential. -/
theorem gaussianStrip_capped_exp_le {x a R c : ℝ} (hc : 0 ≤ c)
    (m : ℕ) (ω : Ω) :
    Real.exp (-c * gaussianDriftWalk X x a (capDiscreteTime (gaussianStripExit X x a R ω) m) ω) ≤
      Real.exp (c * gaussianStripOvershoot X x a R ω) := by
  apply Real.exp_le_exp.mpr
  have hb := (gaussianStrip_capped_position_bounds (X := X) (x := x) (a := a) (R := R) m ω).1
  nlinarith [mul_le_mul_of_nonneg_left hb hc]

end SwingRepair
