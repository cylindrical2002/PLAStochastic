import PLAStochastic.Swing.Gaussian.HalfLine.SmallDriftOvershootMean
import Mathlib.Analysis.Calculus.DSlope

/-! The exponential divided difference with its continuous value at zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The continuous extension of (exp(cu)-1)/c, including c=0. -/
def gaussianExpSlope (c u : ℝ) : ℝ := u * dslope Real.exp 0 (c*u)

@[simp] theorem gaussianExpSlope_zero (u : ℝ) : gaussianExpSlope 0 u = u := by
  simp [gaussianExpSlope, Real.deriv_exp]

@[simp] theorem gaussianExpSlope_zero_arg (c : ℝ) : gaussianExpSlope c 0 = 0 := by
  simp [gaussianExpSlope]

theorem gaussianExpSlope_mul (c u : ℝ) : c * gaussianExpSlope c u = Real.exp (c*u)-1 := by
  have h := sub_smul_dslope Real.exp 0 (c*u)
  simp only [sub_zero, smul_eq_mul, Real.exp_zero] at h
  dsimp [gaussianExpSlope]
  nlinarith only [h]

theorem gaussianExpSlope_eq_div {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    gaussianExpSlope c u = (Real.exp (c*u)-1)/c := by
  apply (eq_div_iff hc).mpr
  rw [mul_comm, gaussianExpSlope_mul]

theorem continuous_gaussianExpSlope : Continuous (fun p : ℝ × ℝ => gaussianExpSlope p.1 p.2) := by
  have hc : Continuous (dslope Real.exp 0) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      exact continuousAt_dslope_same.mpr (Real.differentiable_exp 0)
    · exact (continuousAt_dslope_of_ne hz).mpr Real.continuous_exp.continuousAt
  exact continuous_snd.mul (hc.comp (continuous_fst.mul continuous_snd))

theorem gaussianExpSlope_nonneg {c u : ℝ} (hc : 0 ≤ c) (hu : 0 ≤ u) :
    0 ≤ gaussianExpSlope c u := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simpa using hu
  · rw [gaussianExpSlope_eq_div hc.ne']
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp (mul_nonneg hc.le hu))) hc.le

theorem gaussianExpSlope_le_mul_exp {c u : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1) (hu : 0 ≤ u) :
    gaussianExpSlope c u ≤ u * Real.exp u := by
  rcases eq_or_lt_of_le hc with rfl | hc
  · simpa using le_mul_of_one_le_right hu (Real.one_le_exp hu)
  · rw [gaussianExpSlope_eq_div hc.ne']
    apply (div_le_iff₀ hc).mpr
    have he := exp_le_one_add_mul_exp (c*u)
    have heu : Real.exp (c*u) ≤ Real.exp u := Real.exp_le_exp.mpr (by nlinarith)
    have hm := mul_le_mul_of_nonneg_left heu (mul_nonneg hc.le hu)
    nlinarith

theorem gaussianExpSlope_sq_le_exp {c u : ℝ} (hc : 0 ≤ c) (hc' : c ≤ 1) (hu : 0 ≤ u) :
    (gaussianExpSlope c u)^2 ≤ Real.exp (4*u) := by
  have h0 := gaussianExpSlope_nonneg hc hu
  have h1 := gaussianExpSlope_le_mul_exp hc hc' hu
  have h2 : u * Real.exp u ≤ Real.exp (2*u) := by
    have he : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    calc
      _ ≤ Real.exp u * Real.exp u := mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ (Real.exp (2*u))^2 := pow_le_pow_left₀ h0 (h1.trans h2) 2
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end SwingRepair
