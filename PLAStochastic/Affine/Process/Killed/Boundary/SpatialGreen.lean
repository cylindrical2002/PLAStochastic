import PLAStochastic.Affine.Process.Killed.Boundary.LeftGreen
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def rightBoundaryGreen (r k x : ℝ) : ℝ := 2*Real.sinh (k*x)/Real.sinh (k*r)
def crossBoundaryGreen (r k : ℝ) : ℝ := 2*k/Real.sinh (k*r)
def boundaryPairTransform (r k : ℝ) : ℝ :=
  ∫ y in Icc (0 : ℝ) r, rightBoundaryGreen r k y*leftBoundaryGreen r k y

theorem continuous_rightBoundaryGreen (r k : ℝ) : Continuous (rightBoundaryGreen r k) := by
  change Continuous (fun x => 2*Real.sinh (k*x)/Real.sinh (k*r))
  fun_prop

private theorem sinh_pair_identity (r k y : ℝ) :
    Real.cosh (k*r)-Real.cosh (k*(2*y-r)) = 2*Real.sinh (k*y)*Real.sinh (k*(r-y)) := by
  rw [show k*r=k*y+k*(r-y) by ring, show k*(2*y-r)=k*y-k*(r-y) by ring,
    Real.cosh_add, Real.cosh_sub]
  ring

private theorem deriv_sinh_pair_primitive {k : ℝ} (hk : 0 < k) (r y : ℝ) :
    HasDerivAt (fun y => y*Real.cosh (k*r)/2-Real.sinh (k*(2*y-r))/(4*k))
      (Real.sinh (k*y)*Real.sinh (k*(r-y))) y := by
  have hd := (((hasDerivAt_id y).const_mul 2).sub_const r).const_mul k
  convert! (((hasDerivAt_id y).mul_const (Real.cosh (k*r))).div_const 2).sub (hd.sinh.div_const (4*k)) using 1
  simp only [id_eq]
  field_simp
  simp only [mul_comm y 2]
  linear_combination -4 * (sinh_pair_identity r k y)

theorem integral_sinh_pair {k : ℝ} (hk : 0 < k) (r : ℝ) :
    (∫ y in (0 : ℝ)..r, Real.sinh (k*y)*Real.sinh (k*(r-y))) =
      r*Real.cosh (k*r)/2-Real.sinh (k*r)/(2*k) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => deriv_sinh_pair_primitive hk r y) (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [show 2*r-r=r by ring]
  simp only [mul_zero, zero_mul, zero_sub, mul_neg, Real.sinh_neg, neg_div]
  ring

theorem boundaryPairTransform_eq {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    boundaryPairTransform r k =
      2*r*Real.cosh (k*r)/Real.sinh (k*r)^2-2/(k*Real.sinh (k*r)) := by
  unfold boundaryPairTransform
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.le]
  have heq (y : ℝ) : rightBoundaryGreen r k y*leftBoundaryGreen r k y =
      (4/Real.sinh (k*r)^2)*(Real.sinh (k*y)*Real.sinh (k*(r-y))) := by
    unfold rightBoundaryGreen leftBoundaryGreen
    ring
  simp only [heq]
  rw [intervalIntegral.integral_const_mul, integral_sinh_pair hk]
  have hs : Real.sinh (k*r) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne'
  field_simp
  ring

theorem hasDerivAt_crossBoundaryGreen {r k : ℝ} (hr : 0 < r) (hk : 0 < k) :
    HasDerivAt (crossBoundaryGreen r) (-k*boundaryPairTransform r k) k := by
  have hs : Real.sinh (k*r) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne'
  have hd := ((hasDerivAt_id k).const_mul 2).div (((hasDerivAt_id k).mul_const r).sinh) hs
  convert! hd using 1
  rw [boundaryPairTransform_eq hr hk]
  simp only [id_eq]
  field_simp
  ring

theorem tendsto_crossBoundaryGreen_atTop {r : ℝ} (hr : 0 < r) :
    Tendsto (crossBoundaryGreen r) atTop (𝓝 0) := by
  have hexp : Tendsto (fun k : ℝ => k*Real.exp (-(r*k))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp (tendsto_id.const_mul_atTop hr)
    have h' := h.div_const r
    convert! h' using 1
    · funext k
      dsimp only [Function.comp_def, id_eq, pow_one]
      field_simp
    · simp
  have hbound : ∀ᶠ k : ℝ in atTop, crossBoundaryGreen r k ∈ Icc 0 (8*(k*Real.exp (-(r*k)))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), (tendsto_id.const_mul_atTop hr).eventually_ge_atTop 1] with k hk hkr
    dsimp only [id_eq] at hkr
    have he : Real.exp (r*k)/4 ≤ Real.sinh (r*k) := by
      have h1 := Real.add_one_le_exp (r*k)
      have h2 : Real.exp (-(r*k)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      rw [Real.sinh_eq]
      linarith
    constructor
    · unfold crossBoundaryGreen
      have hs := Real.sinh_pos_iff.mpr (mul_pos hk hr)
      positivity
    · unfold crossBoundaryGreen
      rw [mul_comm k r]
      calc
        _ ≤ (2*k)/(Real.exp (r*k)/4) := div_le_div_of_nonneg_left (by positivity) (by positivity) he
        _ = _ := by rw [Real.exp_neg]; field_simp; ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hexp.const_mul 8)
  · exact hbound.mono (fun _ h => h.1)
  · exact hbound.mono (fun _ h => h.2)

end BrownianAffine
