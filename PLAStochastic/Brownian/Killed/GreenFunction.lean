import PLAStochastic.Brownian.Killed.Semigroup
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Explicit Green function for one half of the Laplacian on a finite interval. -/
def dirichletGreen (r k x z : ℝ) : ℝ :=
  2 * Real.sinh (k * min x z) * Real.sinh (k * (r - max x z)) / (k * Real.sinh (k*r))

theorem continuous_dirichletGreen_right (r k x : ℝ) : Continuous (dirichletGreen r k x) := by
  change Continuous (fun z => 2 * Real.sinh (k * min x z) * Real.sinh (k * (r - max x z)) / (k * Real.sinh (k*r)))
  fun_prop

theorem dirichletGreen_of_le {r k x z : ℝ} (hz : z ≤ x) :
    dirichletGreen r k x z = (2*Real.sinh (k*(r-x))/(k*Real.sinh (k*r)))*Real.sinh (k*z) := by
  unfold dirichletGreen
  rw [min_eq_right hz, max_eq_left hz]
  ring

theorem dirichletGreen_of_ge {r k x z : ℝ} (hz : x ≤ z) :
    dirichletGreen r k x z = (2*Real.sinh (k*x)/(k*Real.sinh (k*r)))*Real.sinh (k*(r-z)) := by
  unfold dirichletGreen
  rw [min_eq_left hz, max_eq_right hz]
  ring

private theorem deriv_sinh_sin_primitive {k a : ℝ} (hk : 0 < k) (u : ℝ) :
    HasDerivAt (fun u => (k*Real.cosh (k*u)*Real.sin (a*u)-a*Real.sinh (k*u)*Real.cos (a*u))/(k^2+a^2))
      (Real.sinh (k*u)*Real.sin (a*u)) u := by
  have hk' := (hasDerivAt_id u).const_mul k
  have ha := (hasDerivAt_id u).const_mul a
  convert! (((hk'.cosh.const_mul k).mul ha.sin).sub
    ((hk'.sinh.const_mul a).mul ha.cos)).div_const (k^2+a^2) using 1
  have hd : k^2+a^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hk) (sq_nonneg a))
  simp only [id_eq]
  field_simp
  ring

private theorem deriv_reflected_sinh_sin_primitive {k a : ℝ} (hk : 0 < k) (r u : ℝ) :
    HasDerivAt (fun u => (-k*Real.cosh (k*(r-u))*Real.sin (a*u)-a*Real.sinh (k*(r-u))*Real.cos (a*u))/(k^2+a^2))
      (Real.sinh (k*(r-u))*Real.sin (a*u)) u := by
  have hk' := ((hasDerivAt_id u).const_sub r).const_mul k
  have ha := (hasDerivAt_id u).const_mul a
  convert! (((hk'.cosh.const_mul (-k)).mul ha.sin).sub
    ((hk'.sinh.const_mul a).mul ha.cos)).div_const (k^2+a^2) using 1
  have hd : k^2+a^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hk) (sq_nonneg a))
  simp only [id_eq]
  field_simp
  ring

theorem integral_sinh_mul_sin {k : ℝ} (hk : 0 < k) (a x : ℝ) :
    (∫ u in (0 : ℝ)..x, Real.sinh (k*u)*Real.sin (a*u)) =
      (k*Real.cosh (k*x)*Real.sin (a*x)-a*Real.sinh (k*x)*Real.cos (a*x))/(k^2+a^2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => deriv_sinh_sin_primitive hk u) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp

theorem integral_reflected_sinh_mul_sin {r k : ℝ} (hr : 0 < r) (hk : 0 < k) (n : ℕ) (x : ℝ) :
    (∫ u in x..r, Real.sinh (k*(r-u))*Real.sin (heatFrequency r n*u)) =
      (k*Real.cosh (k*(r-x))*Real.sin (heatFrequency r n*x)+
        heatFrequency r n*Real.sinh (k*(r-x))*Real.cos (heatFrequency r n*x))/(k^2+heatFrequency r n^2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => deriv_reflected_sinh_sin_primitive hk r u) (by apply Continuous.intervalIntegrable; fun_prop)]
  have hs : Real.sin (heatFrequency r n*r)=0 := by
    rw [heatFrequency_mul_width hr.ne']
    exact_mod_cast Real.sin_nat_mul_pi (n+1)
  simp only [sub_self, mul_zero, Real.cosh_zero, mul_one, hs, Real.sinh_zero, zero_mul]
  ring

/-- Exact sine coefficient obtained from both sides of the Green function's derivative jump. -/
theorem integral_dirichletGreen_sine {r k x : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hx : x ∈ Icc 0 r) (n : ℕ) :
    (∫ z in (0 : ℝ)..r, dirichletGreen r k x z*Real.sin (heatFrequency r n*z)) =
      Real.sin (heatFrequency r n*x)/(k^2/2+heatFrequency r n^2/2) := by
  have hc : Continuous (fun z => dirichletGreen r k x z*Real.sin (heatFrequency r n*z)) :=
    (continuous_dirichletGreen_right r k x).mul (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 x)
    (hc.intervalIntegrable x r)]
  have hleft : (∫ z in (0 : ℝ)..x, dirichletGreen r k x z*Real.sin (heatFrequency r n*z)) =
      (2*Real.sinh (k*(r-x))/(k*Real.sinh (k*r)))*
        (∫ z in (0 : ℝ)..x, Real.sinh (k*z)*Real.sin (heatFrequency r n*z)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hx.1] at hz
    dsimp only
    rw [dirichletGreen_of_le hz.2]
    ring
  have hright : (∫ z in x..r, dirichletGreen r k x z*Real.sin (heatFrequency r n*z)) =
      (2*Real.sinh (k*x)/(k*Real.sinh (k*r)))*
        (∫ z in x..r, Real.sinh (k*(r-z))*Real.sin (heatFrequency r n*z)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hx.2] at hz
    dsimp only
    rw [dirichletGreen_of_ge hz.1]
    ring
  rw [hleft, hright, integral_sinh_mul_sin hk, integral_reflected_sinh_mul_sin hr hk]
  have hd : k^2+heatFrequency r n^2 ≠ 0 := by positivity
  have hsh : Real.sinh (k*r) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos hk hr)).ne'
  have hadd : Real.sinh (k*x)*Real.cosh (k*(r-x))+Real.cosh (k*x)*Real.sinh (k*(r-x)) =
      Real.sinh (k*r) := by
    rw [← Real.sinh_add]
    congr 1
    ring
  have hden : k^2/2+heatFrequency r n^2/2 ≠ 0 := by positivity
  field_simp
  linear_combination k * Real.sin (x * heatFrequency r n) * hadd

 theorem dirichletGreen_nonneg {r k x z : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hx : x ∈ Icc 0 r) (hz : z ∈ Icc 0 r) : 0 ≤ dirichletGreen r k x z := by
  unfold dirichletGreen
  have hmin : 0 ≤ min x z := le_min hx.1 hz.1
  have hmax : max x z ≤ r := max_le hx.2 hz.2
  have hleft := Real.sinh_nonneg_iff.mpr (mul_nonneg hk.le hmin)
  have hright := Real.sinh_nonneg_iff.mpr (mul_nonneg hk.le (sub_nonneg.mpr hmax))
  have hden := Real.sinh_pos_iff.mpr (mul_pos hk hr)
  positivity

end BrownianAffine
