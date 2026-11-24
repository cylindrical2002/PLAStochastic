import PLAStochastic.Affine.Moments.Optimal.Laplace.LaplaceReal
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Actual geometric expansions of the optimal convolution transform -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalQImageCoefficientB (n : ℕ) : ℝ := ((n:ℝ)+1)*((n:ℝ)+2)/2

def optimalQImageCoefficientC (n : ℕ) : ℝ := ((n:ℝ)+1)*((n:ℝ)+2)*(2*(n:ℝ)+3)/6

def optimalQImageLength (n : ℕ) (x y : ℝ) : ℝ := 2*(n:ℝ)+3-x-y

theorem optimalQImageCoefficientB_nonneg (n : ℕ) : 0 ≤ optimalQImageCoefficientB n := by
  unfold optimalQImageCoefficientB
  positivity

theorem optimalQImageCoefficientC_nonneg (n : ℕ) : 0 ≤ optimalQImageCoefficientC n := by
  unfold optimalQImageCoefficientC
  positivity

theorem optimalQImageLength_pos (n : ℕ) {x y : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) :
    0 < optimalQImageLength n x y := by
  unfold optimalQImageLength
  have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

theorem hasSum_optimalQImageCoefficientB {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n => optimalQImageCoefficientB n*q^n) (1/(1-q)^3) := by
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq₀] using hq₁
  convert! hasSum_choose_mul_geometric_of_norm_lt_one 2 hq using 1
  funext n
  rw [Nat.cast_choose_two]
  unfold optimalQImageCoefficientB
  push_cast
  ring

theorem hasSum_optimalQImageCoefficientC {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (fun n => optimalQImageCoefficientC n*q^n) ((1+q)/(1-q)^4) := by
  have hq : ‖q‖ < 1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg hq₀] using hq₁
  have h₃ := (hasSum_choose_mul_geometric_of_norm_lt_one 3 hq).mul_left (2:ℝ)
  have h₂ := hasSum_optimalQImageCoefficientB hq₀ hq₁
  convert! h₃.sub h₂ using 1
  · funext n
    have hc : ((n+3).choose 3:ℝ)=((n:ℝ)+3)*((n:ℝ)+2)*((n:ℝ)+1)/6 := by
      have h := congrArg (fun j : ℕ => (j:ℝ)) (Nat.add_one_mul_choose_eq (n+2) 2)
      norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at h
      change ((n:ℝ)+2+1)*((n+2).choose 2:ℝ)=((n+3).choose 3:ℝ)*3 at h
      rw [Nat.cast_choose_two] at h
      push_cast at h
      linear_combination -h/3
    rw [hc]
    unfold optimalQImageCoefficientC optimalQImageCoefficientB
    ring
  · have hqne : 1-q ≠ 0 := by linarith
    field_simp
    ring


theorem optimalQImage_exp_geometric (n : ℕ) (k : ℝ) :
    Real.exp (-(2*(n:ℝ)+3)*k)=Real.exp (-3*k)*(Real.exp (-2*k))^n := by
  rw [←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  ring

private theorem optimalQImage_geometric_denominatorB {k : ℝ} (hk : 0 < k) :
    Real.exp (-3*k)/(1-Real.exp (-2*k))^3=1/(8*Real.sinh k^3) := by
  have he2 : Real.exp (-2*k)=(Real.exp k)⁻¹^2 := by
    rw [←Real.exp_neg,←Real.exp_nat_mul]
    congr 1
    norm_num
  have he3 : Real.exp (-3*k)=(Real.exp k)⁻¹^3 := by
    rw [←Real.exp_neg,←Real.exp_nat_mul]
    congr 1
    norm_num
  have he : Real.exp k ≠ 0 := Real.exp_ne_zero _
  have hs : Real.exp k - (Real.exp k)⁻¹ ≠ 0 := by
    have h := Real.sinh_pos_iff.mpr hk
    rw [Real.sinh_eq,Real.exp_neg] at h
    linarith
  rw [he2,he3,Real.sinh_eq,Real.exp_neg]
  field_simp
  ring

private theorem optimalQImage_geometric_denominatorC {k : ℝ} (hk : 0 < k) :
    Real.exp (-3*k)*((1+Real.exp (-2*k))/(1-Real.exp (-2*k))^4)=
      Real.cosh k/(8*Real.sinh k^4) := by
  have he2 : Real.exp (-2*k)=(Real.exp k)⁻¹^2 := by
    rw [←Real.exp_neg,←Real.exp_nat_mul]
    congr 1
    norm_num
  have he3 : Real.exp (-3*k)=(Real.exp k)⁻¹^3 := by
    rw [←Real.exp_neg,←Real.exp_nat_mul]
    congr 1
    norm_num
  have he : Real.exp k ≠ 0 := Real.exp_ne_zero _
  have hs : Real.exp k - (Real.exp k)⁻¹ ≠ 0 := by
    have h := Real.sinh_pos_iff.mpr hk
    rw [Real.sinh_eq,Real.exp_neg] at h
    linarith
  rw [he2,he3,Real.sinh_eq,Real.cosh_eq,Real.exp_neg]
  field_simp
  ring

theorem hasSum_optimalQImageB_exp {k : ℝ} (hk : 0 < k) :
    HasSum (fun n => optimalQImageCoefficientB n*Real.exp (-(2*(n:ℝ)+3)*k))
      (1/(8*Real.sinh k^3)) := by
  have hq₀ := Real.exp_nonneg (-2*k)
  have hq₁ : Real.exp (-2*k) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  convert! (hasSum_optimalQImageCoefficientB hq₀ hq₁).mul_left (Real.exp (-3*k)) using 1
  · funext n
    rw [optimalQImage_exp_geometric]
    ring
  · rw [←optimalQImage_geometric_denominatorB hk]
    ring

theorem hasSum_optimalQImageC_exp {k : ℝ} (hk : 0 < k) :
    HasSum (fun n => optimalQImageCoefficientC n*Real.exp (-(2*(n:ℝ)+3)*k))
      (Real.cosh k/(8*Real.sinh k^4)) := by
  have hq₀ := Real.exp_nonneg (-2*k)
  have hq₁ : Real.exp (-2*k) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  convert! (hasSum_optimalQImageCoefficientC hq₀ hq₁).mul_left (Real.exp (-3*k)) using 1
  · funext n
    rw [optimalQImage_exp_geometric]
    ring
  · exact (optimalQImage_geometric_denominatorC hk).symm

end BrownianAffine
