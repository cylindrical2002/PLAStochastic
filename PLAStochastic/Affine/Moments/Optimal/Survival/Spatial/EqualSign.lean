import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Modes

/-! # Actual spatial integration of the equal-sign Gaussian images -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def imageEqualPrimitive (z A B d : ℝ) : ℝ :=
  Real.exp (z*d)*((A+B*d)/z^2-2*B/z^3)

def imageEqualInnerPrimitive (z A B d : ℝ) : ℝ :=
  Real.exp (z*d)*((A+B*d)/z-B/z^2)

theorem hasDerivAt_imageEqualPrimitive {z : ℝ} (hz : z≠0) (A B d : ℝ) :
    HasDerivAt (imageEqualPrimitive z A B) (imageEqualInnerPrimitive z A B d) d := by
  have he := ((hasDerivAt_id d).const_mul z).exp
  have hl := ((((hasDerivAt_id d).const_mul B).const_add A).div_const (z^2)).sub_const (2*B/z^3)
  convert! he.mul hl using 1
  dsimp only [imageEqualInnerPrimitive,id_eq]
  field_simp
  ring

theorem hasDerivAt_imageEqualInnerPrimitive {z : ℝ} (hz : z≠0) (A B d : ℝ) :
    HasDerivAt (imageEqualInnerPrimitive z A B) ((A+B*d)*Real.exp (z*d)) d := by
  have he := ((hasDerivAt_id d).const_mul z).exp
  have hl := ((((hasDerivAt_id d).const_mul B).const_add A).div_const z).sub_const (B/z^2)
  convert! he.mul hl using 1
  dsimp only [id_eq]
  field_simp
  ring

theorem integral_imageEqual_rectangle {z : ℝ} (hz : z≠0) (A B : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (A+B*(x+y-1))*Real.exp (z*(x+y-1))) =
      imageEqualPrimitive z A B 1-2*imageEqualPrimitive z A B 0+
        imageEqualPrimitive z A B (-1) := by
  have he (x : ℝ) :
      (∫ y in (0:ℝ)..1, (A+B*(x+y-1))*Real.exp (z*(x+y-1))) =
        imageEqualInnerPrimitive z A B x-imageEqualInnerPrimitive z A B (x-1) := by
    have hd (y : ℝ) : HasDerivAt (fun u => imageEqualInnerPrimitive z A B (x+u-1))
        ((A+B*(x+y-1))*Real.exp (z*(x+y-1))) y := by
      convert! (hasDerivAt_imageEqualInnerPrimitive hz A B (x+y-1)).comp y
          (((hasDerivAt_id y).const_add x).sub_const 1) using 1
      ring
    convert! intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)
      ((by fun_prop : Continuous (fun y : ℝ => (A+B*(x+y-1))*Real.exp (z*(x+y-1)))).intervalIntegrable 0 1) using 1
    simp only [add_sub_cancel_right,add_zero]
  simp_rw [he]
  have hd (x : ℝ) : HasDerivAt (fun u => imageEqualPrimitive z A B u-imageEqualPrimitive z A B (u-1))
      (imageEqualInnerPrimitive z A B x-imageEqualInnerPrimitive z A B (x-1)) x := by
    exact (hasDerivAt_imageEqualPrimitive hz A B x).sub (by
      convert! (hasDerivAt_imageEqualPrimitive hz A B (x-1)).comp x
        ((hasDerivAt_id x).sub_const 1) using 1
      ring)
  have hi : IntervalIntegrable (fun x => imageEqualInnerPrimitive z A B x-
      imageEqualInnerPrimitive z A B (x-1)) volume 0 1 := by
    exact (by unfold imageEqualInnerPrimitive; fun_prop : Continuous (fun x : ℝ =>
      imageEqualInnerPrimitive z A B x-imageEqualInnerPrimitive z A B (x-1))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) hi]
  norm_num
  ring

def imageEqualF (z : ℝ) : ℝ := 2*(Real.cosh z-1)/z^2

def imageEqualD (z : ℝ) : ℝ :=
  ((z-2)*Real.exp z-(z+2)*Real.exp (-z)+4)/z^3

theorem integral_imageEqual_FD {z : ℝ} (hz : z≠0) (A B : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1, (A+B*(x+y-1))*Real.exp (z*(x+y-1))) =
      A*imageEqualF z+B*imageEqualD z := by
  rw [integral_imageEqual_rectangle hz]
  simp only [imageEqualPrimitive,imageEqualF,imageEqualD,Real.cosh_eq,mul_one,mul_zero,
    Real.exp_zero,mul_neg_one,one_mul,add_zero]
  field_simp
  ring

theorem hasDerivAt_imageEqualF {z : ℝ} (hz : z≠0) :
    HasDerivAt imageEqualF (imageEqualD z) z := by
  have hd := (((Real.hasDerivAt_cosh z).sub_const 1).const_mul 2).div
    ((hasDerivAt_id z).pow 2) (pow_ne_zero _ hz)
  convert! hd using 1
  dsimp [imageEqualD]
  rw [Real.cosh_eq,Real.sinh_eq]
  field_simp
  ring

def imageEqualSpatialF (m T : ℝ) : ℝ :=
  Real.exp (-2*m^2/T)*imageEqualF (2*m/T)

def imageEqualSpatialD (m T : ℝ) : ℝ :=
  Real.exp (-2*m^2/T)*imageEqualD (2*m/T)

/-- The actual ++ spatial integral in the F_m,D_m notation. -/
theorem integral_imageEqual_pos_pos {m T : ℝ} (hm : 0<m) (hT : 0<T) (c b : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      (c*(2*m+1-x-y)-b*T)*Real.exp (-((2*m+1-x-y)^2-(x+y-1)^2)/(2*T))) =
      (2*m*c-b*T)*imageEqualSpatialF m T-c*imageEqualSpatialD m T := by
  have hz : 2*m/T≠0 := by positivity
  have he (x y : ℝ) :
      (c*(2*m+1-x-y)-b*T)*Real.exp (-((2*m+1-x-y)^2-(x+y-1)^2)/(2*T)) =
      Real.exp (-2*m^2/T)*((2*m*c-b*T+(-c)*(x+y-1))*Real.exp ((2*m/T)*(x+y-1))) := by
    have hx : Real.exp (-((2*m+1-x-y)^2-(x+y-1)^2)/(2*T)) =
        Real.exp (-2*m^2/T)*Real.exp ((2*m/T)*(x+y-1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hx]
    ring
  simp_rw [he,intervalIntegral.integral_const_mul]
  rw [integral_imageEqual_FD hz]
  unfold imageEqualSpatialF imageEqualSpatialD
  ring

/-- Simultaneous reflection of both spatial coordinates converts -- at m to ++ at m+1. -/
theorem integral_imageEqual_reflect (m T c b : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      (c*(2*m+1+x+y)-b*T)*Real.exp (-((2*m+1+x+y)^2-(x+y-1)^2)/(2*T))) =
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      (c*(2*(m+1)+1-x-y)-b*T)*Real.exp (-((2*(m+1)+1-x-y)^2-(x+y-1)^2)/(2*T))) := by
  let F : ℝ → ℝ → ℝ := fun x y =>
    (c*(2*(m+1)+1-x-y)-b*T)*Real.exp (-((2*(m+1)+1-x-y)^2-(x+y-1)^2)/(2*T))
  have he (x y : ℝ) :
      (c*(2*m+1+x+y)-b*T)*Real.exp (-((2*m+1+x+y)^2-(x+y-1)^2)/(2*T))=F (1-x) (1-y) := by
    dsimp only [F]
    congr 1 <;> congr 1 <;> ring
  simp_rw [he,intervalIntegral.integral_comp_sub_left]
  have hs := intervalIntegral.integral_comp_sub_left (fun x => ∫ y in (0:ℝ)..1, F x y)
    (a:=0) (b:=1) 1
  simpa only [sub_self,sub_zero] using hs

theorem integral_imageEqual_neg_neg {m T : ℝ} (hm : 0<m) (hT : 0<T) (c b : ℝ) :
    (∫ x in (0:ℝ)..1, ∫ y in (0:ℝ)..1,
      (c*(2*m+1+x+y)-b*T)*Real.exp (-((2*m+1+x+y)^2-(x+y-1)^2)/(2*T))) =
      (2*(m+1)*c-b*T)*imageEqualSpatialF (m+1) T-c*imageEqualSpatialD (m+1) T := by
  rw [integral_imageEqual_reflect,integral_imageEqual_pos_pos (by linarith : 0<m+1) hT]

/-- The coefficients of adjacent equal-sign images combine exactly as in the manuscript. -/
theorem imageEqual_paired_coefficients (m : ℝ) :
    m*(m+1)*(2*m+1)/6+(m-1)*m*(2*m-1)/6=m*(2*m^2+1)/3 ∧
    m*(m+1)/2+(m-1)*m/2=m^2 := by constructor <;> ring

end BrownianAffine
