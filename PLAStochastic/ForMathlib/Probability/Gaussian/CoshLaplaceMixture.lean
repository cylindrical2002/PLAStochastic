import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

/-! # The actual positive Gaussian Laplace mixture used for optimal moments -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem tiltedGaussian_complete_square {T : ℝ} (hT : 0 < T) (d x : ℝ) :
    Real.exp (d*x-T*x^2/2)=
      Real.exp (d^2/(2*T))*Real.exp (-(T/2)*(x-d/T)^2) := by
  rw [←Real.exp_add]
  congr 1
  field_simp
  ring

theorem integrable_tiltedGaussian {T : ℝ} (hT : 0 < T) (d : ℝ) :
    Integrable (fun x : ℝ => Real.exp (d*x-T*x^2/2)) volume := by
  have hi := ((integrable_exp_neg_mul_sq (by positivity : 0 < T/2)).comp_sub_right (d/T)).const_mul
    (Real.exp (d^2/(2*T)))
  have he : (fun x : ℝ => Real.exp (d*x-T*x^2/2))=
      fun x : ℝ => Real.exp (d^2/(2*T))*Real.exp (-(T/2)*(x-d/T)^2) := by
    funext x
    exact tiltedGaussian_complete_square hT d x
  rw [he]
  exact hi

theorem integral_tiltedGaussian {T : ℝ} (hT : 0 < T) (d : ℝ) :
    (∫ x : ℝ, Real.exp (d*x-T*x^2/2))=
      Real.exp (d^2/(2*T))*Real.sqrt (Real.pi/(T/2)) := by
  simp_rw [tiltedGaussian_complete_square hT d]
  rw [integral_const_mul,integral_sub_right_eq_self (fun x : ℝ => Real.exp (-(T/2)*x^2)),integral_gaussian]

theorem coshGaussian_eq_tilted (T d x : ℝ) :
    Real.cosh (d*x)*Real.exp (-T*x^2/2)=
      (Real.exp (d*x-T*x^2/2)+Real.exp ((-d)*x-T*x^2/2))/2 := by
  rw [Real.cosh_eq]
  simp only [Real.exp_sub,Real.exp_neg,neg_mul]
  have he : Real.exp (-(T*x^2)/2)=Real.exp (-(T*x^2/2)) := by congr 1; ring
  rw [he,Real.exp_neg]
  ring

theorem integrable_coshGaussian {T : ℝ} (hT : 0 < T) (d : ℝ) :
    Integrable (fun x : ℝ => Real.cosh (d*x)*Real.exp (-T*x^2/2)) volume := by
  have he : (fun x : ℝ => Real.cosh (d*x)*Real.exp (-T*x^2/2))=
      fun x : ℝ => (Real.exp (d*x-T*x^2/2)+Real.exp ((-d)*x-T*x^2/2))/2 := by
    funext x
    exact coshGaussian_eq_tilted T d x
  rw [he]
  exact ((integrable_tiltedGaussian hT d).add (integrable_tiltedGaussian hT (-d))).div_const 2

theorem integral_coshGaussian {T : ℝ} (hT : 0 < T) (d : ℝ) :
    (∫ x : ℝ, Real.cosh (d*x)*Real.exp (-T*x^2/2))=
      Real.exp (d^2/(2*T))*Real.sqrt (Real.pi/(T/2)) := by
  simp_rw [coshGaussian_eq_tilted]
  rw [integral_div,integral_add (integrable_tiltedGaussian hT d) (integrable_tiltedGaussian hT (-d)),
    integral_tiltedGaussian hT d,integral_tiltedGaussian hT (-d)]
  simp only [neg_sq]
  ring

/-- Full completion of the square and evenness give the genuine half-line identity. -/
theorem integral_coshGaussian_Ioi {T : ℝ} (hT : 0 < T) (d : ℝ) :
    (∫ k : ℝ in Ioi 0, Real.cosh (d*k)*Real.exp (-T*k^2/2))=
      Real.sqrt (Real.pi/(2*T))*Real.exp (d^2/(2*T)) := by
  let f : ℝ → ℝ := fun x => Real.cosh (d*x)*Real.exp (-T*x^2/2)
  have hneg : (∫ x : ℝ in Iic 0, f x)=∫ x : ℝ in Ioi 0, f x := by
    have he := integral_comp_neg_Ioi (0 : ℝ) f
    simp only [neg_zero] at he
    rw [←he]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [f,mul_neg,Real.cosh_neg,neg_sq]
  have h := integral_coshGaussian hT d
  change (∫ x : ℝ, f x)=_ at h
  rw [←integral_add_compl measurableSet_Ioi (integrable_coshGaussian hT d),compl_Ioi,hneg] at h
  have hs : Real.sqrt (Real.pi/(T/2))=2*Real.sqrt (Real.pi/(2*T)) := by
    rw [show Real.pi/(T/2)=4*(Real.pi/(2*T)) by field_simp; ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hs] at h
  change (∫ k : ℝ in Ioi 0, f k)=_
  linear_combination h/2

end BrownianAffine
