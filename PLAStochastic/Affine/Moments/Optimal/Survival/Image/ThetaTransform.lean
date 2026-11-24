import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! # The alternating Gaussian transformation underlying cross-boundary images -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem complex_exp_integer_phase (a : ℝ) (n : ℤ) :
    Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (n : ℂ)^2 +
      2 * (Real.pi : ℂ) * (Complex.I/2) * (n : ℂ)) =
        ((Real.cos ((n : ℝ)*Real.pi) * Real.exp (-Real.pi*a*(n : ℝ)^2) : ℝ) : ℂ) := by
  have he : -(Real.pi : ℂ) * (a : ℂ) * (n : ℂ)^2 +
      2 * (Real.pi : ℂ) * (Complex.I/2) * (n : ℂ) =
        ((-Real.pi*a*(n : ℝ)^2 : ℝ) : ℂ) + (((n : ℝ)*Real.pi : ℝ) : ℂ)*Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.sin_int_mul_pi]
  simp only [Complex.ofReal_zero, zero_mul, add_zero, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  congr 1
  ring

/-- The shift by a half integer is obtained from the proved Poisson summation
formula, rather than postulated as an image representation. -/
theorem alternating_gaussian_poisson {a : ℝ} (ha : 0 < a) :
    (∑' n : ℤ, Real.cos ((n : ℝ)*Real.pi) * Real.exp (-Real.pi*a*(n : ℝ)^2)) =
      (1 / a^(1/2 : ℝ)) * ∑' n : ℤ, Real.exp (-Real.pi/a*((n : ℝ)-1/2)^2) := by
  have hp := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa only [Complex.ofReal_re] using ha) (Complex.I/2)
  have hi (n : ℤ) : (n : ℂ) + Complex.I*(Complex.I/2) =
      (((n : ℝ)-1/2 : ℝ) : ℂ) := by
    push_cast
    rw [← mul_div_assoc, ← pow_two, Complex.I_sq]
    ring
  simp_rw [complex_exp_integer_phase, hi] at hp
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_tsum, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_cpow ha.le, Complex.ofReal_ofNat,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow] using hp

def alternatingHeatTheta (t : ℝ) : ℝ :=
  ∑' n : ℤ, Real.cos ((n : ℝ)*Real.pi) * Real.exp (-Real.pi^2*(n : ℝ)^2*t/2)

theorem alternatingHeatTheta_image {t : ℝ} (ht : 0 < t) :
    alternatingHeatTheta t = (1 / (Real.pi*t/2)^(1/2 : ℝ)) *
      ∑' n : ℤ, Real.exp (-2*((n : ℝ)-1/2)^2/t) := by
  have hp := alternating_gaussian_poisson (a := Real.pi*t/2) (by positivity)
  have he (n : ℤ) : -Real.pi*(Real.pi*t/2)*(n : ℝ)^2 = -Real.pi^2*(n : ℝ)^2*t/2 := by ring
  have hi (n : ℤ) : -Real.pi/(Real.pi*t/2)*((n : ℝ)-1/2)^2 = -2*((n : ℝ)-1/2)^2/t := by
    field_simp
  simpa only [he, hi, alternatingHeatTheta] using hp

end BrownianAffine
