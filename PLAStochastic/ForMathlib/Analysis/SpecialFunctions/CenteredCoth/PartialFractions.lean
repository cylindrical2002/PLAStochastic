import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ReciprocalSinhMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The actual centered hyperbolic cotangent and its convergent partial fractions -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- The centered cotangent in the optimal-moment integrands, with its removable value zero. -/
def centeredCoth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x - 1/x

/-- Positive poles used in the actual cotangent partial fraction expansion. -/
def cothPole (n : ℕ) : ℝ := Real.pi*((n : ℝ)+1)

theorem cothPole_pos (n : ℕ) : 0 < cothPole n := by unfold cothPole; positivity

/-- At an imaginary argument the complex partial fraction term is a real positive kernel. -/
theorem imaginary_cotTerm {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Complex.I/(Real.pi : ℂ) * cotTerm (((x/Real.pi : ℝ) : ℂ)*Complex.I) n =
      ((2*x/(x^2+cothPole n^2) : ℝ) : ℂ) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hp : (((x/Real.pi : ℝ) : ℂ)*Complex.I) ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨m, hm⟩
    have hh := congrArg Complex.im hm
    simp only [Complex.intCast_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hh
    exact (div_pos hx Real.pi_pos).ne' hh.symm
  rw [cotTerm_identity hp n]
  have hm : (((x/Real.pi : ℝ) : ℂ)*Complex.I) - ((n : ℂ)+1) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, Complex.add_im,
      Complex.natCast_im, Complex.one_im, sub_zero, Complex.zero_im] at hh
    exact (div_pos hx Real.pi_pos).ne' hh
  have hp' : (((x/Real.pi : ℝ) : ℂ)*Complex.I) + ((n : ℂ)+1) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero,
      Complex.natCast_im, Complex.one_im, Complex.zero_im] at hh
    exact (div_pos hx Real.pi_pos).ne' hh
  have hd : ((x^2+cothPole n^2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  unfold cothPole at *
  push_cast at *
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring_nf
  rw [← mul_neg, ← inv_neg]
  congr 2
  ring

/-- The infinite series comes from the genuine cotangent theorem, not a postulated expansion. -/
theorem hasSum_centeredCoth {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 2*x/(x^2+cothPole n^2)) (centeredCoth x) := by
  let z : ℂ := ((x/Real.pi : ℝ) : ℂ)*Complex.I
  have hz : z ∈ Complex.integerComplement := by
    rw [Complex.mem_integerComplement_iff]
    rintro ⟨m, hm⟩
    have hh := congrArg Complex.im hm
    simp only [z, Complex.intCast_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hh
    exact (div_pos hx Real.pi_pos).ne' hh.symm
  have hsum := (summable_cotTerm hz).hasSum
  rw [← cot_series_rep' hz] at hsum
  have h := hsum.mul_left (Complex.I/(Real.pi : ℂ))
  have hval : Complex.I/(Real.pi : ℂ) *
      ((Real.pi : ℂ)*Complex.cot ((Real.pi : ℂ)*z)-1/z) = (centeredCoth x : ℂ) := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hsh : (Real.sinh x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr hx.ne')
    have harg : (Real.pi : ℂ)*z = (x : ℂ)*Complex.I := by dsimp [z]; push_cast; field_simp
    rw [harg, Complex.cot, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    unfold centeredCoth z
    push_cast
    field_simp
  rw [hval] at h
  apply Complex.hasSum_ofReal.mp
  convert! h using 1
  funext n
  exact (imaginary_cotTerm hx n).symm

end BrownianAffine
