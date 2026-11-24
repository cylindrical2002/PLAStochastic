import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Entire functions of the squared Brownian root

`cepsBrownianCosh w = cosh (√w)` and `cepsBrownianSinhc w = sinh (√w) / √w`,
with value one at zero. Both functions are entire, including across the root's branch cut.
-/

noncomputable section

open Complex Set Metric Filter Topology

namespace PGM

private theorem entire_even_sqrt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (he : ∀ r, f (-r) = f r) : Differentiable ℂ (fun w => f (Complex.sqrt w)) := by
  intro w
  let r : ℝ := ‖w‖ + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hw : w ∈ ball (0 : ℂ) (r ^ 2) := by
    rw [mem_ball, dist_zero_right]
    dsimp [r]
    nlinarith [norm_nonneg w]
  exact ((differentiableOn_comp_sqrt_of_even hr hf.differentiableOn he) w hw).differentiableAt
    (isOpen_ball.mem_nhds hw)

private theorem sinh_dslope_even (r : ℂ) : dslope Complex.sinh 0 (-r) = dslope Complex.sinh 0 r := by
  by_cases hr : r = 0
  · simp [hr]
  · rw [dslope_of_ne _ (neg_ne_zero.mpr hr), dslope_of_ne _ hr]
    simp [slope_def_field, Complex.sinh_neg]

/-- The entire function `cosh √w`. -/
def cepsBrownianCosh (w : ℂ) : ℂ := Complex.cosh (Complex.sqrt w)

/-- The entire function `sinh √w / √w`, with its analytic value at zero. -/
def cepsBrownianSinhc (w : ℂ) : ℂ := dslope Complex.sinh 0 (Complex.sqrt w)

theorem cepsBrownianCosh_differentiable : Differentiable ℂ cepsBrownianCosh :=
  entire_even_sqrt Complex.differentiable_cosh Complex.cosh_neg

theorem cepsBrownianSinhc_differentiable : Differentiable ℂ cepsBrownianSinhc := by
  have hd : Differentiable ℂ (dslope Complex.sinh 0) := by
    rw [← differentiableOn_univ]
    exact (differentiableOn_dslope (univ_mem : (univ : Set ℂ) ∈ 𝓝 0)).mpr
      Complex.differentiable_sinh.differentiableOn
  exact entire_even_sqrt hd sinh_dslope_even

@[simp] theorem cepsBrownianCosh_zero : cepsBrownianCosh 0 = 1 := by
  simp [cepsBrownianCosh]

@[simp] theorem cepsBrownianSinhc_zero : cepsBrownianSinhc 0 = 1 := by
  simp [cepsBrownianSinhc, Complex.deriv_sinh]

theorem cepsBrownianCosh_sq (a : ℂ) : cepsBrownianCosh (a ^ 2) = Complex.cosh a := by
  have hs : Complex.sqrt (a ^ 2) ^ 2 = a ^ 2 := sqrt_sq_eq _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · rw [cepsBrownianCosh, h]
  · rw [cepsBrownianCosh, h, Complex.cosh_neg]

theorem cepsBrownianSinhc_sq (a : ℂ) : cepsBrownianSinhc (a ^ 2) = dslope Complex.sinh 0 a := by
  have hs : Complex.sqrt (a ^ 2) ^ 2 = a ^ 2 := sqrt_sq_eq _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · rw [cepsBrownianSinhc, h]
  · rw [cepsBrownianSinhc, h, sinh_dslope_even]

theorem cepsBrownianSinhc_mul (a : ℂ) : a * cepsBrownianSinhc (a ^ 2) = Complex.sinh a := by
  rw [cepsBrownianSinhc_sq]
  simpa [smul_eq_mul] using sub_smul_dslope Complex.sinh 0 a

theorem cepsBrownianCosh_sub_mul_sinhc (a : ℂ) :
    cepsBrownianCosh (a ^ 2) - a * cepsBrownianSinhc (a ^ 2) = Complex.exp (-a) := by
  rw [cepsBrownianCosh_sq, cepsBrownianSinhc_mul, Complex.cosh_sub_sinh]

end PGM
