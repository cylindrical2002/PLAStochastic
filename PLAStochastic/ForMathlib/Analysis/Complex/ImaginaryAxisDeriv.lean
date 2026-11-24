import PLAStochastic.ForMathlib.Analysis.Complex.ParametricHolomorphicIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Real derivatives along the imaginary axis

For `f` holomorphic on an open set containing the imaginary axis, the real function
`y ↦ f(iy)` is smooth with `∂_yᵐ f(iy) = iᵐ f⁽ᵐ⁾(iy)` (`iteratedDeriv_comp_I_mul`). On the strip
`imagStrip δ = {|Re z| < δ}` the Cauchy estimate on the disc of radius `δ` around `iy` bounds
every real derivative by the supremum of `‖f‖` on that disc (`norm_iteratedDeriv_comp_I_mul_le`).
-/

noncomputable section
open Complex Set Metric
open scoped ContDiff
namespace PGM

/-- The open vertical strip `{z | |Re z| < δ}`. -/
def imagStrip (δ : ℝ) : Set ℂ := {z | |z.re| < δ}

theorem isOpen_imagStrip (δ : ℝ) : IsOpen (imagStrip δ) :=
  isOpen_lt (continuous_abs.comp continuous_re) continuous_const

theorem mem_imagStrip {δ : ℝ} {z : ℂ} : z ∈ imagStrip δ ↔ |z.re| < δ := Iff.rfl

theorem I_mul_ofReal_mem_imagStrip {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Complex.I * (y : ℂ) ∈ imagStrip δ := by
  simp [imagStrip, hδ]

theorem ball_I_mul_subset_imagStrip (δ y : ℝ) :
    ball (Complex.I * (y : ℂ)) δ ⊆ imagStrip δ := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  have h := abs_re_le_norm (z - Complex.I * (y : ℂ))
  simp only [sub_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero, sub_self,
    sub_zero] at h
  exact lt_of_le_of_lt h hz

/-- The chain rule along the imaginary axis. -/
theorem hasDerivAt_comp_I_mul {f : ℂ → ℂ} {f' : ℂ} {y : ℝ}
    (hf : HasDerivAt f f' (Complex.I * (y : ℂ))) :
    HasDerivAt (fun y : ℝ => f (Complex.I * (y : ℂ))) (f' * Complex.I) y := by
  have hl : HasDerivAt (fun y : ℝ => Complex.I * (y : ℂ)) Complex.I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp).const_mul Complex.I
  exact hf.comp y hl

/-- **Real derivatives on the imaginary axis.** `∂_yᵐ f(iy) = iᵐ f⁽ᵐ⁾(iy)`. -/
theorem iteratedDeriv_comp_I_mul {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hax : ∀ y : ℝ, Complex.I * (y : ℂ) ∈ U) (m : ℕ) :
    iteratedDeriv m (fun y : ℝ => f (Complex.I * (y : ℂ))) =
      fun y : ℝ => Complex.I ^ m * iteratedDeriv m f (Complex.I * (y : ℂ)) := by
  induction m with
  | zero =>
    funext y
    simp
  | succ m ih =>
    funext y
    rw [iteratedDeriv_succ, ih]
    have hd : DifferentiableAt ℂ (iteratedDeriv m f) (Complex.I * (y : ℂ)) :=
      ((differentiableOn_iteratedDeriv_open hU hf m) _ (hax y)).differentiableAt
        (hU.mem_nhds (hax y))
    have h := (hasDerivAt_comp_I_mul hd.hasDerivAt).const_mul (Complex.I ^ m)
    rw [h.deriv, iteratedDeriv_succ]
    ring

/-- `y ↦ f(iy)` is smooth. -/
theorem contDiff_comp_I_mul {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hax : ∀ y : ℝ, Complex.I * (y : ℂ) ∈ U) :
    ContDiff ℝ ∞ (fun y : ℝ => f (Complex.I * (y : ℂ))) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_comp_I_mul hU hf hax m]
  intro y
  have hd : DifferentiableAt ℂ (iteratedDeriv m f) (Complex.I * (y : ℂ)) :=
    ((differentiableOn_iteratedDeriv_open hU hf m) _ (hax y)).differentiableAt
      (hU.mem_nhds (hax y))
  exact ((hasDerivAt_comp_I_mul hd.hasDerivAt).const_mul (Complex.I ^ m)).differentiableAt

theorem contDiff_nat_comp_I_mul {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hax : ∀ y : ℝ, Complex.I * (y : ℂ) ∈ U) (n : ℕ) :
    ContDiff ℝ n (fun y : ℝ => f (Complex.I * (y : ℂ))) :=
  contDiff_infty.mp (contDiff_comp_I_mul hU hf hax) n

/-- **Cauchy estimate on the imaginary axis.** -/
theorem norm_iteratedDeriv_comp_I_mul_le {f : ℂ → ℂ} {δ M : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (imagStrip δ)) (y : ℝ)
    (hM : ∀ z ∈ ball (Complex.I * (y : ℂ)) δ, ‖f z‖ ≤ M) (m : ℕ) :
    ‖iteratedDeriv m (fun y : ℝ => f (Complex.I * (y : ℂ))) y‖ ≤
      m.factorial * M / (δ / 2) ^ m := by
  rw [iteratedDeriv_comp_I_mul (isOpen_imagStrip δ) hf (I_mul_ofReal_mem_imagStrip hδ) m,
    norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul]
  exact norm_iteratedDeriv_le_of_ball m hδ (hf.mono (ball_I_mul_subset_imagStrip δ y)) hM

end PGM
