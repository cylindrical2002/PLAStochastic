import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrtLocal
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Calculus.DSlope

/-! # Derivatives after even square-root descent

The derivative is a divided difference of the odd first derivative. This
formula retains its value at the merged root, without dividing by that root.
-/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem even_comp_sqrt_sq {R : ℝ} {F : ℂ → ℂ}
    (heven : ∀ r ∈ ball (0 : ℂ) R, F (-r) = F r) {r : ℂ}
    (hr : r ∈ ball (0 : ℂ) R) : F (sqrt (r ^ 2)) = F r := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (sqrt_sq_eq (r ^ 2)) with he | he
  · rw [he]
  · rw [he, heven r hr]

theorem deriv_even_comp_square {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (heven : ∀ r ∈ ball (0 : ℂ) R, F (-r) = F r) {r : ℂ}
    (hr : r ∈ ball (0 : ℂ) R) :
    deriv F r = deriv (fun q => F (sqrt q)) (r ^ 2) * (2 * r) := by
  have hrq : r ^ 2 ∈ ball (0 : ℂ) (R ^ 2) := by
    rw [mem_ball_zero_iff, norm_pow]
    exact pow_lt_pow_left₀ (mem_ball_zero_iff.mp hr) (norm_nonneg r) (by norm_num)
  have hE := ((differentiableOn_comp_sqrt_of_locally_even hR hF heven) _ hrq).differentiableAt
    (isOpen_ball.mem_nhds hrq)
  have hd := hE.hasDerivAt.comp r (hasDerivAt_pow 2 r)
  have heq : F =ᶠ[𝓝 r] fun r => F (sqrt (r ^ 2)) := by
    filter_upwards [isOpen_ball.mem_nhds hr] with s hs
    exact (even_comp_sqrt_sq heven hs).symm
  simpa using! (hd.congr_of_eventuallyEq heq).deriv

theorem deriv_comp_sqrt_zero_of_locally_even {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (heven : ∀ r ∈ ball (0 : ℂ) R, F (-r) = F r) :
    deriv (fun q => F (sqrt q)) 0 = deriv (deriv F) 0 / 2 := by
  let E : ℂ → ℂ := fun q => F (sqrt q)
  have hE := differentiableOn_comp_sqrt_of_locally_even hR hF heven
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (R ^ 2) := mem_ball_self (by positivity)
  have hE' : DifferentiableAt ℂ (deriv E) 0 :=
    ((hE.deriv isOpen_ball) 0 h0).differentiableAt (isOpen_ball.mem_nhds h0)
  have hd := (hE'.hasDerivAt.comp_of_eq 0 (hasDerivAt_pow 2 (0 : ℂ)) (by simp)).mul
    ((hasDerivAt_id' (0 : ℂ)).const_mul (2 : ℂ))
  have heq : deriv F =ᶠ[𝓝 0] fun r => deriv E (r ^ 2) * (2 * r) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hR] with r hr
    exact deriv_even_comp_square hR hF heven hr
  have hh := (hd.congr_of_eventuallyEq heq).deriv
  change deriv (deriv F) 0 = _ at hh
  simp only [Nat.cast_ofNat, mul_zero, zero_add, Function.comp_apply,
    zero_pow (by decide : 2 ≠ 0), mul_one] at hh
  change deriv E 0 = deriv (deriv F) 0 / 2
  rw [hh]
  ring

theorem deriv_comp_sqrt_eq_dslope_of_locally_even {R : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (heven : ∀ r ∈ ball (0 : ℂ) R, F (-r) = F r) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) (R ^ 2)) :
    deriv (fun q => F (sqrt q)) q = dslope (deriv F) (-sqrt q) (sqrt q) / 2 := by
  have hr : sqrt q ∈ ball (0 : ℂ) R :=
    mem_ball_zero_iff.mpr (norm_sqrt_lt hR (mem_ball_zero_iff.mp hq))
  by_cases hq0 : q = 0
  · subst q
    rw [sqrt_zero, neg_zero, dslope_same]
    exact deriv_comp_sqrt_zero_of_locally_even hR hF heven
  have hr0 : sqrt q ≠ 0 := by
    intro h
    have := sqrt_sq_eq q
    rw [h, zero_pow (by decide : 2 ≠ 0)] at this
    exact hq0 this.symm
  have hne : sqrt q ≠ -sqrt q := by intro h; apply hr0; linear_combination h / 2
  have hm : -sqrt q ∈ ball (0 : ℂ) R := by simpa only [mem_ball_zero_iff, norm_neg] using hr
  have hp := deriv_even_comp_square hR hF heven hr
  have hn := deriv_even_comp_square hR hF heven hm
  rw [sqrt_sq_eq] at hp
  rw [neg_sq, sqrt_sq_eq] at hn
  rw [dslope_of_ne _ hne, slope_def_field, hp, hn]
  field_simp

theorem norm_iteratedDeriv_comp_sqrt_le_of_locally_even {R M : ℝ} (hR : 0 < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 R))
    (heven : ∀ r ∈ ball (0 : ℂ) R, F (-r) = F r)
    (hM : ∀ r ∈ ball (0 : ℂ) R, ‖F r‖ ≤ M) (n : ℕ) {q : ℂ}
    (hq : q ∈ ball (0 : ℂ) (R ^ 2 / 2)) :
    ‖iteratedDeriv n (fun q => F (sqrt q)) q‖ ≤ n.factorial * M / (R ^ 2 / 4) ^ n := by
  apply norm_iteratedDeriv_le_of_ball_half n (by positivity)
    (differentiableOn_comp_sqrt_of_locally_even hR hF heven) ?_ hq
  intro z hz
  exact hM (sqrt z) (mem_ball_zero_iff.mpr (norm_sqrt_lt hR (mem_ball_zero_iff.mp hz)))

end PGM
