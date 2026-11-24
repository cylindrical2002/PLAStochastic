import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Cauchy estimates on open discs

Wrappers around `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` for functions that
are holomorphic and bounded on an open disc (no continuity on the closed disc is required):

* `norm_iteratedDeriv_le_of_ball`: `‖f⁽ⁿ⁾(c)‖ ≤ n! M / (r/2)ⁿ` if `‖f‖ ≤ M` on `B(c, r)`;
* `norm_iteratedDeriv_le_of_ball_half`: the same at every `z ∈ B(c, r/2)` with `(r/4)ⁿ`;
* `norm_sub_sub_deriv_le_of_ball`: the second-order Taylor bound
  `‖f(z) - f(c) - f'(c)(z - c)‖ ≤ (32 M / r²) ‖z - c‖²` on `B(c, r/2)`.
-/

noncomputable section

open Set Metric

namespace PGM

variable {f : ℂ → ℂ} {c : ℂ} {r M : ℝ}

/-- Cauchy estimate from a bound on the open disc. -/
theorem norm_iteratedDeriv_le_of_ball (n : ℕ) (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * M / (r / 2) ^ n := by
  have hr2 : r / 2 < r := half_lt_self hr
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n (half_pos hr)
    (hf.diffContOnCl_ball (closedBall_subset_ball hr2)) fun z hz => hM z ?_
  exact sphere_subset_ball hr2 hz

/-- Cauchy estimate at the points of the half disc. -/
theorem norm_iteratedDeriv_le_of_ball_half (n : ℕ) (hr : 0 < r)
    (hf : DifferentiableOn ℂ f (ball c r)) (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) {z : ℂ}
    (hz : z ∈ ball c (r / 2)) :
    ‖iteratedDeriv n f z‖ ≤ n.factorial * M / (r / 4) ^ n := by
  have hsub : ball z (r / 2) ⊆ ball c r := by
    intro w hw
    rw [mem_ball] at hw hz ⊢
    calc dist w c ≤ dist w z + dist z c := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add hw hz
      _ = r := by ring
  have := norm_iteratedDeriv_le_of_ball n (half_pos hr) (hf.mono hsub)
    (fun w hw => hM w (hsub hw))
  rwa [show r / 2 / 2 = r / 4 by ring] at this

/-- `‖f'‖ ≤ 4 M / r` on the half disc. -/
theorem norm_deriv_le_of_ball_half (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ ball c (r / 2)) :
    ‖deriv f z‖ ≤ 4 * M / r := by
  have := norm_iteratedDeriv_le_of_ball_half 1 hr hf hM hz
  rw [iteratedDeriv_one] at this
  calc ‖deriv f z‖ ≤ (Nat.factorial 1) * M / (r / 4) ^ 1 := this
    _ = 4 * M / r := by simp; field_simp

/-- Mean value inequality on the half disc from a bound on the disc. -/
theorem norm_sub_le_of_ball_half (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) {z w : ℂ} (hz : z ∈ ball c (r / 2))
    (hw : w ∈ ball c (r / 2)) : ‖f z - f w‖ ≤ 4 * M / r * ‖z - w‖ := by
  have hsub : ball c (r / 2) ⊆ ball c r := ball_subset_ball (by linarith)
  exact (convex_ball c (r / 2)).norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hf x (hsub hx)).differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
    (fun x hx => norm_deriv_le_of_ball_half hr hf hM hx) hw hz

/-- Second-order Taylor bound on the half disc. -/
theorem norm_sub_sub_deriv_le_of_ball (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball c r))
    (hM : ∀ z ∈ ball c r, ‖f z‖ ≤ M) {z : ℂ} (hz : z ∈ ball c (r / 2)) :
    ‖f z - f c - deriv f c * (z - c)‖ ≤ 32 * M / r ^ 2 * ‖z - c‖ ^ 2 := by
  have hsub : ball c (r / 2) ⊆ ball c r := ball_subset_ball (by linarith)
  have hc : c ∈ ball c (r / 2) := mem_ball_self (half_pos hr)
  have hdiff : ∀ x ∈ ball c (r / 2), DifferentiableAt ℂ f x := fun x hx =>
    (hf x (hsub hx)).differentiableAt (isOpen_ball.mem_nhds (hsub hx))
  have hf' : DifferentiableOn ℂ (deriv f) (ball c r) := hf.deriv isOpen_ball
  have hdiff' : ∀ x ∈ ball c (r / 2), DifferentiableAt ℂ (deriv f) x := fun x hx =>
    (hf' x (hsub hx)).differentiableAt (isOpen_ball.mem_nhds (hsub hx))
  -- `‖f''‖ ≤ 32 M / r²` on the half disc
  have h2 : ∀ x ∈ ball c (r / 2), ‖deriv (deriv f) x‖ ≤ 32 * M / r ^ 2 := by
    intro x hx
    have := norm_iteratedDeriv_le_of_ball_half 2 hr hf hM hx
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    calc ‖deriv (deriv f) x‖ ≤ (Nat.factorial 2) * M / (r / 4) ^ 2 := this
      _ = 32 * M / r ^ 2 := by simp [Nat.factorial]; field_simp; ring
  -- the derivative of `g x = f x - f c - f'(c)(x - c)` is `f'(x) - f'(c)`
  set g : ℂ → ℂ := fun x => f x - f c - deriv f c * (x - c) with hg
  have hgd : ∀ x ∈ ball c (r / 2), HasDerivAt g (deriv f x - deriv f c) x := by
    intro x hx
    have h1 := (hdiff x hx).hasDerivAt
    have h3 : HasDerivAt (fun x => deriv f c * (x - c)) (deriv f c * 1) x :=
      ((hasDerivAt_id x).sub_const c).const_mul _
    exact ((h1.sub_const (f c)).sub h3).congr_deriv (by ring)
  have hgb : ∀ x ∈ segment ℝ c z, ‖deriv f x - deriv f c‖ ≤ 32 * M / r ^ 2 * ‖z - c‖ := by
    intro x hx
    have hxb : x ∈ ball c (r / 2) := (convex_ball c (r / 2)).segment_subset hc hz hx
    have := (convex_ball c (r / 2)).norm_image_sub_le_of_norm_deriv_le hdiff' h2 hc hxb
    calc ‖deriv f x - deriv f c‖ ≤ 32 * M / r ^ 2 * ‖x - c‖ := this
      _ ≤ 32 * M / r ^ 2 * ‖z - c‖ := by
          have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c (mem_ball_self hr))
          gcongr
          rw [segment_eq_image'] at hx
          obtain ⟨t, ht, rfl⟩ := hx
          simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
          rw [abs_of_nonneg ht.1]
          exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  have key := (convex_segment c z).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (fun x hx => (hgd x ((convex_ball c (r / 2)).segment_subset hc hz hx)).hasDerivWithinAt)
    hgb (left_mem_segment ℝ c z) (right_mem_segment ℝ c z)
  have hg0 : g c = 0 := by simp [hg]
  rw [hg0, sub_zero] at key
  calc ‖f z - f c - deriv f c * (z - c)‖ = ‖g z‖ := rfl
    _ ≤ 32 * M / r ^ 2 * ‖z - c‖ * ‖z - c‖ := key
    _ = 32 * M / r ^ 2 * ‖z - c‖ ^ 2 := by ring

end PGM
