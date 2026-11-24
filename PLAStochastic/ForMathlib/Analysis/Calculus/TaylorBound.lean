import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Taylor's formula with a derivative bound on a segment

For `f : ℝ → E` of class `Cⁿ` with `‖f⁽ⁿ⁾‖ ≤ L` on the segment `[[x₀, x]]`,
`‖f x - ∑_{m < n} (x - x₀)^m / m! • f⁽ᵐ⁾(x₀)‖ ≤ L |x - x₀|ⁿ` (`norm_sub_taylor_le`), stated with
`iteratedDeriv` on the whole line. The proof differentiates the remainder and inducts on `n`
with the mean value inequality.
-/

namespace PGM

noncomputable section

open Set Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a Taylor polynomial is the Taylor polynomial of the derivative. -/
theorem hasDerivAt_taylorSum (n : ℕ) (f : ℝ → E) (x₀ t : ℝ) :
    HasDerivAt (fun s => ∑ m ∈ range (n + 1), ((m.factorial : ℝ)⁻¹ * (s - x₀) ^ m) •
        iteratedDeriv m f x₀)
      (∑ m ∈ range n, ((m.factorial : ℝ)⁻¹ * (t - x₀) ^ m) • iteratedDeriv m (deriv f) x₀) t := by
  have hp : ∀ m ∈ range (n + 1), HasDerivAt
      (fun s => ((m.factorial : ℝ)⁻¹ * (s - x₀) ^ m) • iteratedDeriv m f x₀)
      (((m.factorial : ℝ)⁻¹ * ((m : ℝ) * (t - x₀) ^ (m - 1))) • iteratedDeriv m f x₀) t := by
    intro m _
    have h0 : HasDerivAt (fun s : ℝ => s - x₀) 1 t := (hasDerivAt_id' t).sub_const x₀
    have h1 := HasDerivAt.const_mul ((m.factorial : ℝ)⁻¹) (HasDerivAt.fun_pow h0 m)
    rw [mul_one] at h1
    exact HasDerivAt.smul_const h1 _
  refine (HasDerivAt.fun_sum hp).congr_deriv ?_
  rw [sum_range_succ']
  simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_smul, add_zero]
  refine sum_congr rfl fun m _ => ?_
  rw [iteratedDeriv_succ', Nat.add_sub_cancel]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **Taylor's formula with a derivative bound.** -/
theorem norm_sub_taylor_le : ∀ (n : ℕ) {f : ℝ → E}, ContDiff ℝ n f → ∀ (x₀ x : ℝ) {L : ℝ},
    (∀ t ∈ uIcc x₀ x, ‖iteratedDeriv n f t‖ ≤ L) →
    ‖f x - ∑ m ∈ range n, ((m.factorial : ℝ)⁻¹ * (x - x₀) ^ m) • iteratedDeriv m f x₀‖ ≤
      L * |x - x₀| ^ n
  | 0, f, _, x₀, x, L, hL => by
    simpa using hL x right_mem_uIcc
  | n + 1, f, hf, x₀, x, L, hL => by
    have hf' : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by exact_mod_cast hf
    obtain ⟨hdf, -, hd⟩ := contDiff_succ_iff_deriv.mp hf'
    have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL x right_mem_uIcc)
    have hderiv : ∀ t, HasDerivAt (fun s => f s - ∑ m ∈ range (n + 1),
        ((m.factorial : ℝ)⁻¹ * (s - x₀) ^ m) • iteratedDeriv m f x₀)
        (deriv f t - ∑ m ∈ range n, ((m.factorial : ℝ)⁻¹ * (t - x₀) ^ m) •
          iteratedDeriv m (deriv f) x₀) t :=
      fun t => (hdf t).hasDerivAt.sub (hasDerivAt_taylorSum n f x₀ t)
    have hbound : ∀ t ∈ uIcc x₀ x, ‖deriv f t - ∑ m ∈ range n,
        ((m.factorial : ℝ)⁻¹ * (t - x₀) ^ m) • iteratedDeriv m (deriv f) x₀‖ ≤
          L * |x - x₀| ^ n := by
      intro t ht
      have h := norm_sub_taylor_le n hd x₀ t (L := L) fun t' ht' => by
        rw [← iteratedDeriv_succ']
        exact hL t' (uIcc_subset_uIcc_left ht ht')
      exact h.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_of_mem_uIcc ht) n) hL0)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hderiv t).hasDerivWithinAt) hbound (convex_uIcc x₀ x) left_mem_uIcc
      right_mem_uIcc
    have h0 : f x₀ - ∑ m ∈ range (n + 1), ((m.factorial : ℝ)⁻¹ * (x₀ - x₀) ^ m) •
        iteratedDeriv m f x₀ = 0 := by
      rw [sum_range_succ']
      simp
    rw [h0, sub_zero, Real.norm_eq_abs] at hmvt
    calc _ ≤ L * |x - x₀| ^ n * |x - x₀| := hmvt
      _ = L * |x - x₀| ^ (n + 1) := by ring

end

end PGM
