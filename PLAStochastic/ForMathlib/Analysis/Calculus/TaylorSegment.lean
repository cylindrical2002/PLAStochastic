import PLAStochastic.ForMathlib.Analysis.Calculus.TaylorBound

/-! # Taylor remainders using derivatives only on the required segment -/

noncomputable section
open Set Finset
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realTaylorSum (f : ℝ → E) (n : ℕ) (c x : ℝ) : E :=
  ∑ m ∈ range n, ((m.factorial : ℝ)⁻¹ * (x - c) ^ m) • iteratedDeriv m f c

theorem realTaylorSum_center (f : ℝ → E) (n : ℕ) (c : ℝ) :
    realTaylorSum f (n + 1) c c = f c := by
  unfold realTaylorSum
  rw [sum_range_succ']
  simp

/-- No regularity away from the segment is required. -/
theorem norm_sub_realTaylorSum_le : ∀ (n : ℕ) {f : ℝ → E} {c x L : ℝ},
    (∀ k < n, ∀ t ∈ uIcc c x,
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f t) t) →
    (∀ t ∈ uIcc c x, ‖iteratedDeriv n f t‖ ≤ L) →
    ‖f x - realTaylorSum f n c x‖ ≤ L * |x - c| ^ n
  | 0, f, c, x, L, _, hb => by
      simpa [realTaylorSum] using hb x right_mem_uIcc
  | n + 1, f, c, x, L, hd, hb => by
      have hL : 0 ≤ L := (norm_nonneg _).trans (hb x right_mem_uIcc)
      have hderiv : ∀ t ∈ uIcc c x, HasDerivAt
          (fun s => f s - realTaylorSum f (n + 1) c s)
          (deriv f t - realTaylorSum (deriv f) n c t) t := by
        intro t ht
        have hf := hd 0 (by omega) t ht
        simp only [Nat.zero_add, iteratedDeriv_zero, iteratedDeriv_one] at hf
        exact hf.sub (hasDerivAt_taylorSum n f c t)
      have hbound : ∀ t ∈ uIcc c x,
          ‖deriv f t - realTaylorSum (deriv f) n c t‖ ≤ L * |x - c| ^ n := by
        intro t ht
        have h := norm_sub_realTaylorSum_le n (f := deriv f) (c := c) (x := t)
          (fun k hk t' ht' => by
            simp only [← iteratedDeriv_succ']
            exact hd (k + 1) (by omega) t' (uIcc_subset_uIcc_left ht ht'))
          (fun t' ht' => by
            rw [← iteratedDeriv_succ']
            exact hb t' (uIcc_subset_uIcc_left ht ht'))
        exact h.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_left_of_mem_uIcc ht) n) hL)
      have hm := (convex_uIcc c x).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound left_mem_uIcc right_mem_uIcc
      rw [realTaylorSum_center, sub_self, sub_zero, Real.norm_eq_abs] at hm
      exact hm.trans_eq (by ring)

end PGM
