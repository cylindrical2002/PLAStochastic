import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Finite Taylor remainders on an open complex disc -/

noncomputable section
open Complex Set Metric Finset
namespace PGM

def complexTaylorSum (f : ℂ → ℂ) (n : ℕ) (c z : ℂ) : ℂ :=
  ∑ m ∈ range n, (m.factorial : ℂ)⁻¹ * (z - c) ^ m * iteratedDeriv m f c

theorem hasDerivAt_complexTaylorSum (n : ℕ) (f : ℂ → ℂ) (c z : ℂ) :
    HasDerivAt (complexTaylorSum f (n + 1) c) (complexTaylorSum (deriv f) n c z) z := by
  have hp : ∀ m ∈ range (n + 1), HasDerivAt
      (fun w : ℂ => (m.factorial : ℂ)⁻¹ * (w - c) ^ m * iteratedDeriv m f c)
      ((m.factorial : ℂ)⁻¹ * ((m : ℂ) * (z - c) ^ (m - 1)) * iteratedDeriv m f c) z := by
    intro m _
    have h1 := (((hasDerivAt_id' z).sub_const c).pow m).const_mul (m.factorial : ℂ)⁻¹
    simpa only [mul_one] using! h1.mul_const (iteratedDeriv m f c)
  refine (HasDerivAt.fun_sum hp).congr_deriv ?_
  unfold complexTaylorSum
  rw [sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine sum_congr rfl fun m _ => ?_
  rw [iteratedDeriv_succ', Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

theorem complexTaylorSum_center (f : ℂ → ℂ) (n : ℕ) (c : ℂ) :
    complexTaylorSum f (n + 1) c c = f c := by
  unfold complexTaylorSum
  rw [sum_range_succ']
  simp

theorem norm_sub_complexTaylorSum_le_derivative_bound : ∀ (n : ℕ) {f : ℂ → ℂ} {c : ℂ}
    {R L : ℝ}, 0 < R → DifferentiableOn ℂ f (ball c R) →
    (∀ w ∈ ball c R, ‖iteratedDeriv n f w‖ ≤ L) → ∀ z ∈ ball c R,
    ‖f z - complexTaylorSum f n c z‖ ≤ L * ‖z - c‖ ^ n
  | 0, f, c, R, L, _, _, hb, z, hz => by
      simpa [complexTaylorSum] using hb z hz
  | n + 1, f, c, R, L, hR, hf, hb, z, hz => by
      have hc : c ∈ ball c R := mem_ball_self hR
      have hL : 0 ≤ L := (norm_nonneg _).trans (hb c hc)
      have hd : DifferentiableOn ℂ (deriv f) (ball c R) := hf.deriv isOpen_ball
      have hderiv : ∀ w ∈ ball c R, HasDerivAt
          (fun w => f w - complexTaylorSum f (n + 1) c w)
          (deriv f w - complexTaylorSum (deriv f) n c w) w := fun w hw =>
        ((hf w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.sub
          (hasDerivAt_complexTaylorSum n f c w)
      have hbound : ∀ w ∈ segment ℝ c z,
          ‖deriv f w - complexTaylorSum (deriv f) n c w‖ ≤ L * ‖z - c‖ ^ n := by
        intro w hw
        have hwR := (convex_ball c R).segment_subset hc hz hw
        have ht := norm_sub_complexTaylorSum_le_derivative_bound n hR hd
          (fun t ht => by rw [← iteratedDeriv_succ']; exact hb t ht) w hwR
        apply ht.trans
        gcongr
        rw [segment_eq_image'] at hw
        obtain ⟨t, hseg, rfl⟩ := hw
        simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        rw [abs_of_nonneg hseg.1]
        exact mul_le_of_le_one_left (norm_nonneg _) hseg.2
      have hm := (convex_segment c z).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun w hw => (hderiv w ((convex_ball c R).segment_subset hc hz hw)).hasDerivWithinAt)
        hbound (left_mem_segment ℝ c z) (right_mem_segment ℝ c z)
      rw [complexTaylorSum_center, sub_self, sub_zero] at hm
      exact hm.trans_eq (by ring)

theorem norm_sub_complexTaylorSum_le_of_ball {f : ℂ → ℂ} {c : ℂ} {R M : ℝ}
    (n : ℕ) (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ w ∈ ball c R, ‖f w‖ ≤ M) {z : ℂ} (hz : z ∈ ball c (R / 2)) :
    ‖f z - complexTaylorSum f n c z‖ ≤
      ((n.factorial : ℝ) * M / (R / 4) ^ n) * ‖z - c‖ ^ n := by
  exact norm_sub_complexTaylorSum_le_derivative_bound n (half_pos hR)
    (hf.mono (ball_subset_ball (half_le_self hR.le)))
    (fun w hw => norm_iteratedDeriv_le_of_ball_half n hR hf hb hw) z hz

end PGM
