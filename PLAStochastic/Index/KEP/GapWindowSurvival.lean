import PLAStochastic.Index.Model.IIDGaps

/-!
# Every surviving gap prefix contains surviving consecutive windows

The statement is deterministic and applies to the original greedy stopping
rule. The window uses its own origin and the same rank tolerance.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

theorem gapSegLen_window_survival {eps : ℝ} {g : ℕ → ℝ} {a w : ℕ}
    (h : ((a + w : ℕ) : ℕ∞) < gapSegLen eps g) :
    (w : ℕ∞) < gapSegLen eps (fun k => g (a + k)) := by
  rw [gapSegLen, lt_segLen_iff] at h ⊢
  have hwin := prefixAffineFeasible_window h (r := a) (w := w + 1) (by omega)
  have he : (fun k => gapKeys g (a + k)) =
      fun k => 1 * gapKeys (fun t => g (a + t)) k + gapKeys g a := by
    funext k
    rw [gapKeys_shift]
    ring
  rw [he, prefixAffineFeasible_affine_iff one_ne_zero] at hwin
  exact hwin

end

end PGM
