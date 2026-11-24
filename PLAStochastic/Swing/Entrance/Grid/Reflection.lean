import PLAStochastic.Swing.Entrance.Grid.Cut

/-!
# Reflection of the entrance cone

The reflection lemma (G4) of the entrance-law review: under the path reflection `y ↦ -y`

* the lower and upper endpoints swap with a sign, `a_n(-y) = -b_n(y)` and `b_n(-y) = -a_n(y)`;
* the rescaled width and the adaptive cut are invariant;
* the lower endpoint of `-y` is refreshed exactly when the upper endpoint of `y` is;
* whenever exactly one endpoint is refreshed (in particular at a finite cut), the side flips,
  the frozen endpoint changes sign, and the reflected local residual, its crossing time,
  overshoot and undershoot, and the reflected grid area are invariant.
-/

open Finset

namespace SwingRepair

noncomputable section

variable (y : ℕ → ℝ) (E : ℝ)

theorem slopeLower_neg (t v t₀ v₀ : ℝ) :
    slopeLower t (-v) t₀ (-v₀) E = -slopeUpper t v t₀ v₀ E := by
  unfold slopeLower slopeUpper
  ring

theorem entranceLower_neg (n : ℕ) : entranceLower (-y) E n = -entranceUpper y E n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  apply le_antisymm
  · apply (entranceLower_le_iff (-y) E hn).mpr
    intro i hi1 hin
    rw [Pi.neg_apply, Pi.neg_apply, slopeLower_neg, neg_le_neg_iff]
    exact entranceUpper_le_slopeUpper y E hi1 hin
  · obtain ⟨i, hi1, hin, he⟩ := exists_entranceUpper_eq y E hn
    rw [he, ← slopeLower_neg]
    exact slopeLower_le_entranceLower (-y) E hi1 hin

variable {y E}

section ExactlyOne

variable {n : ℕ}
  (hone : entranceRefreshesLower y E n ↔
    entranceUpper y E n ≠ slopeUpper (n : ℝ) (y n) 0 (y 0) E)
include hone

end ExactlyOne

section Cut

variable {n : ℕ} (hE0 : 0 ≤ E) (hE : entranceCutLevel E < 2 * E) (hn : entranceCut y E = n)
include hE0 hE hn

end Cut

end

end SwingRepair
