import PLAStochastic.Index.KEP.ReferenceScale.GraphTransfer

/-!
# Positive physical numerators and pin updates

Positive gap support forces every nonzero fixed bridge to have strictly
positive physical numerator. Thus a new exterior pin cannot decrease the
fixed numerator `D`. The graph output is unchanged by the exact length and
endpoint update, including a zero-step remaining tail.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepGapNumerator (σ : ℝ) (n : ℕ) (x y : ℝ) : ℝ := (n : ℝ) + σ * (x - y)

theorem kepGapNumerator_add (σ : ℝ) (m n : ℕ) (x y z : ℝ) :
    kepGapNumerator σ (m + n) x z =
      kepGapNumerator σ m x y + kepGapNumerator σ n y z := by
  simp only [kepGapNumerator, Nat.cast_add]
  ring

theorem kepLogStep_eq_zero_of_numerator_nonpos {f : ℝ → ℝ}
    (hf : ∀ x, x ≤ 0 → f x = 0) {σ s x y : ℝ}
    (h : kepGapNumerator σ 1 x y ≤ 0) : kepLogStep f σ s (y - x) = 0 := by
  unfold kepLogStep
  have hn : 1 - σ * (y - x) ≤ 0 := by
    dsimp [kepGapNumerator] at h
    norm_num only [Nat.cast_one] at h
    nlinarith
  rw [hf _ (mul_nonpos_of_nonpos_of_nonneg hn (Real.exp_pos _).le), zero_mul]

theorem kepFixedBridge_eq_zero_of_numerator_nonpos {f : ℝ → ℝ}
    (hf : ∀ x, x ≤ 0 → f x = 0) (w σ s : ℝ) (n : ℕ) (x y : ℝ)
    (h : kepGapNumerator σ (n + 1) x y ≤ 0) :
    kepFixedBridge (kepLogStep f σ) w s n x y = 0 := by
  induction n generalizing x y with
  | zero => exact kepLogStep_eq_zero_of_numerator_nonpos hf h
  | succ n ih =>
    rw [kepFixedBridge]
    apply integral_eq_zero_of_ae
    exact ae_of_all _ fun z => by
      dsimp only
      change _ = (0 : ℝ)
      by_cases hz : kepGapNumerator σ (n + 1) x z ≤ 0
      · rw [ih x z hz, zero_mul]
      · have hlast : kepGapNumerator σ 1 z y ≤ 0 := by
          have hs := kepGapNumerator_add σ (n + 1) 1 x z y
          linarith
        rw [kepLogStep_eq_zero_of_numerator_nonpos hf hlast, mul_zero]

theorem kepFixedBridge_numerator_pos_of_ne_zero {f : ℝ → ℝ}
    (hf : ∀ x, x ≤ 0 → f x = 0) (w σ s : ℝ) (n : ℕ) (x y : ℝ)
    (h : kepFixedBridge (kepLogStep f σ) w s n x y ≠ 0) :
    0 < kepGapNumerator σ (n + 1) x y := by
  by_contra hn
  exact h (kepFixedBridge_eq_zero_of_numerator_nonpos hf w σ s n x y (le_of_not_gt hn))

/-- The real reference density supplies positive support without a new input. -/
theorem kepReference_bridge_numerator_pos {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j)
    (w σ s : ℝ) (n : ℕ) (x y : ℝ)
    (h : kepFixedBridge (kepLogStep (kepReferenceDensity heps hj).density σ)
      w s n x y ≠ 0) :
    0 < kepGapNumerator σ (n + 1) x y :=
  kepFixedBridge_numerator_pos_of_ne_zero
    (kepReferenceDensity_classical heps hj).1 w σ s n x y h

theorem kepGraphOutput_left_pin (D : ℝ) (i r l : ℕ) (hl : l ≤ i)
    (xA xB b s u v : ℝ) :
    kepGraphOutput (D + kepGapNumerator (-1) l xA b) (i - l) r b xB s u v =
      kepGraphOutput D i r xA xB s u v := by
  have hlen : ((i - l : ℕ) : ℝ) + (l : ℝ) = i := by
    exact_mod_cast Nat.sub_add_cancel hl
  unfold kepGraphOutput kepGapNumerator
  linear_combination Real.exp (-s) * hlen

theorem kepGraphOutput_right_pin (D : ℝ) (i r l : ℕ) (hl : l ≤ r)
    (xA xB b s u v : ℝ) :
    kepGraphOutput (D + kepGapNumerator 1 l xB b) i (r - l) xA b s u v =
      kepGraphOutput D i r xA xB s u v := by
  have hlen : ((r - l : ℕ) : ℝ) + (l : ℝ) = r := by
    exact_mod_cast Nat.sub_add_cancel hl
  unfold kepGraphOutput kepGapNumerator
  linear_combination Real.exp (-s) * hlen

theorem kepGraph_pin_numerator_mono {D d : ℝ} (hd : 0 ≤ d) : D ≤ D + d := by linarith

end

end PGM
