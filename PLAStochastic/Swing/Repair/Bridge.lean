import PLAStochastic.Swing.Repair.Chord
import Mathlib.Topology.Order.OrderClosed

/-!
# The bridge and a single completed repair cycle

The bridge joins consecutive true samples, so it equals the input interpolation
on that original grid edge. A completed cycle joins a true-endpoint chord to
this bridge. This module proves their junction, continuity, and a conditional
error bound for that pair; it does not define the streaming algorithm or prove
that a stream of output cycles covers every input sample.
-/

namespace SwingRepair

/-- On one original grid edge, the bridge is exactly its sample interpolation.
The identity even holds for barycentric coordinates outside the edge. -/
theorem bridge_eq_sample_interpolation {t₁ t₂ : ℝ} (h : t₁ < t₂)
    (y₁ y₂ θ : ℝ) :
    chord t₁ t₂ y₁ y₂ (blend t₁ t₂ θ) = blend y₁ y₂ θ := by
  rw [chord_blend, chord_left, chord_right h]

/-- Consequently the bridge has zero error against that single input edge. -/
theorem bridge_error_zero {t₁ t₂ : ℝ} (h : t₁ < t₂) (y₁ y₂ θ : ℝ) :
    |blend y₁ y₂ θ - chord t₁ t₂ y₁ y₂ (blend t₁ t₂ θ)| = 0 := by
  rw [bridge_eq_sample_interpolation h]
  simp

/-- The old chord and subsequent bridge meet at the same true sample. -/
theorem chord_bridge_junction {t₀ t₁ : ℝ} (h : t₀ < t₁)
    (t₂ y₀ y₁ y₂ : ℝ) :
    chord t₀ t₁ y₀ y₁ t₁ = chord t₁ t₂ y₁ y₂ t₁ := by
  rw [chord_right h, chord_left]

/-- A single chord followed by its bridge, extended affinely outside the cycle.
For a completed repair cycle, `t₁` is the last accepted sample and `t₂` is the
next, rejected sample. Those algorithmic roles are not inferred by this definition. -/
noncomputable def chordBridge (t₀ t₁ t₂ y₀ y₁ y₂ t : ℝ) : ℝ :=
  if t ≤ t₁ then chord t₀ t₁ y₀ y₁ t else chord t₁ t₂ y₁ y₂ t

theorem chordBridge_of_le {t₀ t₁ t₂ y₀ y₁ y₂ t : ℝ} (ht : t ≤ t₁) :
    chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t = chord t₀ t₁ y₀ y₁ t := by
  simp only [chordBridge, if_pos ht]

theorem chordBridge_of_ge {t₀ t₁ t₂ y₀ y₁ y₂ t : ℝ}
    (h : t₀ < t₁) (ht : t₁ ≤ t) :
    chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t = chord t₁ t₂ y₁ y₂ t := by
  by_cases hle : t ≤ t₁
  · have heq : t = t₁ := le_antisymm hle ht
    subst t
    rw [chordBridge_of_le le_rfl, chord_bridge_junction h]
  · simp only [chordBridge, if_neg hle]

/-- Matching true endpoints makes the piecewise function continuous globally. -/
theorem continuous_chordBridge {t₀ t₁ : ℝ} (h : t₀ < t₁)
    (t₂ y₀ y₁ y₂ : ℝ) :
    Continuous (chordBridge t₀ t₁ t₂ y₀ y₁ y₂) := by
  unfold chordBridge
  apply Continuous.if_le (continuous_chord t₀ t₁ y₀ y₁)
    (continuous_chord t₁ t₂ y₁ y₂) continuous_id continuous_const
  intro t ht
  change t = t₁ at ht
  subst t
  exact chord_bridge_junction h t₂ y₀ y₁ y₂

/-- A conditional error bound on a completed pair. `f` is the observed input
interpolation: its old-prefix chord bound is supplied separately, and its last
original grid edge is assumed to be the bridge through its true endpoints. -/
theorem chordBridge_error {t₀ t₁ t₂ y₀ y₁ y₂ ε : ℝ} {f : ℝ → ℝ}
    (hε : 0 ≤ ε)
    (hprefix : ∀ t ∈ Set.Icc t₀ t₁, |f t - chord t₀ t₁ y₀ y₁ t| ≤ ε)
    (hbridge : ∀ t ∈ Set.Icc t₁ t₂, f t = chord t₁ t₂ y₁ y₂ t) :
    ∀ t ∈ Set.Icc t₀ t₂, |f t - chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t| ≤ ε := by
  intro t ht
  by_cases hle : t ≤ t₁
  · rw [chordBridge_of_le hle]
    exact hprefix t ⟨ht.1, hle⟩
  · have hge : t₁ ≤ t := (lt_of_not_ge hle).le
    rw [chordBridge, if_neg hle, hbridge t ⟨hge, ht.2⟩]
    simpa using hε

/-- A nondegenerate completed pair is continuous, preserves all three true
knots, and inherits the prefix error bound while its bridge has zero error.
This specification concerns one pair, conditional on its supplied input pieces. -/
theorem chordBridge_spec {t₀ t₁ t₂ y₀ y₁ y₂ ε : ℝ} {f : ℝ → ℝ}
    (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂) (hε : 0 ≤ ε)
    (hprefix : ∀ t ∈ Set.Icc t₀ t₁, |f t - chord t₀ t₁ y₀ y₁ t| ≤ ε)
    (hbridge : ∀ t ∈ Set.Icc t₁ t₂, f t = chord t₁ t₂ y₁ y₂ t) :
    Continuous (chordBridge t₀ t₁ t₂ y₀ y₁ y₂) ∧
      chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t₀ = y₀ ∧
      chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t₁ = y₁ ∧
      chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t₂ = y₂ ∧
      ∀ t ∈ Set.Icc t₀ t₂, |f t - chordBridge t₀ t₁ t₂ y₀ y₁ y₂ t| ≤ ε := by
  refine ⟨continuous_chordBridge h₀₁ t₂ y₀ y₁ y₂, ?_, ?_, ?_,
    chordBridge_error hε hprefix hbridge⟩
  · rw [chordBridge_of_le h₀₁.le, chord_left]
  · rw [chordBridge_of_le le_rfl, chord_right h₀₁]
  · rw [chordBridge_of_ge h₀₁ h₁₂.le, chord_right h₁₂]

end SwingRepair
