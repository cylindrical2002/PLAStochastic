import PLAStochastic.Swing.Algorithm.FeasibleSlope
import PLAStochastic.Swing.Repair.Chord

/-!
# An accepted finite prefix

The interval here is precisely the half-budget cone in the repair rule.
Theorems cover every original sampling edge of a nontrivial accepted prefix.
The streaming algorithm's production of such prefixes is a separate obligation.
-/

namespace SwingRepair

/-- The half-budget slope cone after samples s+1,...,e have been accepted. -/
def prefixCone (t y : ℕ → ℝ) (s e : ℕ) (ε : ℝ) : Set ℝ :=
  {m | ∀ j ∈ Finset.Icc (s + 1) e,
    m ∈ Set.Icc (slopeLower (t j) (y j) (t s) (y s) (ε / 2))
      (slopeUpper (t j) (y j) (t s) (y s) (ε / 2))}

/-- Cone membership includes the anchor's zero residual as well as every accepted sample. -/
theorem prefix_line_error {t y : ℕ → ℝ} {s e j : ℕ} {ε m : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (hm : m ∈ prefixCone t y s e ε)
    (hsj : s ≤ j) (hje : j ≤ e) :
    |y j - line (t s) (y s) m (t j)| ≤ ε / 2 := by
  rcases eq_or_lt_of_le hsj with rfl | hsj
  · simp [line]
    linarith
  · have hj : j ∈ Finset.Icc (s + 1) e :=
      Finset.mem_Icc.mpr ⟨hsj, hje⟩
    exact (sample_error_iff_bounds (ht hsj)).mpr (hm j hj)

/-- Every sample of an accepted prefix is within the full budget of its endpoint chord. -/
theorem prefix_chord_sample_error {t y : ℕ → ℝ} {s e j : ℕ} {ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (hse : s < e)
    (hne : (prefixCone t y s e ε).Nonempty)
    (hsj : s ≤ j) (hje : j ≤ e) :
    |y j - chord (t s) (t e) (y s) (y e) (t j)| ≤ ε := by
  obtain ⟨m, hm⟩ := hne
  exact chord_sample_error (ht hse) (ht.monotone hsj) (ht.monotone hje)
    (prefix_line_error ht hε hm hse.le le_rfl)
    (prefix_line_error ht hε hm hsj hje)

/-- The repair bound holds on every original interpolation edge, including the first. -/
theorem prefix_chord_interpolation_error {t y : ℕ → ℝ} {s e i : ℕ} {θ ε : ℝ}
    (ht : StrictMono t) (hε : 0 ≤ ε) (hse : s < e)
    (hne : (prefixCone t y s e ε).Nonempty)
    (hsi : s ≤ i) (hie : i < e) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1) :
    |blend (y i) (y (i + 1)) θ -
      chord (t s) (t e) (y s) (y e) (blend (t i) (t (i + 1)) θ)| ≤ ε := by
  exact chord_edge_error hθ₀ hθ₁
    (prefix_chord_sample_error ht hε hse hne hsi hie.le)
    (prefix_chord_sample_error ht hε hse hne (le_trans hsi (Nat.le_succ i)) hie)

end SwingRepair
