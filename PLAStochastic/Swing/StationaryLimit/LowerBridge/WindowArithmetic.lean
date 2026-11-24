import PLAStochastic.Swing.StationaryLimit.LowerBridge.AffineOriginal

/-!
# Explicit natural passage-window indices

The pathwise bridge theorems accept arbitrary window endpoints.  This file
chooses them by ceilings and records exactly the scalar condition needed for
the lower endpoint.  It is deliberately independent of probability.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem exists_affine_passage_window_indices
    {a q b H D : ℝ}
    (hq : 0 ≤ q) (hqa : q < a) (_hD : 0 ≤ D)
    (hx : 0 < (3 * D / (a - q) - 1) / 2)
    (hLscalar :
      (a + q) * ((3 * D / (a - q) - 1) / 2 + 1) + H ≤ b) :
    ∃ L U : ℕ,
      1 ≤ L ∧
      3 * D ≤ (a - q) * (2 * (L : ℝ) + 1) ∧
      (a + q) * (L : ℝ) + H ≤ b ∧
      b < (a - q) * (U : ℝ) - H := by
  have hpos : 0 < a - q := sub_pos.mpr hqa
  let L : ℕ := ⌈(3 * D / (a - q) - 1) / 2⌉₊
  let U : ℕ := ⌈(b + H) / (a - q)⌉₊ + 1
  have hLpos : 1 ≤ L := by
    dsimp [L]
    exact Nat.one_le_ceil_iff.mpr hx
  have hx0 : 0 ≤ (3 * D / (a - q) - 1) / 2 := le_of_lt hx
  have hLupper : (L : ℝ) < (3 * D / (a - q) - 1) / 2 + 1 := by
    dsimp [L]
    exact Nat.ceil_lt_add_one hx0
  have hLlower : (3 * D / (a - q) - 1) / 2 ≤ (L : ℝ) := by
    dsimp [L]
    exact Nat.le_ceil _
  have hcoef : 0 ≤ a + q := by linarith
  have hLwindow : (a + q) * (L : ℝ) + H ≤ b := by
    have hm := mul_le_mul_of_nonneg_left hLupper.le hcoef
    linarith
  have hselector_div : 3 * D / (a - q) ≤ 2 * (L : ℝ) + 1 := by
    nlinarith [hLlower]
  have hselector : 3 * D ≤ (a - q) * (2 * (L : ℝ) + 1) := by
    simpa [mul_comm] using (div_le_iff₀ hpos).mp hselector_div
  have hUlower : (b + H) / (a - q) ≤ (⌈(b + H) / (a - q)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hUstrict : (b + H) / (a - q) < (U : ℝ) := by
    dsimp [U]
    push_cast
    linarith
  have hUwindow : b < (a - q) * (U : ℝ) - H := by
    have hm := (div_lt_iff₀ hpos).mp hUstrict
    linarith
  exact ⟨L, U, hLpos, hselector, hLwindow, hUwindow⟩

/-! The ceiling choice plugged directly into the affine pathwise bridge. -/
theorem prefixCrossingLowerBridgeEventRandom_of_affine_original_envelope_of_ceil_window
    {Ω : Type*} {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) (hE : 0 ≤ E)
    {K δ M C q : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hME : M ≤ E) (hr : |r| ≤ K)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J - 1))
    (hC : 0 ≤ C) (hq : 0 ≤ q) (hqδ : q < δ)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hstrict : M * (J : ℝ) + K + C + q * (J : ℝ) < 2 * E)
    (hD : 0 ≤ E - r + C + q * (J : ℝ))
    (hx : 0 <
      (3 * (E - r + C + q * (J : ℝ)) /
        (prefixCrossingSlope X r J ω - q) - 1) / 2)
    (hLscalar :
      (prefixCrossingSlope X r J ω + q) *
          ((3 * (E - r + C + q * (J : ℝ)) /
            (prefixCrossingSlope X r J ω - q) - 1) / 2 + 1) +
        (2 * C + 2 * q * (J : ℝ) + q) ≤
      prefixCrossingLevel X E r J ω) :
    ω ∈ prefixCrossingLowerBridgeEventRandom X E r J := by
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M) ω hJ hδ hgood hr
  have ha_lower : δ ≤ prefixCrossingSlope X r J ω := hbounds.1
  have haE0 : prefixCrossingSlope X r J ω ≤ M := hbounds.2
  have hqa : q < prefixCrossingSlope X r J ω := lt_of_lt_of_le hqδ ha_lower
  obtain ⟨L, U, hLpos, hselector, hwindowL, hwindowU⟩ :=
    exists_affine_passage_window_indices
      (a := prefixCrossingSlope X r J ω) (q := q)
      (b := prefixCrossingLevel X E r J ω)
      (H := 2 * C + 2 * q * (J : ℝ) + q)
      (D := E - r + C + q * (J : ℝ))
      hq hqa hD hx hLscalar
  exact prefixCrossingLowerBridgeEventRandom_of_affine_original_envelope
    (X := X) E r J ω hJ hE hK hδ hM hME hr hgood hC hq hqδ hW hstrict
    hLpos
    (by simpa [add_assoc, add_left_comm, add_comm] using hwindowL)
    (by simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hwindowU)
    (by simpa [add_assoc, add_left_comm, add_comm] using hselector)

end SwingRepair
