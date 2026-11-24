import PLAStochastic.Swing.Ladder.Renewal.RecordValues
import Mathlib.Tactic

/-!
# Deterministic first-passage windows

These lemmas isolate the pathwise part of the distant-crossing argument.  They
use no probability: a linear envelope for the centered walk gives explicit
lower and upper indices for the first passage.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- If the drift walk is at most the level through `n`, the first strict
crossing occurs after `n`. -/
theorem gaussianWalkPassage_gt_of_prefix_le
    {Y : ℕ → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hcross : ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω)
    {n : ℕ}
    (hbelow : ∀ j ≤ n, gaussianDriftWalk Y 0 a j ω ≤ b) :
    n < gaussianWalkPassage Y a b ω := by
  rw [gaussianWalkPassage, dif_pos hcross]
  by_contra hnot
  have hle : Nat.find hcross ≤ n := Nat.le_of_not_gt hnot
  have hspec := Nat.find_spec hcross
  have hbound := hbelow (Nat.find hcross) hle
  linarith

omit mΩ in
/-- If the walk is already strictly above the level at `n`, the first passage
is no later than `n`. -/
theorem gaussianWalkPassage_le_of_crossing
    {Y : ℕ → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hcross : ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω)
    {n : ℕ}
    (hn : b < gaussianDriftWalk Y 0 a n ω) :
    gaussianWalkPassage Y a b ω ≤ n := by
  rw [gaussianWalkPassage, dif_pos hcross]
  exact Nat.find_le hn

omit mΩ in
/-- A global linear envelope yields a deterministic first-passage window.  The
numbers `L,U` are arbitrary natural indices satisfying the displayed linear
inequalities; this keeps the statement independent of a choice of floors or
ceilings. -/
theorem gaussianWalkPassage_window_of_linear_envelope
    {Y : ℕ → Ω → ℝ} {a b η : ℝ} {ω : Ω}
    (ha : 0 ≤ a) (hη : 0 ≤ η) (hηa : η < a)
    (henv : ∀ n : ℕ,
      |cumulativeSamples Y n ω| ≤ η * ((n : ℝ) + 1))
    {L U : ℕ}
    (hL : (a + η) * (L : ℝ) + η ≤ b)
    (hU : b < (a - η) * (U : ℝ) - η) :
    (∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω) ∧
      L < gaussianWalkPassage Y a b ω ∧
        gaussianWalkPassage Y a b ω ≤ U := by
  have hcross : ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω := by
    refine ⟨U, ?_⟩
    have henvU := henv U
    have hlow : -η * ((U : ℝ) + 1) ≤ cumulativeSamples Y U ω := by
      have habs := neg_le_abs (cumulativeSamples Y U ω)
      linarith
    dsimp [gaussianDriftWalk]
    linarith

  have hbelow : ∀ j ≤ L, gaussianDriftWalk Y 0 a j ω ≤ b := by
    intro j hj
    have henvj := henv j
    have hupp : cumulativeSamples Y j ω ≤ η * ((j : ℝ) + 1) :=
      (le_abs_self _).trans henvj
    have hjcast : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hj
    dsimp [gaussianDriftWalk]
    have hcoef : 0 ≤ a + η := by linarith
    nlinarith
  refine ⟨hcross, ?_, ?_⟩
  · exact gaussianWalkPassage_gt_of_prefix_le hcross hbelow
  · apply gaussianWalkPassage_le_of_crossing hcross
    have henvU := henv U
    have hlow : -η * ((U : ℝ) + 1) ≤ cumulativeSamples Y U ω := by
      have habs := neg_le_abs (cumulativeSamples Y U ω)
      linarith
    dsimp [gaussianDriftWalk]
    linarith

omit mΩ in
/-- Under the same envelope and `η<a`, a crossing exists at an explicit
natural index chosen above `(b+η)/(a-η)`. -/
theorem gaussianWalkPassage_exists_of_linear_envelope
    {Y : ℕ → Ω → ℝ} {a b η : ℝ} {ω : Ω}
    (_ha : 0 ≤ a) (_hη : 0 ≤ η) (hηa : η < a)
    (henv : ∀ n : ℕ,
      |cumulativeSamples Y n ω| ≤ η * ((n : ℝ) + 1)) :
    ∃ m : ℕ, b < gaussianDriftWalk Y 0 a m ω := by
  have hpos : 0 < a - η := sub_pos.mpr hηa
  obtain ⟨U, hU⟩ := exists_nat_gt ((b + η) / (a - η))
  refine ⟨U, ?_⟩
  have henvU := henv U
  have hlow : -η * ((U : ℝ) + 1) ≤ cumulativeSamples Y U ω := by
    have habs := neg_le_abs (cumulativeSamples Y U ω)
    linarith
  dsimp [gaussianDriftWalk]
  have hcast : (b + η) / (a - η) < (U : ℝ) := by
    exact_mod_cast hU
  have hmul' := (div_lt_iff₀ hpos).mp hcast
  have hmul : b + η < (a - η) * (U : ℝ) := by
    nlinarith [hmul']
  linarith

end SwingRepair
