import PLAStochastic.Swing.Ladder.Renewal.PostPassageSplit
import PLAStochastic.Swing.Ladder.Law.UniformBounds
import PLAStochastic.Swing.Ladder.Renewal.OvershootIdentity

/-!
# Position-uniform renewal window bounds for the actual ladder law

`LadderPostPassage` proves, for an abstract i.i.d. sequence, that the expected
number of partial sums inside a window is at most the expected number inside
`Iic` of its length.  Instantiating at the actual Gaussian ladder heights turns
the project's `Icc 0 b` Laplace bound — whose constant grows with `b` — into a
bound that is uniform in the position of the window.

Everything here is unconditional: no renewal expansion and no contour
certificate is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The ladder renewal measure of the actual walk charges no negative set. -/
theorem ladderRenewalMeasure_Iio_zero [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Iio (0 : ℝ)) = 0 := by
  rw [ladderRenewalMeasure_eq_tsum_ladderSum hX hi hG ha measurableSet_Iio]
  have hzero : ∀ n : ℕ, μ {ω | gaussianLadderSum X a n ω ∈ Iio (0 : ℝ)} = 0 := by
    intro n
    have hempty : {ω | gaussianLadderSum X a n ω ∈ Iio (0 : ℝ)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_empty_iff_false, iff_false, not_lt]
      exact gaussianLadderSum_nonneg X a n ω
    rw [hempty, measure_empty]
  simp only [hzero, tsum_zero]

/-- The renewal mass of `Iic w` is carried by `Icc 0 w`. -/
theorem ladderRenewalMeasure_Iic_le_Icc [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (w : ℝ) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Iic w) ≤
      ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 w) := by
  set U := ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) with hU
  have hsub : Iic w ⊆ Icc (0 : ℝ) w ∪ Iio 0 := by
    intro x hx
    rcases le_or_gt 0 x with h | h
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr h
  calc U (Iic w) ≤ U (Icc 0 w ∪ Iio 0) := measure_mono hsub
    _ ≤ U (Icc 0 w) + U (Iio 0) := measure_union_le _ _
    _ = U (Icc 0 w) := by
        rw [ladderRenewalMeasure_Iio_zero hX hi hG ha, add_zero]

/-- **The position-uniform window bound.**  For every real position `c` and
every window length `w ≥ 0` the renewal mass of `Ioc c (c+w)` is at most the
renewal mass of `Icc 0 w`. -/
theorem ladderRenewalMeasure_Ioc_le_Icc [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a)
    (c : ℝ) {w : ℝ} (_hw : 0 ≤ w) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Ioc c (c + w)) ≤
      ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Icc 0 w) := by
  set U := ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) with hU
  rcases le_or_gt 0 c with hc | hc
  · -- the strong-Markov step
    have hmain : (∑' n : ℕ,
        μ {ω | renewalSum (gaussianLadderHeightAt X a) n ω ∈ Ioc c (c + w)}) ≤
        ∑' j : ℕ, measureConvPow (gaussianAscendingLadderLaw X μ a) j (Iic w) :=
      tsum_measure_renewalSum_Ioc_le
        (H := gaussianLadderHeightAt X a)
        (ν := gaussianAscendingLadderLaw X μ a)
        (gaussianLadderHeightAt_measurable hX a)
        (gaussianLadderHeights_iIndepFun hX hi hG ha)
        (gaussianLadderHeightAt_map hX hi hG ha) hc
    have hleft : U (Ioc c (c + w)) =
        ∑' n : ℕ, μ {ω | renewalSum (gaussianLadderHeightAt X a) n ω ∈ Ioc c (c + w)} := by
      rw [hU, ladderRenewalMeasure_eq_tsum_ladderSum hX hi hG ha measurableSet_Ioc]
      rfl
    have hright : (∑' j : ℕ,
        measureConvPow (gaussianAscendingLadderLaw X μ a) j (Iic w)) = U (Iic w) := by
      rw [hU, ladderRenewalMeasure_apply _ measurableSet_Iic]
    rw [hleft]
    exact le_trans hmain (by
      rw [hright]
      exact ladderRenewalMeasure_Iic_le_Icc hX hi hG ha w)
  · -- a window that starts below the origin is inside `Icc 0 w`
    have hsub : Ioc c (c + w) ⊆ Icc (0 : ℝ) w ∪ Iio 0 := by
      intro x hx
      rcases le_or_gt 0 x with h | h
      · exact Or.inl ⟨h, le_trans hx.2 (by linarith)⟩
      · exact Or.inr h
    calc U (Ioc c (c + w)) ≤ U (Icc 0 w ∪ Iio 0) := measure_mono hsub
      _ ≤ U (Icc 0 w) + U (Iio 0) := measure_union_le _ _
      _ = U (Icc 0 w) := by
          rw [ladderRenewalMeasure_Iio_zero hX hi hG ha, add_zero]

/-- The explicit position-uniform constant: the window bound composed with the
project's Laplace estimate at the origin.  The constant depends only on the
window length and on the common minorization scale of the drift interval. -/
theorem ladderRenewalMeasure_Ioc_le_const [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {M a : ℝ} (ha : 0 < a) (haM : a ≤ M) (c : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    ladderRenewalMeasure (gaussianAscendingLadderLaw X μ a) (Ioc c (c + w)) ≤
      ENNReal.ofReal (2 * Real.exp 1 * (1 + w) /
        gaussianAscendingLadderCommonDensity M) :=
  le_trans (ladderRenewalMeasure_Ioc_le_Icc hX hi hG ha c hw)
    (gaussianAscendingLadderRenewal_Icc_le hX hi hG ha haM hw)

end SwingRepair
