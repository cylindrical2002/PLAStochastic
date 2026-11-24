import PLAStochastic.Swing.Gaussian.ZeroLadder.PrefixMoments
import PLAStochastic.Swing.Gaussian.Tail.QuadraticDrift

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option maxHeartbeats 1000000

/-- At a path with distinct partial sums, the unique minimum partitions the path
into the two strict-positive pieces used by the ladder convolution. -/
theorem ladder_piece_partition_pointwise
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hd : Function.Injective (fun j => cumulativeSamples X j ω)) :
    (∑ k ∈ Finset.range (n+1),
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0)) = 1 := by
  obtain ⟨k, hk⟩ := exists_ladderMinimumAt (fun j => cumulativeSamples X j ω) n
    (fun i hi j hj hij => hd.ne hij)
  have hp : ∀ j, j ≤ n →
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X j) j then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun l => X (j+l)) (n-j) then 1 else 0) =
      if ladderMinimumAt (fun l => cumulativeSamples X l ω) n j then 1 else 0 := by
    intro j hj
    by_cases hm : ladderMinimumAt (fun l => cumulativeSamples X l ω) n j
    · have hpieces := (ladderMinimumAt_iff_positive_pieces X n j hj ω).mp hm
      simp [hpieces.1, hpieces.2, hm]
    · have hn : ¬ (ω ∈ ladderPositivePrefix (ladderReverseNeg X j) j ∧
          ω ∈ ladderPositivePrefix (fun l => X (j+l)) (n-j)) := by
        intro hh; exact hm ((ladderMinimumAt_iff_positive_pieces X n j hj ω).mpr hh)
      simp only [hm, if_false, mul_eq_zero]
      by_cases h1 : ω ∈ ladderPositivePrefix (ladderReverseNeg X j) j <;>
        by_cases h2 : ω ∈ ladderPositivePrefix (fun l => X (j+l)) (n-j) <;>
        simp [h1, h2] at hn ⊢
  rw [Finset.sum_eq_single k]
  · simp [hp k hk.1, hk]
  · intro j hj hjk
    have hnone : ¬ ladderMinimumAt (fun l => cumulativeSamples X l ω) n j := by
      intro hjm
      exact hjk (ladderMinimumAt_unique hjm hk)
    rw [hp j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    simp [hnone]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk.1))).elim

end SwingRepair

namespace SwingRepair
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussian_ladder_survival_convolution
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), gaussianLadderSurvivalProbability X μ k *
      gaussianLadderSurvivalProbability X μ (n-k)) = 1 := by
  let := hi.isProbabilityMeasure
  have hpoint : ∀ᵐ ω ∂μ,
      (∑ k ∈ Finset.range (n+1),
        (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
        (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0)) = 1 := by
    filter_upwards [cumulativeSamples_distinct_ae hX hi hG] with ω hd
    exact ladder_piece_partition_pointwise X n ω hd
  have hInt : (∫ ω, (∑ k ∈ Finset.range (n+1),
        (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
        (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0)) ∂μ) = 1 := by
    rw [integral_congr_ae hpoint, integral_const, measureReal_def, measure_univ,
      ENNReal.toReal_one, smul_eq_mul, mul_one]
  have hterms : ∀ k ∈ Finset.range (n+1),
      (∫ ω, (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
        (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) ∂μ) =
      gaussianLadderSurvivalProbability X μ k * gaussianLadderSurvivalProbability X μ (n-k) := by
    intro k hk
    have hprod := ladderPrefixMoment_minimum_product_integral hX hi hG k (n-k) 0 0
    change (∫ ω, ladderPrefixMoment (ladderReverseNeg X k) k 0 ω *
      ladderPrefixMoment (fun j => X (k+j)) (n-k) 0 ω ∂μ) = _
    rw [hprod, ladderPrefixMoment_integral_zero hX hi hG,
      ladderPrefixMoment_integral_zero hX hi hG,
      gaussianLadderSurvivalProbability]
  have hsum := integral_finsetSum (μ := μ) (s := Finset.range (n+1))
    (f := fun k ω =>
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0)) (by
      intro k hk
      have hprod := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k)
        (p := 0) (r := 0) (by norm_num) (by norm_num)
      apply hprod.congr
      filter_upwards [] with ω
      by_cases h₁ : ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k <;>
        by_cases h₂ : ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) <;>
        simp [ladderPrefixMoment, h₁, h₂, mul_comm])
  calc
    (∑ k ∈ Finset.range (n+1), gaussianLadderSurvivalProbability X μ k *
      gaussianLadderSurvivalProbability X μ (n-k)) =
      ∑ k ∈ Finset.range (n+1),
        (∫ ω, (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
          (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) ∂μ) := by
            apply Finset.sum_congr rfl
            intro k hk
            exact (hterms k hk).symm
    _ = ∫ ω, (∑ k ∈ Finset.range (n+1),
        (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
        (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0)) ∂μ := hsum.symm
    _ = 1 := hInt

end SwingRepair

namespace SwingRepair
variable {Ω : Type*}
theorem ladder_piece_square_partition_pointwise
    (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω)
    (hd : Function.Injective (fun j => cumulativeSamples X j ω)) :
    (∑ k ∈ Finset.range (n+1),
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
      ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 +
        (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 -
        2*cumulativeSamples (ladderReverseNeg X k) k ω *
          cumulativeSamples (fun j => X (k+j)) (n-k) ω)) =
      (cumulativeSamples X n ω)^2 := by
  obtain ⟨k, hk⟩ := exists_ladderMinimumAt (fun j => cumulativeSamples X j ω) n
    (fun i hi j hj hij => hd.ne hij)
  have hp (j : ℕ) (hj : j ≤ n) :
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X j) j then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun l => X (j+l)) (n-j) then 1 else 0) =
      if ladderMinimumAt (fun l => cumulativeSamples X l ω) n j then 1 else 0 := by
    by_cases hm : ladderMinimumAt (fun l => cumulativeSamples X l ω) n j
    · obtain ⟨hl, hr⟩ := (ladderMinimumAt_iff_positive_pieces X n j hj ω).mp hm
      simp [hl, hr, hm]
    · have hn : ¬ (ω ∈ ladderPositivePrefix (ladderReverseNeg X j) j ∧
          ω ∈ ladderPositivePrefix (fun l => X (j+l)) (n-j)) := by
        intro hh; exact hm ((ladderMinimumAt_iff_positive_pieces X n j hj ω).mpr hh)
      by_cases h1 : ω ∈ ladderPositivePrefix (ladderReverseNeg X j) j <;>
        by_cases h2 : ω ∈ ladderPositivePrefix (fun l => X (j+l)) (n-j) <;>
        simp [h1, h2, hm] at hn ⊢
  rw [Finset.sum_eq_single k]
  · have hkn : k ≤ n := hk.1
    rw [hp k hk.1]
    simp only [if_pos hk, one_mul]
    rw [cumulativeSamples_ladderReverseNeg X k k le_rfl ω]
    have hs := cumulativeSamples_add_shift X k (n-k) ω
    rw [show k+(n-k)=n by omega] at hs
    have hkk : k-k = 0 := Nat.sub_self k
    rw [hkk, cumulativeSamples_zero] at *
    ring_nf at hs ⊢
    rw [hs]
    ring
  · intro j hj hjk
    rw [hp j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    have hnone : ¬ ladderMinimumAt (fun l => cumulativeSamples X l ω) n j := by
      intro hjm; exact hjk (ladderMinimumAt_unique hjm hk)
    simp [hnone]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk.1))).elim
end SwingRepair
