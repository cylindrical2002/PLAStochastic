import PLAStochastic.Swing.Gaussian.ZeroLadder.PieceConvolution
import PLAStochastic.Swing.Gaussian.ZeroLadder.EpochLimits
import PLAStochastic.Swing.Gaussian.ZeroLadder.WalkSquare
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option maxHeartbeats 1000000
set_option linter.unnecessarySeqFocus false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
theorem gaussian_ladder_square_term (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n k : ℕ) :
      (∫ ω, (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
      ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 +
        (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 -
        2*cumulativeSamples (ladderReverseNeg X k) k ω * cumulativeSamples (fun j => X (k+j)) (n-k) ω) ∂μ) =
      gaussianLadderSurvivingSecondMoment X μ k * gaussianLadderSurvivalProbability X μ (n-k) +
      gaussianLadderSurvivalProbability X μ k * gaussianLadderSurvivingSecondMoment X μ (n-k) -
      2 * (gaussianLadderSurvivingFirstMoment X μ k * gaussianLadderSurvivingFirstMoment X μ (n-k)) := by
  have h1i := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k) (p := 2) (r := 0) (by norm_num) (by norm_num)
  have h2i := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k) (p := 0) (r := 2) (by norm_num) (by norm_num)
  have h3i := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k) (p := 1) (r := 1) (by norm_num) (by norm_num)
  have h1 := ladderPrefixMoment_minimum_product_integral hX hi hG k (n-k) 2 0
  have h2 := ladderPrefixMoment_minimum_product_integral hX hi hG k (n-k) 0 2
  have h3 := ladderPrefixMoment_minimum_product_integral hX hi hG k (n-k) 1 1
  have heq : (fun ω =>
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
      ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 + (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 - 2*cumulativeSamples (ladderReverseNeg X k) k ω*cumulativeSamples (fun j => X (k+j)) (n-k) ω)) =
      (fun ω => ladderPrefixMoment (ladderReverseNeg X k) k 2 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 0 ω + ladderPrefixMoment (ladderReverseNeg X k) k 0 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 2 ω - 2*(ladderPrefixMoment (ladderReverseNeg X k) k 1 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 1 ω)) := by
    funext ω
    by_cases h₁ : ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k <;> by_cases h₂ : ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) <;> simp [ladderPrefixMoment, h₁, h₂] <;> ring
  rw [heq]
  have hspl := integral_sub (h1i.add h2i) (h3i.const_mul 2)
  -- use exact function equality to align subtraction syntax
  have hsplit : (∫ ω, ladderPrefixMoment (ladderReverseNeg X k) k 2 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 0 ω + ladderPrefixMoment (ladderReverseNeg X k) k 0 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 2 ω - 2*(ladderPrefixMoment (ladderReverseNeg X k) k 1 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 1 ω) ∂μ) =
    (∫ ω, ladderPrefixMoment (ladderReverseNeg X k) k 2 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 0 ω + ladderPrefixMoment (ladderReverseNeg X k) k 0 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 2 ω ∂μ) -
      ∫ ω, 2*(ladderPrefixMoment (ladderReverseNeg X k) k 1 ω * ladderPrefixMoment (fun j => X (k+j)) (n-k) 1 ω) ∂μ := by
    simpa [mul_comm, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hspl
  rw [hsplit, integral_add h1i h2i, integral_const_mul, h1, h2, h3]
  simp only [ladderPrefixMoment_integral_zero hX hi hG, ladderPrefixMoment_integral_two hX hi hG, ladderPrefixMoment_integral_one hX hi hG]


 theorem gaussian_ladder_square_wald_identity
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (n : ℝ) =
      2 * (∑ k ∈ Finset.range (n+1), gaussianLadderSurvivingSecondMoment X μ k * gaussianLadderSurvivalProbability X μ (n-k)) -
      2 * (∑ k ∈ Finset.range (n+1), gaussianLadderSurvivingFirstMoment X μ k * gaussianLadderSurvivingFirstMoment X μ (n-k)) := by
  let := hi.isProbabilityMeasure
  have hIntTermi (k : ℕ) : Integrable (fun ω =>
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
      ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 + (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 -
        2*cumulativeSamples (ladderReverseNeg X k) k ω * cumulativeSamples (fun j => X (k+j)) (n-k) ω)) μ := by
    have h1 := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k) (p := 2) (r := 0) (by norm_num) (by norm_num)
    have h2 := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k) (p := 0) (r := 2) (by norm_num) (by norm_num)
    have h3 := ladderPrefixMoment_minimum_product_integrable hX hi hG k (n-k) (p := 1) (r := 1) (by norm_num) (by norm_num)
    simp only [ladderPrefixMoment] at h1 h2 h3
    have hh := (h1.add h2).sub (h3.const_mul 2)
    refine hh.congr (ae_of_all _ (fun ω => ?_))
    by_cases h₁ : ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k
    · by_cases h₂ : ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k)
      · simp [h₁, h₂]; ring
      · simp [h₁, h₂]
    · by_cases h₂ : ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k)
      · simp [h₁, h₂]
      · simp [h₁, h₂]
  have hIntTerm (k : ℕ) := gaussian_ladder_square_term hX hi hG n k
  have hpoint : ∀ᵐ ω ∂μ, (∑ k ∈ Finset.range (n+1),
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
      ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 + (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 -
        2*cumulativeSamples (ladderReverseNeg X k) k ω * cumulativeSamples (fun j => X (k+j)) (n-k) ω)) = (cumulativeSamples X n ω)^2 := by
    filter_upwards [cumulativeSamples_distinct_ae hX hi hG] with ω hd
    exact ladder_piece_square_partition_pointwise X n ω hd
  have hsum := integral_finsetSum (μ := μ) (s := Finset.range (n+1)) (f := fun k ω =>
      (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
      (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
      ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 + (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 -
        2*cumulativeSamples (ladderReverseNeg X k) k ω * cumulativeSamples (fun j => X (k+j)) (n-k) ω)) (fun k hk => hIntTermi k)
  have hEq : (n : ℝ) = ∑ k ∈ Finset.range (n+1), (gaussianLadderSurvivingSecondMoment X μ k * gaussianLadderSurvivalProbability X μ (n-k) + gaussianLadderSurvivalProbability X μ k * gaussianLadderSurvivingSecondMoment X μ (n-k) - 2*(gaussianLadderSurvivingFirstMoment X μ k * gaussianLadderSurvivingFirstMoment X μ (n-k))) := by
    calc
      (n : ℝ) = ∫ ω, (cumulativeSamples X n ω)^2 ∂μ := (gaussianZeroWalk_square_integral hX hi hG n).symm
      _ = ∫ ω, (∑ k ∈ Finset.range (n+1),
        (if ω ∈ ladderPositivePrefix (ladderReverseNeg X k) k then (1 : ℝ) else 0) *
        (if ω ∈ ladderPositivePrefix (fun j => X (k+j)) (n-k) then 1 else 0) *
        ((cumulativeSamples (ladderReverseNeg X k) k ω)^2 + (cumulativeSamples (fun j => X (k+j)) (n-k) ω)^2 -
          2*cumulativeSamples (ladderReverseNeg X k) k ω * cumulativeSamples (fun j => X (k+j)) (n-k) ω)) ∂μ := (integral_congr_ae hpoint).symm
      _ = _ := hsum
      _ = _ := by simp_rw [gaussian_ladder_square_term hX hi hG n]
  have hsym : (∑ k ∈ Finset.range (n+1), gaussianLadderSurvivalProbability X μ k * gaussianLadderSurvivingSecondMoment X μ (n-k)) =
      ∑ k ∈ Finset.range (n+1), gaussianLadderSurvivingSecondMoment X μ k * gaussianLadderSurvivalProbability X μ (n-k) := by
    have hr := (Finset.sum_range_reflect (fun k => gaussianLadderSurvivalProbability X μ k * gaussianLadderSurvivingSecondMoment X μ (n-k)) (n+1)).symm
    calc
      _ = ∑ k ∈ Finset.range (n+1), gaussianLadderSurvivalProbability X μ (n-k) * gaussianLadderSurvivingSecondMoment X μ (n-(n-k)) := by simpa only [Nat.add_sub_cancel] using hr
      _ = ∑ k ∈ Finset.range (n+1), gaussianLadderSurvivalProbability X μ (n-k) * gaussianLadderSurvivingSecondMoment X μ k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hklt : k < n+1 := Finset.mem_range.mp hk
        have hk' : k ≤ n := by omega
        have hh : n - (n-k) = k := by omega
        rw [hh]
      _ = _ := by apply Finset.sum_congr rfl; intro k hk; ring
  rw [hEq, Finset.sum_sub_distrib, Finset.sum_add_distrib, hsym]
  have htwo : (∑ x ∈ Finset.range (n+1), 2 * (gaussianLadderSurvivingFirstMoment X μ x * gaussianLadderSurvivingFirstMoment X μ (n-x))) =
      2 * (∑ x ∈ Finset.range (n+1), gaussianLadderSurvivingFirstMoment X μ x * gaussianLadderSurvivingFirstMoment X μ (n-x)) := by
    rw [← Finset.mul_sum]
  rw [htwo]
  ring

end SwingRepair
