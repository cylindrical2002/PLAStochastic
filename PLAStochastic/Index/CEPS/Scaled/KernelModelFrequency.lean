import PLAStochastic.Index.CEPS.Scaled.KernelDenominatorZero
import PLAStochastic.Index.CEPS.Scaled.KernelPairModel
import PLAStochastic.Index.CEPS.Scaled.KernelHalfFrequency
import PLAStochastic.ForMathlib.Analysis.Complex.TimeOperatorHolomorphy

/-! # Genuine complete-pair frequency neighborhoods for arbitrary finite jet vectors -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

/-- Arbitrary positive-variance jet vectors have genuine joint complete-pair neighborhoods.
No probability law or unpaid denominator premise is required. -/
theorem cepsKernelPairJetModel_frequency_neighborhood (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelPairJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) := by
  obtain ⟨C, hC, hU, hA⟩ := cepsKernelFiniteFactors_frequency_neighborhood p hp N lam hz hne
    (cepsKernelDenominatorJetModel_zero_ne p hp N lam hz)
  have hwc : ContinuousAt (fun x : ℂ × ℂ => 1 + x.1 * (lam : ℂ)) (0, z) := by fun_prop
  obtain ⟨B, hB, hBC, hwidth⟩ := exists_polydisc_ne_zero hC hwc (by simp)
  have hsub : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) C ×ˢ ball z C :=
    fun _ hx => ⟨ball_subset_ball hBC hx.1, ball_subset_ball hBC hx.2⟩
  have ht := differentiableOn_complete_time_pair
    (A := fun b w => cepsKernelEntranceJetModel p N lam w b)
    (U := fun b w => cepsKernelBridgeJetModel p N lam w b) (isOpen_ball.prod isOpen_ball)
    (lam : ℂ) (hA.mono hsub) (hU.mono hsub) hwidth
  refine ⟨B, hB, ?_⟩
  simpa only [cepsKernelPairJetModel] using ht

/-- The complete positive half-line pair also has genuine joint frequency neighborhoods. -/
theorem cepsKernelHalfPairJetModel_frequency_neighborhood (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ}
    (hz : 0 ≤ z.re) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelHalfPairJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) := by
  have hRm : cepsCumulantRootModel p N lam z (-1) N 0 ≠ 0 := by
    rw [cepsCumulantRootModel_zero p hp.ne' N lam z (-1) (by norm_num) N]
    exact cepsCumulantRootBase_minus_ne_zero p hp (by linarith) z
  obtain ⟨C, hC, hU, hA⟩ := cepsKernelHalfFactors_frequency_neighborhood p hp N lam hz
    (Or.inl (by linarith)) hRm
  have hwc : ContinuousAt (fun x : ℂ × ℂ => 1 + x.1 * (lam : ℂ)) (0, z) := by fun_prop
  obtain ⟨B, hB, hBC, hwidth⟩ := exists_polydisc_ne_zero hC hwc (by simp)
  have hsub : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) C ×ˢ ball z C :=
    fun _ hx => ⟨ball_subset_ball hBC hx.1, ball_subset_ball hBC hx.2⟩
  have ht := differentiableOn_complete_time_pair
    (A := fun b w => cepsKernelHalfEntranceJetModel p N lam w b)
    (U := fun b w => cepsKernelHalfBridgeJetModel p N lam w b)
    (isOpen_ball.prod isOpen_ball) (lam : ℂ) (hA.mono hsub) (hU.mono hsub) hwidth
  refine ⟨B, hB, ?_⟩
  simpa only [cepsKernelHalfPairJetModel] using ht

/-- Subtraction preserves joint complete-pair holomorphy for arbitrary positive-variance
finite jet inputs, away from the single joint origin. -/
theorem cepsKernelSubtractedPairJetModel_frequency_neighborhood (p : ℕ → ℝ)
    (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelSubtractedPairJetModel p N lam x.2 x.1)
        (ball 0 B ×ˢ ball z B) := by
  obtain ⟨C, hC, hP⟩ := cepsKernelPairJetModel_frequency_neighborhood p hp N lam hz hne
  by_cases hlam : 1 ≤ lam
  · obtain ⟨D, hD, hH⟩ := cepsKernelHalfPairJetModel_frequency_neighborhood p hp N lam hlam hz
    let B := min C D
    have hsubC : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) C ×ˢ ball z C :=
      fun _ hx => ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩
    have hsubD : ball (0 : ℂ) B ×ˢ ball z B ⊆ ball (0 : ℂ) D ×ˢ ball z D :=
      fun _ hx => ⟨ball_subset_ball (min_le_right _ _) hx.1, ball_subset_ball (min_le_right _ _) hx.2⟩
    refine ⟨B, lt_min hC hD, ?_⟩
    simpa only [cepsKernelSubtractedPairJetModel, if_pos hlam, Pi.sub_apply] using!
      (hP.mono hsubC).sub (hH.mono hsubD)
  · exact ⟨C, hC, by simpa only [cepsKernelSubtractedPairJetModel, if_neg hlam, sub_zero] using hP⟩

end PGM
