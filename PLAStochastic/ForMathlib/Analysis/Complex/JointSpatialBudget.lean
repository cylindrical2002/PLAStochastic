import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Compact-disc norm budgets for jointly holomorphic spatial germs -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem exists_bound_joint_spatial_germ {G : ℂ → ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hG : ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 B ×ˢ ball 0 (2 * R))) :
    ∃ B M : ℝ, 0 < B ∧ 0 ≤ M ∧
      DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2) (ball 0 B ×ˢ ball 0 R) ∧
      ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖G b ξ‖ ≤ M := by
  obtain ⟨B, hB, hD⟩ := hG
  have hsub : closedBall (0 : ℂ) (B / 2) ×ˢ closedBall (0 : ℂ) R ⊆
      ball (0 : ℂ) B ×ˢ ball (0 : ℂ) (2 * R) := by
    intro x hx
    exact ⟨mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.1).trans_lt (half_lt_self hB)),
      mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx.2).trans_lt (by linarith))⟩
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) (B / 2)).prod
    (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn (hD.continuousOn.mono hsub)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0)
    ⟨mem_closedBall_self (half_pos hB).le, mem_closedBall_self hR.le⟩)
  have hsmall : ball (0 : ℂ) (B / 2) ×ˢ ball (0 : ℂ) R ⊆
      closedBall (0 : ℂ) (B / 2) ×ˢ closedBall (0 : ℂ) R :=
    fun _ hx => ⟨ball_subset_closedBall hx.1, ball_subset_closedBall hx.2⟩
  exact ⟨B / 2, M, half_pos hB, hM0, hD.mono (hsmall.trans hsub),
    fun b hb ξ hξ => hM (b, ξ) (hsmall ⟨hb, hξ⟩)⟩

end PGM
