import PLAStochastic.ForMathlib.Analysis.Complex.UniformTaylorJets

/-! # Uniform finite-jet error budgets on arbitrary fixed spatial discs -/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries
namespace PGM

theorem exists_uniform_taylorJets_budget {F G : ℂ → ℂ → ℂ} (N : ℕ) {R : ℝ} (hR : 0 < R)
    (hF : ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ (fun x : ℂ × ℂ => F x.1 x.2)
      (ball 0 B ×ˢ ball 0 (2 * R)))
    (hG : ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ (fun x : ℂ × ℂ => G x.1 x.2)
      (ball 0 B ×ˢ ball 0 (2 * R)))
    (he : ∀ ξ : ℂ, ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => F b ξ) 0) =
      coeff j (complexTaylorSeries (fun b => G b ξ) 0)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {b ξ : ℂ}, b ∈ ball (0 : ℂ) B → ξ ∈ ball 0 R →
      ‖F b ξ - G b ξ‖ ≤ C * ‖b‖ ^ (N + 1) := by
  obtain ⟨BF, hBF, hFD⟩ := hF
  obtain ⟨BG, hBG, hGD⟩ := hG
  let B : ℝ := min BF BG / 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hsubF : closedBall (0 : ℂ) B ×ˢ closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) BF ×ˢ ball (0 : ℂ) (2 * R) := by
    intro x hx
    refine ⟨mem_ball_zero_iff.mpr ?_, mem_ball_zero_iff.mpr ?_⟩
    · have hb := mem_closedBall_zero_iff.mp hx.1; dsimp [B] at hb
      linarith [min_le_left BF BG]
    · exact (mem_closedBall_zero_iff.mp hx.2).trans_lt (by linarith)
  have hsubG : closedBall (0 : ℂ) B ×ˢ closedBall (0 : ℂ) R ⊆ ball (0 : ℂ) BG ×ˢ ball (0 : ℂ) (2 * R) := by
    intro x hx
    refine ⟨mem_ball_zero_iff.mpr ?_, mem_ball_zero_iff.mpr ?_⟩
    · have hb := mem_closedBall_zero_iff.mp hx.1; dsimp [B] at hb
      linarith [min_le_right BF BG]
    · exact (mem_closedBall_zero_iff.mp hx.2).trans_lt (by linarith)
  have hcont := (hFD.continuousOn.mono hsubF).sub (hGD.continuousOn.mono hsubG)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) B).prod
    (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0)
    ⟨mem_closedBall_self hB.le, mem_closedBall_self hR.le⟩)
  have hsmall : ball (0 : ℂ) B ×ˢ ball (0 : ℂ) R ⊆ closedBall (0 : ℂ) B ×ˢ closedBall (0 : ℂ) R :=
    fun _ hx => ⟨ball_subset_closedBall hx.1, ball_subset_closedBall hx.2⟩
  refine ⟨((N + 1).factorial : ℝ) * M / (B / 4) ^ (N + 1), B / 2, by positivity, half_pos hB, ?_⟩
  intro b ξ hb hξ
  exact norm_sub_le_of_uniform_taylorJets hB (hFD.mono (hsmall.trans hsubF))
    (hGD.mono (hsmall.trans hsubG)) (fun b hb ξ hξ => hM (b, ξ) (hsmall ⟨hb, hξ⟩)) N
    (fun ξ _ => he ξ) hb hξ

end PGM
