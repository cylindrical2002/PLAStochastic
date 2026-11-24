import PLAStochastic.Index.CEPS.Scaled.QuotientSpatialRecovery
import PLAStochastic.Index.CEPS.Normal.MovingHolomorphicSlope
import PLAStochastic.ForMathlib.Analysis.Complex.UniformTaylorJets

/-! # Joint spatial families and uniform recovery of genuine quotient jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

theorem cepsCumulantJetQuotient_differentiableOn_joint (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsCumulantJetQuotient p N lam z x.1 x.2) (ball 0 B ×ˢ ball 0 R) := by
  let a := cepsCumulantRootModel p N lam z 1 N
  let d := cepsCumulantRootModel p N lam z (-1) N
  let S : ℝ := R + 1 + ‖a 0‖ + ‖d 0‖
  have ha0 : a 0 ∈ ball (0 : ℂ) S := by rw [mem_ball_zero_iff]; dsimp [S]; linarith [norm_nonneg (d 0)]
  have hd0 : d 0 ∈ ball (0 : ℂ) S := by rw [mem_ball_zero_iff]; dsimp [S]; linarith [norm_nonneg (a 0)]
  have ha : Differentiable ℂ a := cepsCumulantRootModel_differentiable p N lam z 1 N
  have hd : Differentiable ℂ d := cepsCumulantRootModel_differentiable p N lam z (-1) N
  obtain ⟨B, hB, hball⟩ := Metric.mem_nhds_iff.mp
    ((ha.continuous.continuousAt.eventually (isOpen_ball.mem_nhds ha0)).and
      (hd.continuous.continuousAt.eventually (isOpen_ball.mem_nhds hd0)))
  have hG : DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsCumulantQuotientSpatialUnit p N lam z x.1 x.2) (ball 0 B ×ˢ ball 0 S) :=
    fun x _ => (cepsCumulantQuotientSpatialUnit_joint_analyticAt p N lam z x).differentiableAt.differentiableWithinAt
  have he := cepsNormal_joint_moving_second_dslope_of_differentiable isOpen_ball hG
    ha.differentiableOn hd.differentiableOn (fun _ hb => (hball hb).1) (fun _ hb => (hball hb).2)
  exact ⟨B, hB, he.mono (fun x hx => ⟨hx.1, ball_subset_ball
    (show R ≤ S by dsimp [S]; linarith [norm_nonneg (a 0), norm_nonneg (d 0)]) hx.2⟩)⟩

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledQuotient_spatial_differentiableOn_joint (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) {R : ℝ} (hR : 0 < R) :
    ∃ B : ℝ, 0 < B ∧ DifferentiableOn ℂ
      (fun x : ℂ × ℂ => cepsScaledQuotient D θ ρW lam z x.1 (x.1 * x.2))
      (ball 0 B ×ˢ ball 0 R) := by
  let B : ℝ := min (dom.canonScaleRadius lam z) (dom.ρA / (2 * R))
  have hB : 0 < B := by dsimp [B]; positivity [canonScaleRadius_pos dom hW hθ hD lam z, dom.ρA_pos]
  have hBR : B * R ≤ dom.ρA / 2 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (dom.canonScaleRadius lam z) (dom.ρA / (2 * R))) hR.le
    have he : dom.ρA / (2 * R) * R = dom.ρA / 2 := by field_simp [hR.ne']
    exact hh.trans_eq he
  have hmap : MapsTo (fun x : ℂ × ℂ => (x.1, x.1 * x.2)) (ball 0 B ×ˢ ball 0 R)
      (ball 0 (dom.canonScaleRadius lam z) ×ˢ ball 0 dom.ρA) := by
    intro x hx
    refine ⟨ball_subset_ball (min_le_left _ _) hx.1, mem_ball_zero_iff.mpr ?_⟩
    calc
      ‖x.1 * x.2‖ = ‖x.1‖ * ‖x.2‖ := norm_mul _ _
      _ ≤ B * R := mul_le_mul (mem_ball_zero_iff.mp hx.1).le (mem_ball_zero_iff.mp hx.2).le
        (norm_nonneg _) hB.le
      _ ≤ dom.ρA / 2 := hBR
      _ < dom.ρA := half_lt_self dom.ρA_pos
  have hcurve : DifferentiableOn ℂ (fun x : ℂ × ℂ => (x.1, x.1 * x.2)) (ball 0 B ×ˢ ball 0 R) := by
    fun_prop
  have he := (cepsScaledQuotient_differentiableOn dom hW hθ hD lam hz).comp hcurve hmap
  exact ⟨B, hB, he⟩

include dom hW hθ hD in
theorem cepsScaledQuotient_spatial_jet_budget (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {R : ℝ} (hR : 0 < R) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {b ξ : ℂ}, b ∈ ball (0 : ℂ) B → ξ ∈ ball 0 R →
      ‖cepsScaledQuotient D θ ρW lam z b (b * ξ) -
        cepsCumulantJetQuotient (cepsJet f) N lam z b ξ‖ ≤ C * ‖b‖ ^ (N + 1) := by
  obtain ⟨BF, hBF, hF⟩ := cepsScaledQuotient_spatial_differentiableOn_joint dom hW hθ hD lam hz
    (show 0 < 2 * R by positivity)
  obtain ⟨BG, hBG, hG⟩ := cepsCumulantJetQuotient_differentiableOn_joint (cepsJet f) N lam z
    (show 0 < 2 * R by positivity)
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
  have hcont := (hF.continuousOn.mono hsubF).sub (hG.continuousOn.mono hsubG)
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) B).prod
    (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (0, 0)
    ⟨mem_closedBall_self hB.le, mem_closedBall_self hR.le⟩)
  have hsmall : ball (0 : ℂ) B ×ˢ ball (0 : ℂ) R ⊆ closedBall (0 : ℂ) B ×ˢ closedBall (0 : ℂ) R :=
    fun _ hx => ⟨ball_subset_closedBall hx.1, ball_subset_closedBall hx.2⟩
  refine ⟨((N + 1).factorial : ℝ) * M / (B / 4) ^ (N + 1), B / 2, by positivity, half_pos hB, ?_⟩
  intro b ξ hb hξ
  apply norm_sub_le_of_uniform_taylorJets hB (hF.mono (hsmall.trans hsubF))
    (hG.mono (hsmall.trans hsubG)) (fun b hb ξ hξ => hM (b, ξ) (hsmall ⟨hb, hξ⟩)) N ?_ hb hξ
  intro ξ _ j hj
  exact cepsScaledQuotient_curve_taylorJets_eq_finite_model dom hW hθ hD hfW N lam hz
    (analyticAt_const (v := ξ)) j hj

end PGM
