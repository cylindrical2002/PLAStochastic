import PLAStochastic.Index.CEPS.Scaled.QuotientUnit
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Genuine analytic quotient-unit germs and compact finite-model budgets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

theorem cepsCumulantJetQuotient_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z : ℂ) :
    cepsCumulantJetQuotient p N lam z = cepsCumulantJetQuotient p' N lam z := by
  funext b ξ
  simp only [cepsCumulantJetQuotient, cepsCumulantQuotientSpatialUnit_congr N hp,
    cepsCumulantRootModel_congr N hp]

theorem cepsCumulantQuotientSpatialUnit_disc_bound (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) (R : ℝ) :
    ∃ M : ℝ, ∀ b ∈ ball (0 : ℂ) 1, ∀ ξ ∈ ball (0 : ℂ) R,
      ‖cepsCumulantQuotientSpatialUnit p N lam z b ξ‖ ≤ M := by
  have hc : Continuous (fun x : ℂ × ℂ => cepsCumulantQuotientSpatialUnit p N lam z x.1 x.2) :=
    continuous_iff_continuousAt.mpr fun x =>
      (cepsCumulantQuotientSpatialUnit_joint_analyticAt p N lam z x).continuousAt
  obtain ⟨M, hM⟩ := ((isCompact_closedBall (0 : ℂ) 1).prod
    (isCompact_closedBall (0 : ℂ) R)).exists_bound_of_continuousOn hc.continuousOn
  exact ⟨M, fun b hb ξ hξ => hM (b, ξ) ⟨ball_subset_closedBall hb, ball_subset_closedBall hξ⟩⟩

theorem cepsCumulantJetQuotientAtRoot_analyticAt (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z sign : ℂ) : AnalyticAt ℂ (cepsCumulantJetQuotientAtRoot p N lam z sign) 0 := by
  let a := cepsCumulantRootModel p N lam z 1 N
  let d := cepsCumulantRootModel p N lam z (-1) N
  let t := cepsCumulantRootModel p N lam z sign N
  let R : ℝ := 1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖
  have hG : AnalyticOnNhd ℂ (fun x : ℂ × ℂ => cepsCumulantQuotientSpatialUnit p N lam z x.1 x.2)
      (ball 0 1 ×ˢ ball 0 R) := fun x _ => cepsCumulantQuotientSpatialUnit_joint_analyticAt p N lam z x
  have ha : AnalyticAt ℂ a 0 := (cepsCumulantRootModel_differentiable p N lam z 1 N).analyticAt 0
  have hd : AnalyticAt ℂ d 0 := (cepsCumulantRootModel_differentiable p N lam z (-1) N).analyticAt 0
  have ht : AnalyticAt ℂ t 0 := (cepsCumulantRootModel_differentiable p N lam z sign N).analyticAt 0
  apply cepsNormal_analyticAt_moving_second_dslope (by norm_num : (0 : ℝ) < 1) hG ha hd ht
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (d 0), norm_nonneg (t 0)]
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (t 0)]
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0)]

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotientSpatialUnit_analyticOnNhd_disc {R B : ℝ}
    (hR : 0 < R) (hBR : B * R < cepsCgfRadius D θ) :
    AnalyticOnNhd ℂ (fun x : ℂ × ℂ => cepsScaledQuotientSpatialUnit ρW lam z x.1 x.2)
      (ball 0 B ×ˢ ball 0 R) := by
  intro x hx
  apply cepsScaledQuotientSpatialUnit_joint_analyticAt hW hθ hD _ _ x
  calc
    ‖x.1 * x.2‖ = ‖x.1‖ * ‖x.2‖ := norm_mul _ _
    _ ≤ ‖x.1‖ * R := mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx.2).le (norm_nonneg _)
    _ < B * R := mul_lt_mul_of_pos_right (mem_ball_zero_iff.mp hx.1) hR
    _ < cepsCgfRadius D θ := hBR

include dom hW hθ hD in
theorem cepsScaledUnitQuotientAtRoot_analyticAt (lam : ℝ) {z sign : ℂ}
    (hz : 0 ≤ z.re) (hsign : sign ^ 2 = 1) :
    AnalyticAt ℂ (cepsScaledUnitQuotientAtRoot D θ ρW lam z sign) 0 := by
  let a := cepsScaledSignedRoot D θ ρW lam z 1
  let d := cepsScaledSignedRoot D θ ρW lam z (-1)
  let t := cepsScaledSignedRoot D θ ρW lam z sign
  let R : ℝ := 1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖
  have hR : 0 < R := by dsimp [R]; positivity
  let B : ℝ := cepsCgfRadius D θ / (2 * R)
  have hB : 0 < B := by dsimp [B]; exact div_pos (cepsCgfRadius_pos hD hθ) (by positivity)
  have hBR : B * R < cepsCgfRadius D θ := by
    have he : B * R = cepsCgfRadius D θ / 2 := by dsimp [B]; field_simp [hR.ne']
    rw [he]
    exact half_lt_self (cepsCgfRadius_pos hD hθ)
  have hG := cepsScaledQuotientSpatialUnit_analyticOnNhd_disc hW hθ hD (lam := lam) (z := z) hR hBR
  have ha := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hd := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have ht := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  apply cepsNormal_analyticAt_moving_second_dslope hB hG ha hd ht
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (d 0), norm_nonneg (t 0)]
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (t 0)]
  · rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (a 0), norm_nonneg (d 0)]

end PGM
