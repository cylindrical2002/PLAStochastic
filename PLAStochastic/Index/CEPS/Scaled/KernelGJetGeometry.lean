import PLAStochastic.Index.CEPS.Scaled.KernelGJetBudget
import PLAStochastic.ForMathlib.Analysis.Complex.JointSpatialBudget

/-! # Common spatial germ budgets for actual and finite mixed-jet kernels -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateG_finite_jet_geometry :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → ∀ {R : ℝ}, 0 < R →
      ∃ C B M : ℝ, 0 ≤ C ∧ 0 < B ∧ 0 ≤ M ∧
        DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsScaledSurrogateG dom ρW N lam z x.1 x.2)
          (ball 0 B ×ˢ ball 0 R) ∧
        DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsKernelGJetModel (cepsJet f) N lam z x.1 x.2)
          (ball 0 B ×ˢ ball 0 R) ∧
        (∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R, ‖cepsKernelGJetModel (cepsJet f) N lam z b ξ‖ ≤ M) ∧
        ∀ b ∈ ball (0 : ℂ) B, ∀ ξ ∈ ball (0 : ℂ) R,
          ‖cepsScaledSurrogateG dom ρW N lam z b ξ - cepsKernelGJetModel (cepsJet f) N lam z b ξ‖ ≤
            C * ‖b‖ ^ (N + 1) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateG_spatial_jet_budget dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz R hR
  obtain ⟨C, BE, hC, hBE, hE⟩ := he hW hfW hneg hη hf hfS hηc hclose N hN lam hz hR
  obtain ⟨BF, hBF, hF⟩ := cepsScaledSurrogateG_fixedSpatial_differentiableOn_joint
    dom hW hθ hD hfS hηc N (by omega) lam hz hR
  obtain ⟨BG, M, hBG, hM, hG, hbound⟩ := exists_bound_joint_spatial_germ hR
    (cepsKernelGJetModel_differentiableOn_joint (cepsJet f) N lam z (by positivity))
  let B := min BE (min BF BG)
  have hB : 0 < B := by dsimp [B]; positivity
  have hBF' : B ≤ BF := (min_le_right BE _).trans (min_le_left BF BG)
  have hBG' : B ≤ BG := (min_le_right BE _).trans (min_le_right BF BG)
  exact ⟨C, B, M, hC, hB, hM,
    hF.mono (fun x hx => ⟨ball_subset_ball hBF' hx.1, hx.2⟩),
    hG.mono (fun x hx => ⟨ball_subset_ball hBG' hx.1, hx.2⟩),
    fun b hb ξ hξ => hbound b (ball_subset_ball hBG' hb) ξ hξ,
    fun b hb ξ hξ => hE (ball_subset_ball (min_le_left BE _) hb) hξ⟩

end PGM
