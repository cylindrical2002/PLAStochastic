import PLAStochastic.Index.CEPS.Scaled.KernelGJetModel
import PLAStochastic.Index.CEPS.Scaled.KernelGJointJets
import PLAStochastic.ForMathlib.Analysis.Complex.JointSpatialBudget
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Finite spatial-node substitutions in the explicit mixed-jet kernel -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries Asymptotics
open PGM.WienerHopf
namespace PGM

theorem cepsKernelGJetModel_curve_taylorJets_congr (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z : ℂ) {ξ ξ' : ℂ → ℂ} (hξ : AnalyticAt ℂ ξ 0) (hξ' : AnalyticAt ℂ ξ' 0)
    (he : (fun b => ξ b - ξ' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1))) :
    ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => cepsKernelGJetModel p N lam z b (ξ b)) 0) =
      coeff j (complexTaylorSeries (fun b => cepsKernelGJetModel p N lam z b (ξ' b)) 0) := by
  let R : ℝ := 4 * (1 + ‖ξ 0‖ + ‖ξ' 0‖)
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨B, M, hB, _, hG, hbound⟩ := exists_bound_joint_spatial_germ hR
    (cepsKernelGJetModel_differentiableOn_joint p N lam z (by positivity))
  have hξ0 : ξ 0 ∈ ball (0 : ℂ) (R / 2) := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (ξ 0), norm_nonneg (ξ' 0)]
  have hξ'0 : ξ' 0 ∈ ball (0 : ℂ) (R / 2) := by
    rw [mem_ball_zero_iff]; dsimp [R]; linarith [norm_nonneg (ξ 0), norm_nonneg (ξ' 0)]
  have hBmem : ∀ᶠ b : ℂ in 𝓝 0, b ∈ ball (0 : ℂ) B := ball_mem_nhds _ hB
  have hnode : (fun b => cepsKernelGJetModel p N lam z b (ξ b) -
      cepsKernelGJetModel p N lam z b (ξ' b)) =O[𝓝 (0 : ℂ)] (fun b => ξ b - ξ' b) := by
    apply IsBigO.of_bound (4 * M / R)
    filter_upwards [hBmem, hξ.continuousAt.eventually (isOpen_ball.mem_nhds hξ0),
      hξ'.continuousAt.eventually (isOpen_ball.mem_nhds hξ'0)] with b hb hξb hξ'b
    have hGS : DifferentiableOn ℂ (cepsKernelGJetModel p N lam z b) (ball 0 R) := fun t ht =>
      (differentiableAt_slice_snd (isOpen_ball.prod isOpen_ball) hG ⟨hb, ht⟩).differentiableWithinAt
    exact norm_sub_le_of_ball_half hR hGS (hbound b hb) hξb hξ'b
  exact complexTaylorSeries_coeff_eq_of_isBigO
    (cepsKernelGJetModel_curve_analyticAt p N lam z hξ)
    (cepsKernelGJetModel_curve_analyticAt p N lam z hξ') N (hnode.trans he)

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateG_root_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z sign : ℂ}, 0 ≤ z.re → sign ^ 2 = 1 → ∀ j ≤ N,
        coeff j (complexTaylorSeries (fun b => cepsScaledSurrogateG dom ρW N lam z b
          (cepsScaledSignedRoot D θ ρW lam z sign b)) 0) =
        coeff j (complexTaylorSeries (fun b => cepsKernelGJetModel (cepsJet f) N lam z b
          (cepsCumulantRootModel (cepsJet f) N lam z sign N b)) 0) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateG_curve_taylorJets_eq_finite_model dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z sign hz hsign j hj
  have hroot := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  have hmodel := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z sign N).analyticAt 0
  exact (he hW hfW hneg hη hf hfS hηc hclose N hN lam hz hroot j hj).trans
    (cepsKernelGJetModel_curve_taylorJets_congr (cepsJet f) N lam z hroot hmodel
      (cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz hsign) j hj)

end PGM
