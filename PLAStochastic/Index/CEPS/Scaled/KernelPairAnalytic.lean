import PLAStochastic.Index.CEPS.Scaled.KernelPairJets
import PLAStochastic.Index.CEPS.Scaled.KernelHalfPairJets
import PLAStochastic.Index.CEPS.Scaled.SurrogatePairJoint

/-! # Genuine scale analytic germs of complete finite pair models -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsScaledSurrogatePair_analyticAt_zero {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (cepsScaledSurrogatePair dom ρW N lam z) 0 := by
  obtain ⟨B, hB, hP⟩ := cepsScaledSurrogatePair_holomorphic_near_joint
    dom hW hθ hD hf hη le_rfl N hN lam hz
      (mem_ball_self (surrogateJointScaleRadius_pos dom hW hθ hD N (cepsSobolev m η fW) lam z))
  exact analyticAt_slice_fst_on_polydisc hB hP

include dom hW hθ hD in
theorem cepsScaledSurrogateHalfPair_analyticAt_zero {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (cepsScaledSurrogateHalfPair dom ρW N lam z) 0 := by
  have hRA : 0 < min (dom.jointRootScaleRadius lam z)
      (dom.entranceScaleRadius N (cepsSobolev m η fW) lam z) :=
    lt_min (jointRootScaleRadius_pos dom hW hθ hD lam z)
      (entranceScale_constants dom hW hθ hD N (cepsSobolev m η fW) lam z).1
  obtain ⟨B, hB, hAB, hAD⟩ := cepsScaledSurrogateHalfBridge_holomorphic_near_joint
    dom hW hθ hD hf hη N hN lam hz (Or.inl (by linarith)) (mem_ball_self hRA)
  have hEA : 0 < dom.pairPolynomialScaleBase N (cepsSobolev m η fW) / (1 + |lam| + Real.sqrt ‖z‖) := by
    positivity [pairPolynomialScaleBase_pos dom hW hθ hD N (cepsSobolev m η fW)]
  have hAE := (cepsScaledSurrogateHalfEntrance_differentiableOn dom hW hθ hD hf hη
    (M := cepsSobolev m η fW) N hN lam hlam hz).analyticAt (ball_mem_nhds _ hEA)
  exact analyticAt_completePair hAE (analyticAt_slice_fst_on_polydisc hB hAB)
    (analyticAt_slice_fst_on_polydisc hB hAD) lam z

include dom hW hθ hD in
theorem cepsKernelHalfPairJetModel_cepsJet_analyticAt_zero (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (cepsKernelHalfPairJetModel (cepsJet f) N lam z) 0 := by
  obtain ⟨B, hB, hFB, hFE⟩ := cepsKernelHalfFactors_cepsJet_frequency_neighborhood dom hW hθ hD hfW N lam hlam hz
  have hFD := differentiableOn_deriv_snd (isOpen_ball.prod isOpen_ball) hFB
  exact analyticAt_completePair (analyticAt_slice_fst_on_polydisc hB hFE)
    (analyticAt_slice_fst_on_polydisc hB hFB) (analyticAt_slice_fst_on_polydisc hB hFD) lam z

include hθ hD in
theorem cepsKernelPairJetModel_cepsJet_analyticAt_zero :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → (lam ≠ 0 ∨ z ≠ 0) →
        AnalyticAt ℂ (cepsKernelPairJetModel (cepsJet f) N lam z) 0 := by
  obtain ⟨r, hr, he⟩ := cepsKernelFiniteFactors_cepsJet_frequency_neighborhood hθ hD dom
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz hne
  obtain ⟨B, hB, hFB, hFE⟩ := he hW hfW hneg hη hf hfS hηc hclose N hN lam hz hne
  have hFD := differentiableOn_deriv_snd (isOpen_ball.prod isOpen_ball) hFB
  exact analyticAt_completePair (analyticAt_slice_fst_on_polydisc hB hFE)
    (analyticAt_slice_fst_on_polydisc hB hFB) (analyticAt_slice_fst_on_polydisc hB hFD) lam z

end PGM
