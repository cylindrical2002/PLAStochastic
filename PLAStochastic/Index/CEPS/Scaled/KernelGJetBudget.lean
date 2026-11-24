import PLAStochastic.Index.CEPS.Scaled.KernelGJointJets
import PLAStochastic.ForMathlib.Analysis.Complex.UniformTaylorGerm

/-! # Uniform recovery of genuine scaled spatial kernel jets on fixed discs -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateG_spatial_jet_budget :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → ∀ {R : ℝ}, 0 < R →
      ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {b ξ : ℂ}, b ∈ ball (0 : ℂ) B → ξ ∈ ball 0 R →
        ‖cepsScaledSurrogateG dom ρW N lam z b ξ -
          cepsKernelGJetModel (cepsJet f) N lam z b ξ‖ ≤ C * ‖b‖ ^ (N + 1) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateG_curve_taylorJets_eq_finite_model dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz R hR
  exact exists_uniform_taylorJets_budget N hR
    (cepsScaledSurrogateG_fixedSpatial_differentiableOn_joint dom hW hθ hD hfS hηc N (by omega)
      lam hz (by positivity))
    (cepsKernelGJetModel_differentiableOn_joint (cepsJet f) N lam z (by positivity))
    (fun ξ => he hW hfW hneg hη hf hfS hηc hclose N hN lam hz (analyticAt_const (v := ξ)))

end PGM
