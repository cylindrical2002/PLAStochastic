import PLAStochastic.Index.CEPS.Scaled.QuotientUnitAnalytic
import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticSpatialBudget

/-! # The genuine spatial quotient unit has a uniform finite cumulant-jet error -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology Asymptotics
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledQuotientSpatialUnit_jet_budget (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) (z : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ {b ξ : ℂ}, b ∈ ball (0 : ℂ) B → ξ ∈ ball 0 R →
      ‖cepsScaledQuotientSpatialUnit ρW lam z b ξ -
        cepsCumulantQuotientSpatialUnit (cepsJet f) N lam z b ξ‖ ≤ C * ‖b‖ ^ (N + 1) := by
  have hH := (cepsCgfUnit_differentiableOn hW hθ hD).analyticAt
    (ball_mem_nhds _ (cepsCgfRadius_pos hD hθ))
  have hP := (cepsCgfJetPolynomial_differentiable (cepsJet f) N).analyticAt 0
  have he := cepsCgfJetPolynomial_cepsJet_isBigO hW hθ hD hfW N
  have he' : (fun s => cepsCgfUnit ρW s - cepsCgfJetPolynomial (cepsJet f) N s)
      =O[𝓝 (0 : ℂ)] (fun s => s ^ (N + 1)) := by
    simpa only [neg_sub] using he.neg_left
  exact quadraticSpatialUnit_difference_budget hH.continuousAt hP.continuousAt N he' lam z hR

end PGM
