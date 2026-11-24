import PLAStochastic.Index.CEPS.Scaled.QuotientSpatialRecovery
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesGermCongr

/-! # Genuine marked quotient finite jets in the physical quadratic spatial scale -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include dom hW hθ hD in
theorem cepsMarkedQuotient_analyticAt_and_finite_jets (hfW : ∀ y, fW y = f (1 - y))
    (N : ℕ) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (fun b => cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) 0 ∧
    ∀ j ≤ N, coeff j (complexTaylorSeries
      (fun b => cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) 0) =
      coeff j (complexTaylorSeries (fun b => cepsCumulantJetQuotient (cepsJet f) N lam z b (b * z)) 0) := by
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  have ha := cepsScaledQuotient_curve_analyticAt dom hW hθ hD lam hz hmark
  have hev : (fun b => cepsScaledQuotient D θ ρW lam z b (b * (b * z))) =ᶠ[𝓝 (0 : ℂ)]
      (fun b => cepsQ D θ ρW (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (canonScaleRadius_pos dom hW hθ hD lam z)] with b hb
    rw [cepsScaledQuotient_eq_actual dom hW hθ hD lam hz hb]
    congr 1
    ring
  have he := cepsScaledQuotient_curve_taylorJets_eq_finite_model dom hW hθ hD hfW N lam hz hmark
  have hseries := complexTaylorSeries_eq_of_eventuallyEq hev
  exact ⟨ha.congr hev, fun j hj => (congrArg (coeff j) hseries).symm.trans (he j hj)⟩

end PGM
