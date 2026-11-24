import PLAStochastic.Index.CEPS.Scaled.KernelGSlopeJets
import PLAStochastic.Index.CEPS.Scaled.KernelFiniteFactors

/-! # Exact denominator and entrance second-slope coefficients from finite jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries Asymptotics
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogate_finite_slope_jets :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re →
      (∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledSurrogateDenominator dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelDenominatorJetModel (cepsJet f) N lam z) 0)) ∧
      (∀ j ≤ N, coeff j (complexTaylorSeries (fun b =>
        dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b)
          (cepsScaledSignedRoot D θ ρW lam z (-1) b))
            (cepsScaledSignedRoot D θ ρW lam z 1 b) (b * z)) 0) =
        coeff j (complexTaylorSeries (cepsKernelEntranceSlopeJetModel (cepsJet f) N lam z) 0)) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateG_moving_slopes_taylorJets_eq_finite_model dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz
  have hRm := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have hRp := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hRMm := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z (-1) N).analyticAt 0
  have hRMp := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z 1 N).analyticAt 0
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  have hmem : (fun b : ℂ => b * z - b * z) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) := by
    simpa only [sub_self] using (isBigO_zero (E' := ℂ) (fun b : ℂ => b ^ (N + 1)) (𝓝 0))
  exact he hW hfW hneg hη hf hfS hηc hclose N hN lam hz hRm hRp hmark hRMm hRMp hmark
    (cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz (by norm_num))
    (cepsCumulantRootModel_actual_isBigO_all dom hθ hD hW hfW N lam hz (by norm_num)) hmem

end PGM
