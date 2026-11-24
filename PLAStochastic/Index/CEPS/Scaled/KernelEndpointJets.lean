import PLAStochastic.Index.CEPS.Scaled.KernelHalfJets
import PLAStochastic.Index.CEPS.Scaled.KernelHalfModelAnalytic
import PLAStochastic.Index.CEPS.Scaled.EndpointSurrogate
import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceHolomorphy

/-! # Exact genuine marked endpoint Taylor coefficients from finite mixed jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateMarkedEndpoint_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ {z : ℂ}, 0 ≤ z.re → ∀ j ≤ N,
        coeff j (complexTaylorSeries (cepsScaledSurrogateMarkedEndpoint dom ρW N z) 0) =
        coeff j (complexTaylorSeries (cepsKernelMarkedEndpointJetModel (cepsJet f) N z) 0) := by
  obtain ⟨rL, hrL, heL⟩ := cepsCanonDriftTaylor_taylorJets_eq_jetPolynomial dom hθ hD
  obtain ⟨rH, hrH, heH⟩ := cepsScaledSurrogateHalfFactors_taylorJets_eq_finite_model dom hθ hD
  refine ⟨min rL rH, lt_min hrL hrH, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN z hz
  have hμ : AnalyticAt ℂ (fun b : ℂ => b) 0 := analyticAt_id
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount 1 z) 0 := by unfold cepsComplexScaledDiscount; fun_prop
  have hζ : AnalyticAt ℂ (fun b : ℂ => b ^ 2 * z) 0 := by fun_prop
  have hLA := cepsCanonDriftTaylor_curve_analyticAt dom hW hθ hD hfS hηc N (by omega)
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have hLM := cepsCanonJetPolynomial_curve_analyticAt (cepsJet f) N hμ hq hζ
  have heLc := heL hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_left rL rH)) N hN
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have heExp := complexTaylorSeries_coeff_eq_composition hLA hLM (F := exp) (by fun_prop) N heLc
  have heHS := heH hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_right rL rH)) N hN 1 hz
  have hExp : AnalyticAt ℂ (fun b : ℂ => exp ((b * z) * (1 + b))) 0 := by fun_prop
  have hPR : 0 < dom.pairPolynomialScaleBase N 0 / (1 + |(1 : ℝ)| + Real.sqrt ‖z‖) := by
    positivity [pairPolynomialScaleBase_pos dom hW hθ hD N 0]
  have hEA := (cepsScaledSurrogateHalfEntrance_differentiableOn dom hW hθ hD hfS hηc N (by omega)
    1 le_rfl hz (M := 0)).analyticAt (ball_mem_nhds _ hPR)
  have hEM := cepsKernelHalfEntranceJetModel_cepsJet_analyticAt dom hW hθ hD hfW N 1 le_rfl hz
  have hRP := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD 1 hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hRM := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD 1 hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have hGP := cepsScaledSurrogateG_curve_analyticAt dom hW hθ hD hfS hηc N (by omega) 1 hz hRP
  have hBA : AnalyticAt ℂ (cepsScaledSurrogateHalfBridge dom ρW N 1 z) 0 := (hRP.sub hRM).mul hGP
  have hBM := cepsKernelHalfBridgeJetModel_analyticAt (cepsJet f) N 1 z
  have heA := complexTaylorSeries_coeff_eq_mul hExp hLA.cexp hExp hLM.cexp N (fun _ _ => rfl) heExp
  have heB := complexTaylorSeries_coeff_eq_mul (hExp.mul hLA.cexp) hEA (hExp.mul hLM.cexp) hEM N heA (heHS.2 le_rfl)
  exact complexTaylorSeries_coeff_eq_mul ((hExp.mul hLA.cexp).mul hEA) hBA
    ((hExp.mul hLM.cexp).mul hEM) hBM N heB heHS.1

end PGM
