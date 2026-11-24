import PLAStochastic.Index.CEPS.Scaled.KernelHalfFactors
import PLAStochastic.Index.CEPS.Scaled.KernelEntranceJets
import PLAStochastic.Index.CEPS.Scaled.SurrogateHalfEntranceBudget
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridgeCorrection
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetLinear

/-! # Exact finite mixed-jet coefficients of the positive half-line subtraction -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateHalfFactors_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re →
      (∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledSurrogateHalfBridge dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelHalfBridgeJetModel (cepsJet f) N lam z) 0)) ∧
      (1 ≤ lam → ∀ j ≤ N, coeff j (complexTaylorSeries (cepsScaledSurrogateHalfEntrance dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelHalfEntranceJetModel (cepsJet f) N lam z) 0)) := by
  obtain ⟨rL, hrL, heL⟩ := cepsCanonDriftTaylor_taylorJets_eq_jetPolynomial dom hθ hD
  obtain ⟨rG, hrG, heG⟩ := cepsScaledSurrogateG_root_taylorJets_eq_finite_model dom hθ hD
  refine ⟨min rL rG, lt_min hrL hrG, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz
  have hRP := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hRM := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have hMP := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z 1 N).analyticAt 0
  have hMM := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z (-1) N).analyticAt 0
  have heRP := cepsScaledSignedRoot_taylorJets_eq_finite_model dom hW hθ hD hfW N lam hz
    (by norm_num : (1 : ℂ) ^ 2 = 1)
  have heRM := cepsScaledSignedRoot_taylorJets_eq_finite_model dom hW hθ hD hfW N lam hz
    (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have heGap := complexTaylorSeries_coeff_eq_sub hRP hRM hMP hMM N heRP heRM
  have hGP := cepsScaledSurrogateG_curve_analyticAt dom hW hθ hD hfS hηc N (by omega) lam hz hRP
  have hGMP := cepsKernelGJetModel_curve_analyticAt (cepsJet f) N lam z hMP
  have heGP := heG hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_right rL rG)) N hN lam hz
    (by norm_num : (1 : ℂ) ^ 2 = 1)
  refine ⟨complexTaylorSeries_coeff_eq_mul (hRP.sub hRM) hGP (hMP.sub hMM) hGMP N heGap heGP, ?_⟩
  intro hlam
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by unfold cepsComplexScaledDiscount; fun_prop
  have hζ : AnalyticAt ℂ (fun b : ℂ => b ^ 2 * z) 0 := by fun_prop
  have hLA := cepsCanonDriftTaylor_curve_analyticAt dom hW hθ hD hfS hηc N (by omega)
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have hLM := cepsCanonJetPolynomial_curve_analyticAt (cepsJet f) N hμ hq hζ
  have heLc := heL hW hfW hneg hη hf hfS hηc (hclose.trans (min_le_left rL rG)) N hN
    hμ hq hζ (by simp [cepsComplexScaledDiscount]) (by simp)
  have heExp := complexTaylorSeries_coeff_eq_composition hLA hLM (F := exp) (by fun_prop) N heLc
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  have heMarkGap := complexTaylorSeries_coeff_eq_sub hmark hRM hmark hMM N (fun _ _ => rfl) heRM
  have hQA := cepsMarkedQuotient_analyticAt_and_finite_jets dom hW hθ hD hfW N lam hz
  have hQM := cepsCumulantJetQuotient_curve_analyticAt (cepsJet f) N lam z hmark
  have heDen := complexTaylorSeries_coeff_eq_mul hQA.1 (hmark.sub hRM) hQM (hmark.sub hMM) N hQA.2 heMarkGap
  have hER := (entranceScale_constants dom hW hθ hD N 0 lam z).1
  have hQb := (cepsScaledSurrogateMarkQuotient_budget dom hW hθ hD N 0 lam hz).2 0 (mem_ball_self hER)
  have hQ0 : cepsQ D θ ρW (0 * lam) (cepsComplexScaledDiscount lam z 0) (0 ^ 2 * z) ≠ 0 :=
    norm_pos_iff.mp ((by positivity [cepsVarLo_pos hD] : 0 < cepsVarLo D / 4).trans_le hQb)
  have hPR : 0 < dom.pairPolynomialScaleBase N 0 / (1 + |lam| + Real.sqrt ‖z‖) := by
    positivity [pairPolynomialScaleBase_pos dom hW hθ hD N 0]
  have hGb := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD N 0 lam hlam hz (mem_ball_self hPR)
  have hGap0 : 0 * z - cepsScaledSignedRoot D θ ρW lam z (-1) 0 ≠ 0 :=
    norm_pos_iff.mp ((positiveMarkerGapLower_pos dom hW hθ hD).trans_le hGb)
  exact complexTaylorSeries_coeff_eq_div hLA.cexp (hQA.1.mul (hmark.sub hRM))
    hLM.cexp (hQM.mul (hmark.sub hMM)) (mul_ne_zero hQ0 hGap0) N heExp heDen

end PGM
