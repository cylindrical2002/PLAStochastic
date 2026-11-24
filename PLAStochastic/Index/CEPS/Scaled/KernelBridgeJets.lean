import PLAStochastic.Index.CEPS.Scaled.KernelFiniteSlopeJets
import PLAStochastic.Index.CEPS.Scaled.SurrogateBridge
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorJetDivision

/-! # Exact finite mixed-jet coefficients of the actual surrogate bridge -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateBridge_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → ∀ j ≤ N,
        coeff j (complexTaylorSeries (cepsScaledSurrogateBridge dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelBridgeJetModel (cepsJet f) N lam z) 0) := by
  obtain ⟨rG, hrG, heG⟩ := cepsScaledSurrogateG_root_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rS, hrS, heS⟩ := cepsScaledSurrogate_finite_slope_jets dom hθ hD
  refine ⟨min rG rS, lt_min hrG hrS, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz
  have hcloseG := hclose.trans (min_le_left rG rS)
  have hcloseS := hclose.trans (min_le_right rG rS)
  have heP := heG hW hfW hneg hη hf hfS hηc hcloseG N hN lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have heM := heG hW hfW hneg hη hf hfS hηc hcloseG N hN lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have heD := (heS hW hfW hneg hη hf hfS hηc hcloseS N hN lam hz).1
  have hRP := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (1 : ℂ) ^ 2 = 1)
  have hRM := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz (by norm_num : (-1 : ℂ) ^ 2 = 1)
  have hMP := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z 1 N).analyticAt 0
  have hMM := (cepsCumulantRootModel_differentiable (cepsJet f) N lam z (-1) N).analyticAt 0
  have hGP := cepsScaledSurrogateG_curve_analyticAt dom hW hθ hD hfS hηc N (by omega) lam hz hRP
  have hGM := cepsScaledSurrogateG_curve_analyticAt dom hW hθ hD hfS hηc N (by omega) lam hz hRM
  have hGMP := cepsKernelGJetModel_curve_analyticAt (cepsJet f) N lam z hMP
  have hGMM := cepsKernelGJetModel_curve_analyticAt (cepsJet f) N lam z hMM
  have heNeg := complexTaylorSeries_coeff_eq_composition hGP hGMP (F := fun x : ℂ => -x)
    (by fun_prop) N heP
  have heNum := complexTaylorSeries_coeff_eq_mul hGP.neg hGM hGMP.neg hGMM N heNeg heM
  have hRadius := surrogateRegularScaleRadius_pos dom hW hθ hD N (cepsSobolev m η fW) lam z
  have hDA := (cepsScaledSurrogateDenominator_differentiableOn dom hW hθ hD hfS hηc
    le_rfl N (by omega) lam hz).analyticAt (ball_mem_nhds _ hRadius)
  have hDM := (cepsKernelFiniteSlopes_analyticAt (cepsJet f) N lam z).1
  have hD0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hfS hηc le_rfl N (by omega)
    lam hz (mem_ball_self hRadius)
  exact complexTaylorSeries_coeff_eq_div (hGP.neg.mul hGM) hDA (hGMP.neg.mul hGMM) hDM
    hD0 N heNum heD

end PGM
