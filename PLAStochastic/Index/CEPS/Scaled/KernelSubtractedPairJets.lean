import PLAStochastic.Index.CEPS.Scaled.KernelPairAnalytic
import PLAStochastic.Index.CEPS.Scaled.SubtractedPairError

/-! # Exact complete subtracted pair coefficients in finitely many input jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateSubtractedPair_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re → (lam ≠ 0 ∨ z ≠ 0) → ∀ j ≤ N,
        coeff j (complexTaylorSeries (cepsScaledSurrogateSubtractedPair dom ρW N lam z) 0) =
        coeff j (complexTaylorSeries (cepsKernelSubtractedPairJetModel (cepsJet f) N lam z) 0) := by
  obtain ⟨rP, hrP, heP⟩ := cepsScaledSurrogatePair_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rH, hrH, heH⟩ := cepsScaledSurrogateHalfPair_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rA, hrA, heA⟩ := cepsKernelPairJetModel_cepsJet_analyticAt_zero dom hθ hD
  refine ⟨min rP (min rH rA), lt_min hrP (lt_min hrH hrA), ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz hne
  have hcloseP := hclose.trans (min_le_left _ _)
  have hcloseH := (hclose.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcloseA := (hclose.trans (min_le_right _ _)).trans (min_le_right _ _)
  have he := heP hW hfW hneg hη hf hfS hηc hcloseP N hN lam hz hne
  by_cases hlam : 1 ≤ lam
  · have hAP := cepsScaledSurrogatePair_analyticAt_zero dom hW hθ hD hfS hηc N (by omega) lam hz
    have hAH := cepsScaledSurrogateHalfPair_analyticAt_zero dom hW hθ hD hfS hηc N (by omega) lam hlam hz
    have hMP := heA hW hfW hneg hη hf hfS hηc hcloseA N hN lam hz hne
    have hMH := cepsKernelHalfPairJetModel_cepsJet_analyticAt_zero dom hW hθ hD hfW N lam hlam hz
    have ha : cepsScaledSurrogateSubtractedPair dom ρW N lam z =
        (fun b => cepsScaledSurrogatePair dom ρW N lam z b - cepsScaledSurrogateHalfPair dom ρW N lam z b) := by
      funext b; simp only [cepsScaledSurrogateSubtractedPair, if_pos hlam]
    have hm : cepsKernelSubtractedPairJetModel (cepsJet f) N lam z =
        (fun b => cepsKernelPairJetModel (cepsJet f) N lam z b - cepsKernelHalfPairJetModel (cepsJet f) N lam z b) := by
      funext b; simp only [cepsKernelSubtractedPairJetModel, if_pos hlam]
    rw [ha, hm]
    exact complexTaylorSeries_coeff_eq_sub hAP hAH hMP hMH N he
      (heH hW hfW hneg hη hf hfS hηc hcloseH N hN lam hlam hz)
  · have ha : cepsScaledSurrogateSubtractedPair dom ρW N lam z = cepsScaledSurrogatePair dom ρW N lam z := by
      funext b; simp only [cepsScaledSurrogateSubtractedPair, if_neg hlam]
    have hm : cepsKernelSubtractedPairJetModel (cepsJet f) N lam z = cepsKernelPairJetModel (cepsJet f) N lam z := by
      funext b; simp only [cepsKernelSubtractedPairJetModel, if_neg hlam, sub_zero]
    rw [ha, hm]
    exact he

end PGM
