import PLAStochastic.Index.CEPS.Scaled.KernelNormalModel
import PLAStochastic.Index.CEPS.Scaled.NormalSeriesConsistency
import PLAStochastic.Index.CEPS.Scaled.MeanSeriesConsistency

/-! # Exact genuine normal-transform and mean coefficients in finite input jets -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledNormalMeanSeries_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 3 ≤ m → ∀ {z : ℂ}, 0 ≤ z.re → ∀ j ≤ N,
        coeff j (cepsScaledNormalSeries dom ρW N z) =
          coeff j (cepsKernelNormalSeriesJetModel (cepsJet f) N z) ∧
        coeff j (cepsScaledMeanSeries dom ρW N) =
          coeff j (cepsKernelMeanSeriesJetModel (cepsJet f) N) := by
  obtain ⟨rE, hrE, heE⟩ := cepsScaledSurrogateMarkedEndpoint_taylorJets_eq_finite_model dom hθ hD
  obtain ⟨rI, hrI, heI⟩ := cepsScaledSurrogatePairIntegralCoeff_eq_finite_model dom hθ hD
  obtain ⟨rZ, hrZ, heZ⟩ := cepsScaledSurrogateZeroEndpoint_eq_jetPolynomial dom hθ hD
  refine ⟨min rE (min rI rZ), lt_min hrE (lt_min hrI hrZ), ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN z hz j hj
  have hcloseE := hclose.trans (min_le_left _ _)
  have hcloseI := (hclose.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hcloseZ := (hclose.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hEp := heE hW hfW hneg hη hf hfS hηc hcloseE N (by omega) hz j hj
  have hDs := cepsScaledMarkedDiscount_taylorJets_eq_finite_model hW hθ hD hfW N z
  have hIz (n : ℕ) (hn : n ≤ N + 1) :=
    (heI hW hfW hneg hη hf hfS hηc hcloseI (N + 1) (by omega) hz n hn).2
  have hI0 := (heI hW hfW hneg hη hf hfS hηc hcloseI (N + 1) (by omega)
    (by simp : 0 ≤ (0 : ℂ).re) j (by omega)).2
  have hZe := heZ hW hfW hneg hη hf hcloseZ N (by omega)
  constructor
  · simp only [cepsScaledNormalSeries, cepsKernelNormalSeriesJetModel, map_sub, coeff_mul]
    rw [hEp]
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hqj := Finset.mem_antidiagonal.mp hq
    simp only [cepsScaledPairIntegralSeries, coeff_mk]
    rw [hDs q.1 (by omega), hIz q.2 (by omega)]
  · simp only [cepsScaledMeanSeries, cepsKernelMeanSeriesJetModel, map_add,
      cepsScaledPairIntegralSeries, coeff_mk, hZe, hI0]

include hθ hD in
theorem cepsScaledNormalMeanCoefficients_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ j : ℕ, j + 3 ≤ m → ∀ {z : ℂ}, 0 ≤ z.re →
        cepsScaledNormalCoeff dom ρW j z = cepsKernelNormalCoeffJetModel (cepsJet f) j z ∧
        cepsScaledMeanCoeff dom ρW j = cepsKernelMeanCoeffJetModel (cepsJet f) j := by
  obtain ⟨r, hr, he⟩ := cepsScaledNormalMeanSeries_taylorJets_eq_finite_model dom hθ hD
  exact ⟨r, hr, fun hW hfW hneg hη hf hfS hηc hclose j hj z hz =>
    he hW hfW hneg hη hf hfS hηc hclose j hj hz j le_rfl⟩

end PGM
