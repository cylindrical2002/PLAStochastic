import PLAStochastic.Index.CEPS.Scaled.CanonJetCurves

/-! # A canonical root-curve model reading only finitely many input jets -/

noncomputable section
open Complex Set Metric MeasureTheory Finset Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

theorem cepsJetDim_monotone : Monotone cepsJetDim := by
  intro n k hnk
  apply Finset.sup_mono
  unfold cepsJetIdxBox
  apply Finset.union_subset_union
  · exact Finset.map_subset_map.mpr (Finset.range_mono (by omega))
  · apply Finset.map_subset_map.mpr
    exact Finset.product_subset_product
      (Finset.range_mono (by omega))
      (Finset.product_subset_product (Finset.range_mono (by omega)) (Finset.range_mono (by omega)))

def cepsCanonRootJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z sign b : ℂ) : ℂ :=
  cepsCanonJetPolynomial p N (b * lam) (cepsComplexScaledDiscount lam z b)
    (b * cepsCumulantRootModel p N lam z sign N b)

theorem cepsCanonRootJetModel_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (lam : ℝ) (z sign : ℂ) :
    cepsCanonRootJetModel p N lam z sign = cepsCanonRootJetModel p' N lam z sign := by
  have hr := cepsCumulantRootModel_congr N
    (fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega : N ≤ 4 * N)))) lam z sign N
  funext b
  simp only [cepsCanonRootJetModel, hr, cepsCanonJetPolynomial_congr N hp]

theorem cepsCanonRootJetModel_differentiable (p : ℕ → ℝ) (N : ℕ)
    (lam : ℝ) (z sign : ℂ) : Differentiable ℂ (cepsCanonRootJetModel p N lam z sign) := by
  unfold cepsCanonRootJetModel
  apply cepsCanonJetPolynomial_curve_differentiable
  · fun_prop
  · unfold cepsComplexScaledDiscount; fun_prop
  · exact differentiable_id.mul (cepsCumulantRootModel_differentiable p N lam z sign N)

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsCanonDriftTaylor_root_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z sign : ℂ}, 0 ≤ z.re → sign ^ 2 = 1 →
      ∀ j ≤ N, coeff j (complexTaylorSeries (fun b => cepsCanonDriftTaylor dom ρW N
        (b * lam) (cepsComplexScaledDiscount lam z b)
          (b * cepsScaledSignedRoot D θ ρW lam z sign b)) 0) =
        coeff j (complexTaylorSeries (cepsCanonRootJetModel (cepsJet f) N lam z sign) 0) := by
  obtain ⟨r, hr, he⟩ := cepsCanonDriftTaylor_taylorJets_eq_jetPolynomial dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z sign hz hsign j hj
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by
    unfold cepsComplexScaledDiscount; fun_prop
  have hroot := cepsScaledSignedRoot_analyticAt_zero dom hW hθ hD lam hz hsign
  have hζ : AnalyticAt ℂ (fun b => b * cepsScaledSignedRoot D θ ρW lam z sign b) 0 :=
    analyticAt_id.mul hroot
  exact (he hW hfW hneg hη hf hfS hηc hclose N hN hμ hq hζ
    (by simp [cepsComplexScaledDiscount]) (by simp) j hj).trans
      (cepsCanonJetPolynomial_rootModel_taylorJets dom hθ hD hW hfW N lam hz hsign j hj)

end PGM
