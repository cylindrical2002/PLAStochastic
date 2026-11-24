import PLAStochastic.Index.CEPS.Scaled.ComplexJetKernel

/-! # Exact finite coordinate dependence of the complex cumulant and spatial kernels -/

noncomputable section
open Complex Finset
namespace PGM

def cepsComplexJetPad (d : ℕ) (p : Fin d → ℂ) (i : ℕ) : ℂ :=
  if h : i < d then p ⟨i, h⟩ else 0

theorem cepsComplexJetPad_apply {d i : ℕ} (p : Fin d → ℂ) (hi : i < d) :
    cepsComplexJetPad d p i = p ⟨i, hi⟩ := by simp [cepsComplexJetPad, hi]

theorem cepsComplexJetPad_continuous (d i : ℕ) :
    Continuous (fun p : Fin d → ℂ => cepsComplexJetPad d p i) := by
  by_cases hi : i < d
  · simp only [cepsComplexJetPad, dif_pos hi]
    exact continuous_apply _
  · simp only [cepsComplexJetPad, dif_neg hi]
    exact continuous_const

theorem cepsComplexJetPad_analyticAt (d i : ℕ) (p : Fin d → ℂ) :
    AnalyticAt ℂ (fun p : Fin d → ℂ => cepsComplexJetPad d p i) p := by
  by_cases hi : i < d
  · simp only [cepsComplexJetPad, dif_pos hi]
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d => ℂ) ⟨i, hi⟩).analyticAt _
  · simp only [cepsComplexJetPad, dif_neg hi]
    exact analyticAt_const

theorem cepsCgfComplexJetPolynomial_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) :
    cepsCgfComplexJetPolynomial p N = cepsCgfComplexJetPolynomial p' N := by
  funext s
  apply sum_congr rfl
  intro j hj
  rw [hp (cepsJetCode (.inl j)) (cepsJetCode_lt_cepsJetDim
    (by have := mem_range.mp hj; simp only [cepsJetWeight]; omega))]

theorem cepsCanonComplexJetPolynomial_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) :
    cepsCanonComplexJetPolynomial p N = cepsCanonComplexJetPolynomial p' N := by
  funext μ q ζ
  unfold cepsCanonComplexJetPolynomial
  apply sum_congr rfl
  intro j hj
  congr 1
  apply sum_congr rfl
  intro m hm
  congr 1
  apply sum_congr rfl
  intro n hn
  rw [hp (cepsJetCode (.inr (j, m, n))) (cepsJetCode_lt_cepsJetDim (by
    have := mem_range.mp hj; have := mem_range.mp hm; have := mem_range.mp hn
    simp only [cepsJetWeight]; omega))]

theorem cepsComplexCumulantRootBase_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z sign : ℂ) :
    cepsComplexCumulantRootBase p lam z sign = cepsComplexCumulantRootBase p' lam z sign := by
  have hv := hp (cepsJetCode (.inl 0)) (cepsJetCode_lt_cepsJetDim (by simp [cepsJetWeight]))
  simp only [cepsComplexCumulantRootBase, hv]

theorem cepsComplexCumulantRootModel_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z sign : ℂ) (k : ℕ) :
    cepsComplexCumulantRootModel p N lam z sign k = cepsComplexCumulantRootModel p' N lam z sign k := by
  have hv := hp (cepsJetCode (.inl 0)) (cepsJetCode_lt_cepsJetDim (by simp [cepsJetWeight]))
  have hg : cepsComplexCumulantRootGap p lam z sign = cepsComplexCumulantRootGap p' lam z sign := by
    simp only [cepsComplexCumulantRootGap, hv, cepsComplexCumulantRootBase_congr N hp lam z sign]
  induction k with
  | zero => funext b; exact cepsComplexCumulantRootBase_congr N hp lam z sign
  | succ k ih =>
    funext b
    simp only [cepsComplexCumulantRootModel, quadraticNewtonStep, ih, hg,
      cepsCgfComplexJetPolynomial_congr N hp]

theorem cepsComplexCumulantQuotientSpatialUnit_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z b : ℂ) :
    cepsComplexCumulantQuotientSpatialUnit p N lam z b =
      cepsComplexCumulantQuotientSpatialUnit p' N lam z b := by
  funext ξ
  simp only [cepsComplexCumulantQuotientSpatialUnit, cepsComplexCumulantQuadraticEquation,
    cepsCgfComplexJetPolynomial_congr N hp]

theorem cepsComplexCumulantJetQuotient_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim N → p i = p' i) (lam : ℝ) (z b : ℂ) :
    cepsComplexCumulantJetQuotient p N lam z b = cepsComplexCumulantJetQuotient p' N lam z b := by
  funext ξ
  simp only [cepsComplexCumulantJetQuotient, cepsComplexCumulantQuotientSpatialUnit_congr N hp,
    cepsComplexCumulantRootModel_congr N hp]

theorem cepsComplexKernelGJetModel_congr {p p' : ℕ → ℂ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (lam : ℝ) (z b : ℂ) :
    cepsComplexKernelGJetModel p N lam z b = cepsComplexKernelGJetModel p' N lam z b := by
  have hQ := cepsComplexCumulantJetQuotient_congr N
    (fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega : N ≤ 4 * N)))) lam z b
  funext ξ
  simp only [cepsComplexKernelGJetModel, hQ, cepsCanonComplexJetPolynomial_congr N hp]

end PGM
