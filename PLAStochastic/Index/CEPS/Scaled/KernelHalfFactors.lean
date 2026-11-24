import PLAStochastic.Index.CEPS.Scaled.KernelFiniteFactors

/-! # Explicit finite mixed-jet half-line subtraction and marked endpoint -/

noncomputable section
open Complex PowerSeries
namespace PGM

def cepsKernelHalfEntranceJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp (cepsCanonJetPolynomial p N (b * lam) (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) /
    (cepsCumulantJetQuotient p N lam z b (b * z) * (b * z - cepsCumulantRootModel p N lam z (-1) N b))

def cepsKernelHalfBridgeJetModel (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  (cepsCumulantRootModel p N lam z 1 N b - cepsCumulantRootModel p N lam z (-1) N b) *
    cepsKernelGJetModel p N lam z b (cepsCumulantRootModel p N lam z 1 N b)

def cepsKernelMarkedEndpointJetModel (p : ℕ → ℝ) (N : ℕ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b)) * exp (cepsCanonJetPolynomial p N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z)) *
    cepsKernelHalfEntranceJetModel p N 1 z b * cepsKernelHalfBridgeJetModel p N 1 z b

theorem cepsKernelHalfFactors_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (lam : ℝ) (z : ℂ) :
    cepsKernelHalfEntranceJetModel p N lam z = cepsKernelHalfEntranceJetModel p' N lam z ∧
    cepsKernelHalfBridgeJetModel p N lam z = cepsKernelHalfBridgeJetModel p' N lam z ∧
    cepsKernelMarkedEndpointJetModel p N z = cepsKernelMarkedEndpointJetModel p' N z := by
  have hpN : ∀ i, i < cepsJetDim N → p i = p' i :=
    fun i hi => hp i (hi.trans_le (cepsJetDim_monotone (by omega : N ≤ 4 * N)))
  have hHalfE (lam : ℝ) : cepsKernelHalfEntranceJetModel p N lam z = cepsKernelHalfEntranceJetModel p' N lam z := by
    funext b
    simp only [cepsKernelHalfEntranceJetModel, cepsCanonJetPolynomial_congr N hp,
      cepsCumulantJetQuotient_congr N hpN, cepsCumulantRootModel_congr N hpN]
  have hHalfB (lam : ℝ) : cepsKernelHalfBridgeJetModel p N lam z = cepsKernelHalfBridgeJetModel p' N lam z := by
    funext b
    simp only [cepsKernelHalfBridgeJetModel, cepsKernelGJetModel_congr N hp lam z,
      cepsCumulantRootModel_congr N hpN]
  refine ⟨hHalfE lam, hHalfB lam, ?_⟩
  funext b
  simp only [cepsKernelMarkedEndpointJetModel, cepsCanonJetPolynomial_congr N hp, hHalfE 1, hHalfB 1]

theorem cepsKernelHalfBridgeJetModel_analyticAt (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (cepsKernelHalfBridgeJetModel p N lam z) 0 := by
  have hp := (cepsCumulantRootModel_differentiable p N lam z 1 N).analyticAt 0
  have hm := (cepsCumulantRootModel_differentiable p N lam z (-1) N).analyticAt 0
  exact (hp.sub hm).mul (cepsKernelGJetModel_curve_analyticAt p N lam z hp)

theorem cepsKernelHalfEntranceJetModel_analyticAt (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z : ℂ)
    (hVar : p (cepsJetCode (.inl 0)) ≠ 0) (hRoot : cepsCumulantRootModel p N lam z (-1) N 0 ≠ 0) :
    AnalyticAt ℂ (cepsKernelHalfEntranceJetModel p N lam z) 0 := by
  have hμ : AnalyticAt ℂ (fun b : ℂ => b * lam) 0 := by fun_prop
  have hq : AnalyticAt ℂ (cepsComplexScaledDiscount lam z) 0 := by unfold cepsComplexScaledDiscount; fun_prop
  have hζ : AnalyticAt ℂ (fun b : ℂ => b ^ 2 * z) 0 := by fun_prop
  have hL := (cepsCanonJetPolynomial_curve_analyticAt p N hμ hq hζ).cexp
  have hmark : AnalyticAt ℂ (fun b : ℂ => b * z) 0 := by fun_prop
  have hQ := cepsCumulantJetQuotient_curve_analyticAt p N lam z hmark
  have hRm := (cepsCumulantRootModel_differentiable p N lam z (-1) N).analyticAt 0
  have hQ0 : cepsCumulantJetQuotient p N lam z 0 (0 * z) ≠ 0 := by
    rw [cepsCumulantJetQuotient_zero]
    exact div_ne_zero (by exact_mod_cast hVar) (by norm_num)
  exact hL.div (hQ.mul (hmark.sub hRm)) (mul_ne_zero hQ0 (by simpa using neg_ne_zero.mpr hRoot))

end PGM
