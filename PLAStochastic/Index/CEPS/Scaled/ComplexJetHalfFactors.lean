import PLAStochastic.Index.CEPS.Scaled.ComplexJetFactors
import PLAStochastic.Index.CEPS.Scaled.KernelHalfFactors

/-! # Genuine complex finite-jet half-line factors and marked endpoint germs -/

noncomputable section
open Complex Set
namespace PGM

def cepsComplexKernelHalfEntranceJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp (cepsCanonComplexJetPolynomial p N (b * lam)
    (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) /
      (cepsComplexCumulantJetQuotient p N lam z b (b * z) *
        (b * z - cepsComplexCumulantRootModel p N lam z (-1) N b))

def cepsComplexKernelHalfBridgeJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  (cepsComplexCumulantRootModel p N lam z 1 N b -
    cepsComplexCumulantRootModel p N lam z (-1) N b) *
      cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z 1 N b)

def cepsComplexKernelMarkedEndpointJetModel (p : ℕ → ℂ) (N : ℕ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b)) *
    exp (cepsCanonComplexJetPolynomial p N b (cepsComplexScaledDiscount 1 z b) (b ^ 2 * z)) *
      cepsComplexKernelHalfEntranceJetModel p N 1 z b * cepsComplexKernelHalfBridgeJetModel p N 1 z b

theorem cepsComplexKernelHalfFactors_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsComplexKernelHalfEntranceJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelHalfEntranceJetModel p N lam z b ∧
    cepsComplexKernelHalfBridgeJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelHalfBridgeJetModel p N lam z b ∧
    cepsComplexKernelMarkedEndpointJetModel (fun i => (p i : ℂ)) N z b =
      cepsKernelMarkedEndpointJetModel p N z b := by
  simp only [cepsComplexKernelHalfEntranceJetModel, cepsKernelHalfEntranceJetModel,
    cepsComplexKernelHalfBridgeJetModel, cepsKernelHalfBridgeJetModel,
    cepsComplexKernelMarkedEndpointJetModel, cepsKernelMarkedEndpointJetModel,
    cepsComplexCumulantRootModel_real, cepsComplexKernelGJetModel_real,
    cepsCanonComplexJetPolynomial_real, cepsComplexCumulantJetQuotient_real, and_self]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cepsComplexKernelHalfFactors_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hc : CepsComplexJetRootChart (p x) lam (z x))
    (hquot : cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (b x * z x) ≠ 0)
    (hmark : b x * z x - cepsComplexCumulantRootModel (p x) N lam (z x) (-1) N (b x) ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelHalfEntranceJetModel (p u) N lam (z u) (b u)) x ∧
    AnalyticAt ℂ (fun u => cepsComplexKernelHalfBridgeJetModel (p u) N lam (z u) (b u)) x := by
  have hM := cepsComplexCumulantRootModel_analyticAt (fun i => hp i x hx) (hb x hx) (hz x hx)
    N lam (-1) hc.variance_ne hc.variance_chart hc.frequency_chart hc.gap_minus_ne N
  have hP := cepsComplexCumulantRootModel_analyticAt (fun i => hp i x hx) (hb x hx) (hz x hx)
    N lam 1 hc.variance_ne hc.variance_chart hc.frequency_chart hc.gap_plus_ne N
  have hG := cepsComplexKernelGJetModel_curve_analyticAt hU hx N lam hp hb hz hc hP
  have hμ : AnalyticAt ℂ (fun u => b u * lam) x := (hb x hx).mul analyticAt_const
  have hq : AnalyticAt ℂ (fun u => cepsComplexScaledDiscount lam (z u) (b u)) x := by
    unfold cepsComplexScaledDiscount
    exact (((hb x hx).pow 2).mul (hz x hx)).mul
      (analyticAt_const.add ((hb x hx).mul analyticAt_const))
  have hζ : AnalyticAt ℂ (fun u => b u ^ 2 * z u) x := ((hb x hx).pow 2).mul (hz x hx)
  have hL := (cepsCanonComplexJetPolynomial_analyticAt (fun i => hp i x hx) hμ hq hζ N).cexp
  have hQ := cepsComplexCumulantJetQuotient_analyticAt hU hx hp hb hz
    ((hb x hx).mul (hz x hx)) N lam hc.variance_ne hc.variance_chart hc.frequency_chart
      hc.gap_plus_ne hc.gap_minus_ne
  exact ⟨hL.div (hQ.mul (((hb x hx).mul (hz x hx)).sub hM)) (mul_ne_zero hquot hmark),
    (hP.sub hM).mul hG⟩

/-- The positive half-line has a nonzero marker denominator at zero scale for every
positive-variance real input vector and every right-half-plane frequency. -/
theorem cepsComplexKernelHalfFactors_real_zero_denominators
    (p : ℕ → ℝ) (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (z : ℂ) :
    cepsComplexCumulantJetQuotient (fun i => (p i : ℂ)) N lam z 0 (0 * z) ≠ 0 ∧
    0 * z - cepsComplexCumulantRootModel (fun i => (p i : ℂ)) N lam z (-1) N 0 ≠ 0 := by
  constructor
  · rw [cepsComplexCumulantJetQuotient_real, cepsCumulantJetQuotient_zero]
    exact div_ne_zero (by exact_mod_cast hp.ne') (by norm_num)
  · rw [cepsComplexCumulantRootModel_real,
      cepsCumulantRootModel_zero p hp.ne' N lam z (-1) (by norm_num) N, zero_mul, zero_sub]
    exact neg_ne_zero.mpr (cepsCumulantRootBase_minus_ne_zero p hp hlam z)

theorem cepsComplexKernelMarkedEndpointJetModel_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hc : CepsComplexJetRootChart (p x) 1 (z x))
    (hquot : cepsComplexCumulantJetQuotient (p x) N 1 (z x) (b x) (b x * z x) ≠ 0)
    (hmark : b x * z x - cepsComplexCumulantRootModel (p x) N 1 (z x) (-1) N (b x) ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelMarkedEndpointJetModel (p u) N (z u) (b u)) x := by
  have hf := cepsComplexKernelHalfFactors_analyticAt hU hx N 1 hp hb hz hc hquot hmark
  have hq : AnalyticAt ℂ (fun u => cepsComplexScaledDiscount 1 (z u) (b u)) x := by
    unfold cepsComplexScaledDiscount
    exact (((hb x hx).pow 2).mul (hz x hx)).mul
      (analyticAt_const.add ((hb x hx).mul analyticAt_const))
  have hL := (cepsCanonComplexJetPolynomial_analyticAt (fun i => hp i x hx) (hb x hx) hq
    (((hb x hx).pow 2).mul (hz x hx)) N).cexp
  exact (((((hb x hx).mul (hz x hx)).mul (analyticAt_const.add (hb x hx))).cexp.mul hL).mul hf.1).mul hf.2

end PGM
