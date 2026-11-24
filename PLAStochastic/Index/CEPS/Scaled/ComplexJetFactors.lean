import PLAStochastic.Index.CEPS.Scaled.ComplexJetKernelLift
import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootDomain
import PLAStochastic.Index.CEPS.Scaled.KernelDenominatorZero

/-! # Genuine complex finite-jet bridge and entrance parameter germs -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

def cepsComplexKernelDenominatorJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  dslope (cepsComplexKernelGJetModel p N lam z b)
    (cepsComplexCumulantRootModel p N lam z (-1) N b)
    (cepsComplexCumulantRootModel p N lam z 1 N b)

def cepsComplexKernelEntranceSlopeJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  dslope (dslope (cepsComplexKernelGJetModel p N lam z b)
    (cepsComplexCumulantRootModel p N lam z (-1) N b))
    (cepsComplexCumulantRootModel p N lam z 1 N b) (b * z)

def cepsComplexKernelBridgeJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  -cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z 1 N b) *
    cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z (-1) N b) /
      cepsComplexKernelDenominatorJetModel p N lam z b

def cepsComplexKernelEntranceJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  -exp (cepsCanonComplexJetPolynomial p N (b * lam)
    (cepsComplexScaledDiscount lam z b) (b ^ 2 * z)) *
    cepsComplexKernelEntranceSlopeJetModel p N lam z b /
      (cepsComplexCumulantJetQuotient p N lam z b (b * z) *
        cepsComplexKernelDenominatorJetModel p N lam z b)

theorem cepsComplexKernelFiniteFactors_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsComplexKernelDenominatorJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelDenominatorJetModel p N lam z b ∧
    cepsComplexKernelEntranceSlopeJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelEntranceSlopeJetModel p N lam z b ∧
    cepsComplexKernelBridgeJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelBridgeJetModel p N lam z b ∧
    cepsComplexKernelEntranceJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelEntranceJetModel p N lam z b := by
  have hG : cepsComplexKernelGJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelGJetModel p N lam z b := by
    funext ξ; exact cepsComplexKernelGJetModel_real p N lam z b ξ
  simp only [cepsComplexKernelDenominatorJetModel, cepsKernelDenominatorJetModel,
    cepsComplexKernelEntranceSlopeJetModel, cepsKernelEntranceSlopeJetModel,
    cepsComplexKernelBridgeJetModel, cepsKernelBridgeJetModel,
    cepsComplexKernelEntranceJetModel, cepsKernelEntranceJetModel,
    cepsComplexCumulantRootModel_real, hG, cepsCanonComplexJetPolynomial_real,
    cepsComplexCumulantJetQuotient_real, and_self]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem cepsComplexKernelGJetModel_curve_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z ξ : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hchart : CepsComplexJetRootChart (p x) lam (z x)) (hξ : AnalyticAt ℂ ξ x) :
    AnalyticAt ℂ (fun u => cepsComplexKernelGJetModel (p u) N lam (z u) (b u) (ξ u)) x := by
  have hQ := cepsComplexCumulantJetQuotient_analyticAt hU hx hp hb hz hξ N lam
    hchart.variance_ne hchart.variance_chart hchart.frequency_chart
      hchart.gap_plus_ne hchart.gap_minus_ne
  have hμ : AnalyticAt ℂ (fun u => b u * lam) x := (hb x hx).mul analyticAt_const
  have hq : AnalyticAt ℂ (fun u => cepsComplexScaledDiscount lam (z u) (b u)) x := by
    unfold cepsComplexScaledDiscount
    exact (((hb x hx).pow 2).mul (hz x hx)).mul
      (analyticAt_const.add ((hb x hx).mul analyticAt_const))
  have hL := cepsCanonComplexJetPolynomial_analyticAt (fun i => hp i x hx) hμ hq
    ((hb x hx).mul hξ) N
  exact (hξ.neg.mul (analyticAt_const.add ((hb x hx).mul analyticAt_const))).cexp.mul
    (hQ.mul ((analyticAt_const.mul hL).cexp))

theorem cepsComplexKernelFiniteSlopes_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hchart : ∀ u ∈ U, CepsComplexJetRootChart (p u) lam (z u)) :
    AnalyticAt ℂ (fun u => cepsComplexKernelDenominatorJetModel (p u) N lam (z u) (b u)) x ∧
    AnalyticAt ℂ (fun u => cepsComplexKernelEntranceSlopeJetModel (p u) N lam (z u) (b u)) x := by
  have hc := hchart x hx
  have hM := cepsComplexCumulantRootModel_analyticAt (fun i => hp i x hx) (hb x hx) (hz x hx)
    N lam (-1) hc.variance_ne hc.variance_chart hc.frequency_chart hc.gap_minus_ne N
  have hP := cepsComplexCumulantRootModel_analyticAt (fun i => hp i x hx) (hb x hx) (hz x hx)
    N lam 1 hc.variance_ne hc.variance_chart hc.frequency_chart hc.gap_plus_ne N
  exact cepsComplexKernelGJetModel_moving_slopes_analyticAt hU hx N lam hp hb hz hchart hM hP
    ((hb x hx).mul (hz x hx))

/-- Both complete factors are genuine parameter germs. Denominator assumptions refer only
to the center; continuity then supplies actual neighborhoods. -/
theorem cepsComplexKernelFiniteFactors_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hchart : ∀ u ∈ U, CepsComplexJetRootChart (p u) lam (z u))
    (hden : cepsComplexKernelDenominatorJetModel (p x) N lam (z x) (b x) ≠ 0)
    (hquot : cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (b x * z x) ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelBridgeJetModel (p u) N lam (z u) (b u)) x ∧
    AnalyticAt ℂ (fun u => cepsComplexKernelEntranceJetModel (p u) N lam (z u) (b u)) x := by
  have hc := hchart x hx
  have hM := cepsComplexCumulantRootModel_analyticAt (fun i => hp i x hx) (hb x hx) (hz x hx)
    N lam (-1) hc.variance_ne hc.variance_chart hc.frequency_chart hc.gap_minus_ne N
  have hP := cepsComplexCumulantRootModel_analyticAt (fun i => hp i x hx) (hb x hx) (hz x hx)
    N lam 1 hc.variance_ne hc.variance_chart hc.frequency_chart hc.gap_plus_ne N
  have hGM := cepsComplexKernelGJetModel_curve_analyticAt hU hx N lam hp hb hz hc hM
  have hGP := cepsComplexKernelGJetModel_curve_analyticAt hU hx N lam hp hb hz hc hP
  have hs := cepsComplexKernelFiniteSlopes_analyticAt hU hx N lam hp hb hz hchart
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
  exact ⟨(hGP.neg.mul hGM).div hs.1 hden,
    (hL.neg.mul hs.2).div (hQ.mul hs.1) (mul_ne_zero hquot hden)⟩

/-- Every positive-variance real jet center pays the two complexified denominators at
zero scale, independently of law realization. -/
theorem cepsComplexKernelFiniteFactors_real_zero_denominators
    (p : ℕ → ℝ) (hp : 0 < p (cepsJetCode (.inl 0))) (N : ℕ) (lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) :
    cepsComplexKernelDenominatorJetModel (fun i => (p i : ℂ)) N lam z 0 ≠ 0 ∧
    cepsComplexCumulantJetQuotient (fun i => (p i : ℂ)) N lam z 0 (0 * z) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [(cepsComplexKernelFiniteFactors_real p N lam z 0).1]
    exact cepsKernelDenominatorJetModel_zero_ne p hp N lam hz
  · rw [cepsComplexCumulantJetQuotient_real, cepsCumulantJetQuotient_zero]
    exact div_ne_zero (by exact_mod_cast hp.ne') (by norm_num)

/-- A center root chart suffices: the neighboring chart and both nonzero factor
denominators are supplied by genuine analytic germs. -/
theorem cepsComplexKernelFiniteFactors_germ
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (hchart : CepsComplexJetRootChart (p x) lam (z x))
    (hden : cepsComplexKernelDenominatorJetModel (p x) N lam (z x) (b x) ≠ 0)
    (hquot : cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (b x * z x) ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelBridgeJetModel (p u) N lam (z u) (b u)) x ∧
    AnalyticAt ℂ (fun u => cepsComplexKernelEntranceJetModel (p u) N lam (z u) (b u)) x := by
  have he := hchart.eventually (fun i => hp i x hx) (hz x hx)
  have hnear : ∀ᶠ u in 𝓝 x, u ∈ U ∧ CepsComplexJetRootChart (p u) lam (z u) :=
    (show ∀ᶠ u in 𝓝 x, u ∈ U from hU.mem_nhds hx).and he
  obtain ⟨V, hV, hVo, hxV⟩ := mem_nhds_iff.mp hnear
  exact cepsComplexKernelFiniteFactors_analyticAt hVo hxV N lam
    (fun i => (hp i).mono (fun u hu => (hV hu).1))
    (hb.mono (fun u hu => (hV hu).1)) (hz.mono (fun u hu => (hV hu).1))
    (fun u hu => (hV hu).2) hden hquot

/-- Positive-variance real centers require no extra root-chart or denominator premises. -/
theorem cepsComplexKernelFiniteFactors_germ_real_zero
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticOnNhd ℂ z U)
    (p₀ : ℕ → ℝ) (hp₀ : 0 < p₀ (cepsJetCode (.inl 0)))
    (he : p x = fun i => (p₀ i : ℂ)) (hb₀ : b x = 0)
    (hz₀ : 0 ≤ (z x).re) (hne : lam ≠ 0 ∨ z x ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelBridgeJetModel (p u) N lam (z u) (b u)) x ∧
    AnalyticAt ℂ (fun u => cepsComplexKernelEntranceJetModel (p u) N lam (z u) (b u)) x := by
  have hc : CepsComplexJetRootChart (p x) lam (z x) := by
    rw [he]
    exact cepsComplexJetRootChart_real p₀ hp₀ lam hz₀ hne
  have hd := cepsComplexKernelFiniteFactors_real_zero_denominators p₀ hp₀ N lam hz₀
  exact cepsComplexKernelFiniteFactors_germ hU hx N lam hp hb hz hc
    (by simpa only [he, hb₀] using hd.1) (by simpa only [he, hb₀] using hd.2)

end PGM
