import PLAStochastic.Index.CEPS.Scaled.ComplexJetHalfFactors
import PLAStochastic.Index.CEPS.Scaled.KernelPairModel
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricTimeOperator

/-! # Genuine finite complex-jet complete and subtracted time-operator pairs -/

noncomputable section
open Complex Set
namespace PGM

def cepsComplexKernelPairJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsComplexKernelEntranceJetModel p N lam z b) ^ 2 *
    (-(1 / (1 + b * lam)) * deriv (fun w => cepsComplexKernelBridgeJetModel p N lam w b) z -
      b * cepsComplexKernelBridgeJetModel p N lam z b)

def cepsComplexKernelHalfPairJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  exp ((b * z) * (1 + b * lam)) * (cepsComplexKernelHalfEntranceJetModel p N lam z b) ^ 2 *
    (-(1 / (1 + b * lam)) * deriv (fun w => cepsComplexKernelHalfBridgeJetModel p N lam w b) z -
      b * cepsComplexKernelHalfBridgeJetModel p N lam z b)

def cepsComplexKernelSubtractedPairJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsComplexKernelPairJetModel p N lam z b -
    if 1 ≤ lam then cepsComplexKernelHalfPairJetModel p N lam z b else 0

theorem cepsComplexKernelPairModels_real (p : ℕ → ℝ) (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsComplexKernelPairJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelPairJetModel p N lam z b ∧
    cepsComplexKernelHalfPairJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelHalfPairJetModel p N lam z b ∧
    cepsComplexKernelSubtractedPairJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelSubtractedPairJetModel p N lam z b := by
  have hB (w : ℂ) := (cepsComplexKernelFiniteFactors_real p N lam w b).2.2.1
  have hA := (cepsComplexKernelFiniteFactors_real p N lam z b).2.2.2
  have hHB (w : ℂ) := (cepsComplexKernelHalfFactors_real p N lam w b).2.1
  have hHA := (cepsComplexKernelHalfFactors_real p N lam z b).1
  have hp : cepsComplexKernelPairJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelPairJetModel p N lam z b := by
    simp only [cepsComplexKernelPairJetModel, cepsKernelPairJetModel, hB, hA]
  have hh : cepsComplexKernelHalfPairJetModel (fun i => (p i : ℂ)) N lam z b =
      cepsKernelHalfPairJetModel p N lam z b := by
    simp only [cepsComplexKernelHalfPairJetModel, cepsKernelHalfPairJetModel, hHB, hHA]
  exact ⟨hp, hh, by simp only [cepsComplexKernelSubtractedPairJetModel,
    cepsKernelSubtractedPairJetModel, hp, hh]⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The derivative in the complete pair is the actual frequency derivative. -/
theorem cepsComplexKernelPairJetModel_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticAt ℂ z x)
    (hc : CepsComplexJetRootChart (p x) lam (z x))
    (hden : cepsComplexKernelDenominatorJetModel (p x) N lam (z x) (b x) ≠ 0)
    (hquot : cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (b x * z x) ≠ 0)
    (hw : 1 + b x * lam ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelPairJetModel (p u) N lam (z u) (b u)) x := by
  have hf := cepsComplexKernelFiniteFactors_germ (U := U ×ˢ (univ : Set ℂ)) (hU.prod isOpen_univ)
    (x := (x, z x)) ⟨hx, mem_univ _⟩ N lam
    (p := fun v : E × ℂ => p v.1) (b := fun v : E × ℂ => b v.1) (z := Prod.snd)
    (fun i v hv => (hp i v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
    (fun v hv => (hb v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
    (fun _ _ => analyticAt_snd) hc hden hquot
  exact analyticAt_complete_parametric_time_pair
    (A := fun v : E × ℂ => cepsComplexKernelEntranceJetModel (p v.1) N lam v.2 (b v.1))
    (U := fun v : E × ℂ => cepsComplexKernelBridgeJetModel (p v.1) N lam v.2 (b v.1))
    (lam : ℂ) hf.2 hf.1 (hb x hx) hz hw

theorem cepsComplexKernelHalfPairJetModel_analyticAt
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticAt ℂ z x)
    (hc : CepsComplexJetRootChart (p x) lam (z x))
    (hquot : cepsComplexCumulantJetQuotient (p x) N lam (z x) (b x) (b x * z x) ≠ 0)
    (hmark : b x * z x - cepsComplexCumulantRootModel (p x) N lam (z x) (-1) N (b x) ≠ 0)
    (hw : 1 + b x * lam ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelHalfPairJetModel (p u) N lam (z u) (b u)) x := by
  have hf := cepsComplexKernelHalfFactors_analyticAt (U := U ×ˢ (univ : Set ℂ)) (hU.prod isOpen_univ)
    (x := (x, z x)) ⟨hx, mem_univ _⟩ N lam
    (p := fun v : E × ℂ => p v.1) (b := fun v : E × ℂ => b v.1) (z := Prod.snd)
    (fun i v hv => (hp i v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
    (fun v hv => (hb v.1 hv.1).comp (x := v) (f := Prod.fst) analyticAt_fst)
    (fun _ _ => analyticAt_snd) hc hquot hmark
  exact analyticAt_complete_parametric_time_pair
    (A := fun v : E × ℂ => cepsComplexKernelHalfEntranceJetModel (p v.1) N lam v.2 (b v.1))
    (U := fun v : E × ℂ => cepsComplexKernelHalfBridgeJetModel (p v.1) N lam v.2 (b v.1))
    (lam : ℂ) hf.1 hf.2 (hb x hx) hz hw

/-- At zero scale, every real positive-variance jet center has a genuine jointly analytic
subtracted-pair germ, with no law realization or extra denominator premise. -/
theorem cepsComplexKernelSubtractedPairJetModel_germ_real_zero
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) (N : ℕ) (lam : ℝ)
    {p : E → ℕ → ℂ} {b z : E → ℂ}
    (hp : ∀ i, AnalyticOnNhd ℂ (fun x => p x i) U)
    (hb : AnalyticOnNhd ℂ b U) (hz : AnalyticAt ℂ z x)
    (p₀ : ℕ → ℝ) (hp₀ : 0 < p₀ (cepsJetCode (.inl 0)))
    (he : p x = fun i => (p₀ i : ℂ)) (hb₀ : b x = 0)
    (hz₀ : 0 ≤ (z x).re) (hne : lam ≠ 0 ∨ z x ≠ 0) :
    AnalyticAt ℂ (fun u => cepsComplexKernelSubtractedPairJetModel (p u) N lam (z u) (b u)) x := by
  have hc : CepsComplexJetRootChart (p x) lam (z x) := by
    rw [he]; exact cepsComplexJetRootChart_real p₀ hp₀ lam hz₀ hne
  have hd := cepsComplexKernelFiniteFactors_real_zero_denominators p₀ hp₀ N lam hz₀
  have hP := cepsComplexKernelPairJetModel_analyticAt hU hx N lam hp hb hz hc
    (by simpa only [he, hb₀] using hd.1) (by simpa only [he, hb₀] using hd.2)
    (by simp [hb₀])
  by_cases hl : 1 ≤ lam
  · have hh := cepsComplexKernelHalfFactors_real_zero_denominators p₀ hp₀ N
      (lam := lam) (by linarith) (z x)
    have hH := cepsComplexKernelHalfPairJetModel_analyticAt hU hx N lam hp hb hz hc
      (by simpa only [he, hb₀] using hh.1) (by simpa only [he, hb₀] using hh.2)
      (by simp [hb₀])
    simpa only [cepsComplexKernelSubtractedPairJetModel, if_pos hl, Pi.sub_apply] using! hP.sub hH
  · simpa only [cepsComplexKernelSubtractedPairJetModel, if_neg hl, sub_zero] using hP

end PGM
