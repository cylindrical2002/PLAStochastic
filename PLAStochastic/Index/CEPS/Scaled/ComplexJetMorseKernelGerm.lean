import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseKernelDefs

/-! # Joint analyticity of the signed Morse energy, frequency and nodes at the origin -/

noncomputable section
open Complex Filter Topology
namespace PGM

theorem cepsComplexJetMorseEnergy_analyticAt {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) :
    AnalyticAt ℂ (cepsComplexJetMorseEnergy d N η) (((p₀, 0), 0), 0) := by
  let v : CepsComplexJetMorseParam d × ℂ := (((p₀, 0), 0), 0)
  have hp : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.1.1) v :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hl : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.1.2) v :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hb : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.2) v :=
    analyticAt_snd.comp analyticAt_fst
  have hU₀ : AnalyticAt ℂ (cepsComplexCgfJetMinimumUnit d N η) (p₀, (0 : ℂ) * 0) := by
    simpa only [zero_mul] using cepsComplexCgfJetMinimumUnit_analyticAt hη
  have hU := hU₀.comp (x := v)
    (f := fun u : CepsComplexJetMorseParam d × ℂ => (u.1.1.1, u.1.2 * u.1.1.2))
    (hp.prod (hb.mul hl))
  exact (analyticAt_snd.pow 2).add ((hl.pow 2).mul hU)

theorem cepsComplexJetMorseFrequency_analyticAt {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) :
    AnalyticAt ℂ (cepsComplexJetMorseFrequency d N η) (((p₀, 0), 0), 0) := by
  have hw : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => 1 + u.1.2 * u.1.1.2)
      (((p₀, 0), 0), 0) :=
    analyticAt_const.add ((analyticAt_snd.comp analyticAt_fst).mul
      (analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)))
  exact (cepsComplexJetMorseEnergy_analyticAt hη).div hw (by simp)

theorem cepsComplexJetMorseNode_analyticAt {d : ℕ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0)) (sgn : ℂ) :
    AnalyticAt ℂ (cepsComplexJetMorseNode d Θ sgn) (((p₀, 0), 0), 0) := by
  let v : CepsComplexJetMorseParam d × ℂ := (((p₀, 0), 0), 0)
  have hp : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.1.1) v :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hl : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.1.2) v :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hb : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ => u.1.2) v :=
    analyticAt_snd.comp analyticAt_fst
  have hm : AnalyticAt ℂ (fun u : CepsComplexJetMorseParam d × ℂ =>
      (((u.1.1.1, u.1.1.2), sgn * u.2), u.1.2)) v :=
    ((hp.prod hl).prod (analyticAt_const.mul analyticAt_snd)).prod hb
  have hΨ : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ =>
      cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2)
      (((p₀, 0), sgn * 0), 0) := by
    simpa only [mul_zero] using cepsComplexJetMorseScaleRoot_analyticAt hΘ 0 0
  have h := hΨ.comp (x := v)
    (f := fun u : CepsComplexJetMorseParam d × ℂ => (((u.1.1.1, u.1.1.2), sgn * u.2), u.1.2)) hm
  simpa only [v, mul_zero] using! h

theorem cepsComplexJetMorseNode_zero {d : ℕ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0)) (sgn : ℂ) :
    cepsComplexJetMorseNode d Θ sgn (((p₀, 0), 0), 0) = 0 := by
  simp only [cepsComplexJetMorseNode, mul_zero, cepsComplexJetMorseScaleRoot_zero_fderiv hΘ]
  exact (fderiv ℂ Θ ((p₀, 0), 0)).map_zero

end PGM
