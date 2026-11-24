import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseRoot
import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfMinimum
import PLAStochastic.Index.CEPS.Normal.ParametricDSlopeGerm

/-! # Actual removable scale division of finite-input signed Morse roots -/

noncomputable section
open Complex Filter Topology
namespace PGM

def cepsComplexJetMorseScaleRoot (d : ℕ) (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ)
    (p : Fin d → ℂ) (lam r b : ℂ) : ℂ :=
  dslope (fun t => Θ ((p, t * lam), t * r)) 0 b

theorem cepsComplexJetMorseScaleRoot_analyticAt {d : ℕ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0)) (lam r : ℂ) :
    AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ =>
      cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2) (((p₀, lam), r), 0) := by
  have hp : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => u.1.1.1)
      (((p₀, lam), r), 0) := analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hl : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => u.1.1.2)
      (((p₀, lam), r), 0) := analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hr : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => u.1.2)
      (((p₀, lam), r), 0) := analyticAt_snd.comp analyticAt_fst
  have hb : AnalyticAt ℂ (Prod.snd : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ → ℂ)
      (((p₀, lam), r), 0) := analyticAt_snd
  have hmap := (hp.prod (hb.mul hl)).prod (hb.mul hr)
  have hΘ' : AnalyticAt ℂ Θ ((p₀, (0 : ℂ) * lam), (0 : ℂ) * r) := by
    simpa only [zero_mul] using hΘ
  exact analyticAt_parametric_dslope_zero
    (hΘ'.comp (x := (((p₀, lam), r), 0))
      (f := fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ =>
        ((u.1.1.1, u.2 * u.1.1.2), u.2 * u.1.2)) hmap)

theorem cepsComplexJetMorseScaleRoot_factor {d : ℕ}
    (Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ) (p : Fin d → ℂ)
    (hzero : Θ ((p, 0), 0) = 0) (lam r b : ℂ) :
    Θ ((p, b * lam), b * r) = b * cepsComplexJetMorseScaleRoot d Θ p lam r b := by
  have h := sub_smul_dslope (fun t : ℂ => Θ ((p, t * lam), t * r)) 0 b
  simpa [cepsComplexJetMorseScaleRoot, hzero] using! h.symm

theorem cepsComplexJetMorseScaleRoot_zero_fderiv {d : ℕ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0)) (lam r : ℂ) :
    cepsComplexJetMorseScaleRoot d Θ p₀ lam r 0 =
      fderiv ℂ Θ ((p₀, 0), 0) ((0, lam), r) := by
  have hc : HasDerivAt (fun t : ℂ => ((p₀, t * lam), t * r)) ((0, lam), r) 0 := by
    simpa [Pi.mul_def, id_eq] using!
      ((hasDerivAt_const (0 : ℂ) p₀).prodMk ((hasDerivAt_id (0 : ℂ)).mul_const lam)).prodMk
        ((hasDerivAt_id (0 : ℂ)).mul_const r)
  have hd := hΘ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hc (by simp)
  simpa only [cepsComplexJetMorseScaleRoot, dslope_same] using! hd.deriv

/-- The zero-scale value has the exact oriented quadratic form. -/
theorem cepsComplexJetMorseScaleRoot_zero {d N : ℕ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {η : (Fin d → ℂ) × ℂ → ℂ}
    {p₀ : Fin d → ℂ} {s₀ : ℂ}
    (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0))
    (hη : AnalyticAt ℂ η (p₀, 0)) (hη₀ : η (p₀, 0) = 0)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0)
    (hz : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), Θ (u, 0) = η u)
    (hr : HasDerivAt (fun t : ℂ => Θ ((p₀, 0), t)) s₀⁻¹ 0) (lam r : ℂ) :
    cepsComplexJetMorseScaleRoot d Θ p₀ lam r 0 =
      -lam / cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) + r / s₀ := by
  let D := fderiv ℂ Θ ((p₀, 0), 0)
  have hline : AnalyticAt ℂ (fun t : ℂ => (p₀, t)) 0 := analyticAt_const.prod analyticAt_id
  have he : (fun t : ℂ => Θ ((p₀, t), 0)) =ᶠ[𝓝 0] (fun t => η (p₀, t)) := by
    filter_upwards [hline.continuousAt.tendsto.eventually hz] with t ht
    exact ht
  have hηd := (cepsComplexCgfJetCenter_hasDerivAt_zero hη hη₀ hV hc).congr_of_eventuallyEq he
  have hmuCurve : HasDerivAt (fun t : ℂ => ((p₀, t), (0 : ℂ))) ((0, 1), 0) 0 :=
    ((hasDerivAt_const 0 p₀).prodMk (hasDerivAt_id 0)).prodMk (hasDerivAt_const 0 (0 : ℂ))
  have hrCurve : HasDerivAt (fun t : ℂ => ((p₀, (0 : ℂ)), t)) ((0, 0), 1) 0 :=
    (hasDerivAt_const 0 (p₀, (0 : ℂ))).prodMk (hasDerivAt_id 0)
  have hdMu := hΘ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hmuCurve rfl
  have hdR := hΘ.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq 0 hrCurve rfl
  have hMu : D ((0, 1), 0) = -(cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)))⁻¹ := hdMu.unique hηd
  have hR : D ((0, 0), 1) = s₀⁻¹ := hdR.unique hr
  rw [cepsComplexJetMorseScaleRoot_zero_fderiv hΘ]
  have hvec : ((0, lam), r) =
      lam • (((0 : Fin d → ℂ), (1 : ℂ)), (0 : ℂ)) +
      r • (((0 : Fin d → ℂ), (0 : ℂ)), (1 : ℂ)) := by simp
  change D ((0, lam), r) = _
  rw [hvec, map_add, map_smul, map_smul, hMu, hR]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end PGM
