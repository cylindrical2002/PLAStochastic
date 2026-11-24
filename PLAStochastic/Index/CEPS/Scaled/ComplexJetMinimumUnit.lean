import PLAStochastic.Index.CEPS.Scaled.ComplexJetCgfMinimum
import PLAStochastic.Index.CEPS.Normal.ParametricDSlopeGerm
import PLAStochastic.Index.CEPS.Normal.SecondSlopeTaylor

/-! # Genuine removable finite-input critical-value quadratic quotient -/

noncomputable section
open Complex Filter Topology
namespace PGM

def cepsComplexCgfJetMinimumUnit (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (u : (Fin d → ℂ) × ℂ) : ℂ :=
  dslope (dslope (fun t => cepsComplexCgfJetMinimum d N η (u.1, t)) 0) 0 u.2

theorem cepsComplexCgfJetMinimumUnit_analyticAt {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ} (hη : AnalyticAt ℂ η (p₀, 0)) :
    AnalyticAt ℂ (cepsComplexCgfJetMinimumUnit d N η) (p₀, 0) :=
  analyticAt_parametric_second_dslope_zero (cepsComplexCgfJetMinimum_analyticAt hη)

theorem cepsComplexCgfJetMinimumUnit_zero {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hη₀ : η (p₀, 0) = 0)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) :
    cepsComplexCgfJetMinimumUnit d N η (p₀, 0) =
      -(cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)))⁻¹ / 2 := by
  rw [cepsComplexCgfJetMinimumUnit,
    second_dslope_zero_eq_half_deriv (cepsComplexCgfJetMinimum_analyticAt hη).curry_right,
    (cepsComplexCgfJetMinimum_deriv_hasDerivAt_zero hη hη₀ hV hc).deriv]

/-- The identity is algebraic for every scalar drift; only its zero value and
derivative use the actual critical germ on the common input neighborhood. -/
theorem cepsComplexCgfJetMinimum_factor_eventually {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0))
    (hz : ∀ᶠ p in 𝓝 p₀, η (p, 0) = 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0) :
    ∀ᶠ p in 𝓝 p₀, ∀ t : ℂ, cepsComplexCgfJetMinimum d N η (p, t) =
      t ^ 2 * cepsComplexCgfJetMinimumUnit d N η (p, t) := by
  have hm : AnalyticAt ℂ (fun p : Fin d → ℂ => (p, (0 : ℂ))) p₀ :=
    analyticAt_id.prod analyticAt_const
  filter_upwards [hz, hm.continuousAt.tendsto.eventually
    (cepsComplexCgfJetMinimum_deriv_eventually hη hc)] with p hη₀ hd
  change deriv (fun t => cepsComplexCgfJetMinimum d N η (p, t)) 0 = η (p, 0) at hd
  rw [hη₀] at hd
  have hzero : cepsComplexCgfJetMinimum d N η (p, 0) = 0 := by
    simp [cepsComplexCgfJetMinimum, hη₀, cepsComplexCgfJetModel]
  intro t
  simpa only [zero_add, hzero, hd, zero_mul, add_zero, cepsComplexCgfJetMinimumUnit] using!
    second_dslope_taylor_identity (fun t => cepsComplexCgfJetMinimum d N η (p, t)) 0 t

def cepsComplexJetMorseSquare (d N : ℕ) (η : (Fin d → ℂ) × ℂ → ℂ)
    (p : Fin d → ℂ) (lam z b : ℂ) : ℂ :=
  z * (1 + b * lam) - lam ^ 2 * cepsComplexCgfJetMinimumUnit d N η (p, b * lam)

theorem cepsComplexJetMorseSquare_analyticAt {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (lam z : ℂ) :
    AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ =>
      cepsComplexJetMorseSquare d N η u.1.1.1 u.1.1.2 u.1.2 u.2) (((p₀, lam), z), 0) := by
  have hp : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => u.1.1.1)
      (((p₀, lam), z), 0) := analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hl : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => u.1.1.2)
      (((p₀, lam), z), 0) := analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hz : AnalyticAt ℂ (fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => u.1.2)
      (((p₀, lam), z), 0) := analyticAt_snd.comp analyticAt_fst
  have hb : AnalyticAt ℂ (Prod.snd : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ → ℂ)
      (((p₀, lam), z), 0) := analyticAt_snd
  have hmap := hp.prod (hb.mul hl)
  have hU : AnalyticAt ℂ (cepsComplexCgfJetMinimumUnit d N η) (p₀, (0 : ℂ) * lam) := by
    simpa only [zero_mul] using cepsComplexCgfJetMinimumUnit_analyticAt hη
  exact (hz.mul (analyticAt_const.add (hb.mul hl))).sub ((hl.pow 2).mul
    (hU.comp (x := (((p₀, lam), z), 0))
      (f := fun u : (((Fin d → ℂ) × ℂ) × ℂ) × ℂ => (u.1.1.1, u.2 * u.1.1.2)) hmap))

theorem cepsComplexJetMorseSquare_zero {d N : ℕ}
    {η : (Fin d → ℂ) × ℂ → ℂ} {p₀ : Fin d → ℂ}
    (hη : AnalyticAt ℂ η (p₀, 0)) (hη₀ : η (p₀, 0) = 0)
    (hV : cepsComplexJetPad d p₀ (cepsJetCode (.inl 0)) ≠ 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0)
    (lam z : ℂ) :
    cepsComplexJetMorseSquare d N η p₀ lam z 0 =
      z + lam ^ 2 / (2 * cepsComplexJetPad d p₀ (cepsJetCode (.inl 0))) := by
  simp only [cepsComplexJetMorseSquare, zero_mul, add_zero, mul_one,
    cepsComplexCgfJetMinimumUnit_zero hη hη₀ hV hc]
  field_simp [hV]
  ring

end PGM
