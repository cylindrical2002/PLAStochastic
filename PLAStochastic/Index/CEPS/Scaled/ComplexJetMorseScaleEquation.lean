import PLAStochastic.Index.CEPS.Scaled.ComplexJetMorseScaleRoot
import PLAStochastic.Index.CEPS.Scaled.ComplexJetMinimumUnit
import PLAStochastic.ForMathlib.Analysis.Complex.ParametricPowerCancel

/-! # Exact finite-input scaled Morse equation on a genuine joint neighborhood -/

noncomputable section
open Complex Filter Topology
namespace PGM

set_option maxHeartbeats 800000 in
theorem cepsComplexJetMorseScaleRoot_equation_eventually {d N : ℕ}
    {Θ : ((Fin d → ℂ) × ℂ) × ℂ → ℂ} {η : (Fin d → ℂ) × ℂ → ℂ}
    {p₀ : Fin d → ℂ} (hΘ : AnalyticAt ℂ Θ ((p₀, 0), 0))
    (hη : AnalyticAt ℂ η (p₀, 0))
    (hz : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), Θ (u, 0) = η u)
    (hηz : ∀ᶠ p in 𝓝 p₀, η (p, 0) = 0)
    (hc : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)),
      deriv (cepsComplexCgfJetModel (cepsComplexJetPad d u.1) N) (η u) + u.2 = 0)
    (hroot : ∀ᶠ u in 𝓝 ((p₀, (0 : ℂ)), (0 : ℂ)),
      cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1) N (Θ u) + u.1.2 * Θ u =
        cepsComplexCgfJetMinimum d N η u.1 + u.2 ^ 2) (lam r : ℂ) :
    ∀ᶠ u in 𝓝 (((p₀, lam), r), (0 : ℂ)),
      (cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2) ^ 2 *
          cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N
            (u.2 * cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2) +
        u.1.1.2 * cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2 =
      u.1.1.2 ^ 2 * cepsComplexCgfJetMinimumUnit d N η (u.1.1.1, u.2 * u.1.1.2) +
        u.1.2 ^ 2 := by
  let A := ((Fin d → ℂ) × ℂ) × ℂ
  let v : A × ℂ := (((p₀, lam), r), 0)
  let Ψ : A × ℂ → ℂ := fun u => cepsComplexJetMorseScaleRoot d Θ u.1.1.1 u.1.1.2 u.1.2 u.2
  have hΨ : AnalyticAt ℂ Ψ v := cepsComplexJetMorseScaleRoot_analyticAt hΘ lam r
  have hp : AnalyticAt ℂ (fun u : A × ℂ => u.1.1.1) v :=
    analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)
  have hl : AnalyticAt ℂ (fun u : A × ℂ => u.1.1.2) v :=
    analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)
  have hr : AnalyticAt ℂ (fun u : A × ℂ => u.1.2) v := analyticAt_snd.comp analyticAt_fst
  have hb : AnalyticAt ℂ (Prod.snd : A × ℂ → ℂ) v := analyticAt_snd
  have hpi : ∀ i, AnalyticAt ℂ (fun u : A × ℂ => cepsComplexJetPad d u.1.1.1 i) v := by
    intro i
    simpa only [Function.comp_apply] using!
      (cepsComplexJetPad_analyticAt d i p₀).comp (x := v)
        (f := fun u : A × ℂ => u.1.1.1) hp
  have hPol : AnalyticAt ℂ (fun u : A × ℂ =>
      cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N (u.2 * Ψ u)) v :=
    cepsCgfComplexJetPolynomial_analyticAt hpi (hb.mul hΨ) N
  have hU : AnalyticAt ℂ (cepsComplexCgfJetMinimumUnit d N η) (p₀, (0 : ℂ) * lam) := by
    simpa only [zero_mul] using cepsComplexCgfJetMinimumUnit_analyticAt hη
  have hUnit := hU.comp (x := v) (f := fun u : A × ℂ => (u.1.1.1, u.2 * u.1.1.2))
    (hp.prod (hb.mul hl))
  let R : A × ℂ → ℂ := fun u =>
    (Ψ u) ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N (u.2 * Ψ u) +
      u.1.1.2 * Ψ u - u.1.1.2 ^ 2 * cepsComplexCgfJetMinimumUnit d N η (u.1.1.1, u.2 * u.1.1.2) -
        u.1.2 ^ 2
  have hR : AnalyticAt ℂ R v :=
    ((((hΨ.pow 2).mul hPol).add (hl.mul hΨ)).sub ((hl.pow 2).mul hUnit)).sub (hr.pow 2)
  have hM : AnalyticAt ℂ (fun u : A × ℂ => ((u.1.1.1, u.2 * u.1.1.2), u.2 * u.1.2)) v :=
    (hp.prod (hb.mul hl)).prod (hb.mul hr)
  have htM : Tendsto (fun u : A × ℂ => ((u.1.1.1, u.2 * u.1.1.2), u.2 * u.1.2))
      (𝓝 v) (𝓝 ((p₀, (0 : ℂ)), (0 : ℂ))) := by
    simpa only [v, zero_mul] using hM.continuousAt.tendsto
  have hmap : AnalyticAt ℂ (fun p : Fin d → ℂ => (p, (0 : ℂ))) p₀ :=
    analyticAt_id.prod analyticAt_const
  have hpzero : ∀ᶠ p in 𝓝 p₀, Θ ((p, 0), 0) = 0 := by
    filter_upwards [hηz, hmap.continuousAt.tendsto.eventually hz] with p hp hz
    change Θ ((p, 0), 0) = η (p, 0) at hz
    exact hz.trans hp
  have hpower : ∀ᶠ u in 𝓝 v, u.2 ^ 2 * R u = 0 := by
    filter_upwards [htM.eventually hroot, hp.continuousAt.tendsto.eventually hpzero,
      hp.continuousAt.tendsto.eventually (cepsComplexCgfJetMinimum_factor_eventually hη hηz hc)]
      with u hu hz hm
    change cepsComplexCgfJetModel (cepsComplexJetPad d u.1.1.1) N
        (Θ ((u.1.1.1, u.2 * u.1.1.2), u.2 * u.1.2)) +
        (u.2 * u.1.1.2) * Θ ((u.1.1.1, u.2 * u.1.1.2), u.2 * u.1.2) =
      cepsComplexCgfJetMinimum d N η (u.1.1.1, u.2 * u.1.1.2) + (u.2 * u.1.2) ^ 2 at hu
    change Θ ((u.1.1.1, 0), 0) = 0 at hz
    rw [cepsComplexJetMorseScaleRoot_factor Θ u.1.1.1 hz, hm (u.2 * u.1.1.2)] at hu
    change (u.2 * Ψ u) ^ 2 *
        cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N (u.2 * Ψ u) +
        (u.2 * u.1.1.2) * (u.2 * Ψ u) =
      (u.2 * u.1.1.2) ^ 2 * cepsComplexCgfJetMinimumUnit d N η (u.1.1.1, u.2 * u.1.1.2) +
        (u.2 * u.1.2) ^ 2 at hu
    dsimp only [R]
    linear_combination hu
  filter_upwards [analyticAt_eventually_zero_of_scalar_pow_mul hR 2 hpower] with u hu
  change (Ψ u) ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N (u.2 * Ψ u) +
      u.1.1.2 * Ψ u - u.1.1.2 ^ 2 * cepsComplexCgfJetMinimumUnit d N η (u.1.1.1, u.2 * u.1.1.2) -
        u.1.2 ^ 2 = 0 at hu
  change (Ψ u) ^ 2 * cepsCgfComplexJetPolynomial (cepsComplexJetPad d u.1.1.1) N (u.2 * Ψ u) +
      u.1.1.2 * Ψ u = _
  linear_combination hu

end PGM
