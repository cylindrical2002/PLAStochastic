import PLAStochastic.Index.CEPS.Normal.RootDifferential
import PLAStochastic.Index.CEPS.Normal.ActualDenominator

/-! # Actual root differentials used by the half-line transport formula

The root path and root-slope jets follow from the actual Morse chart and
root equation. The non-merger condition is explicit; no root derivative
or nonzero root slope is assumed.
-/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsRootPlus_differentiableAt_joint {μ q : ℂ}
    (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ)
    (hslit : q - cepsMorseMin D θ ρW μ ∈ slitPlane) :
    DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsRootPlus D θ ρW x.1 x.2) (μ, q) := by
  have hμb : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := mem_ball_zero_iff.mpr hμ
  have hm := ((differentiableOn_cepsMorseMin hW hθ hD) μ hμb).differentiableAt
    (isOpen_ball.mem_nhds hμb)
  have hw : DifferentiableAt ℂ (fun x : ℂ × ℂ => x.2 - cepsMorseMin D θ ρW x.1) (μ, q) :=
    differentiableAt_snd.sub (DifferentiableAt.fun_comp'
      (g := cepsMorseMin D θ ρW) (f := fun x : ℂ × ℂ => x.1) (μ, q) hm differentiableAt_fst)
  have hs := (differentiableAt_sqrt hslit).comp (μ, q) hw
  have hmem : (μ, cepsRootR D θ ρW μ q) ∈
      ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ) :=
    ⟨hμb, mem_ball_zero_iff.mpr hr⟩
  have hΘ := ((differentiableOn_cepsMorseRoot hW hθ hD) _ hmem).differentiableAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hmem)
  exact hΘ.comp (μ, q) (differentiableAt_fst.prodMk hs)

include hW hθ hD in
theorem cepsRootPlus_equation_of_mem_SPRegion {μ q : ℂ}
    (hx : (μ, q) ∈ cepsSPRegion D θ ρW) :
    cepsCgf ρW (cepsRootPlus D θ ρW μ q) + μ * cepsRootPlus D θ ρW μ q = q := by
  have hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ :=
    norm_sqrt_lt (cepsChartRho_pos hD hθ) hx.2
  have he := cepsRootEq_rootPlus hW hθ hD hx.1 hr
  exact sub_eq_zero.mp he

variable (dom : CepsCanonDomain D θ v)

include hW hθ hD in
theorem cepsRootR_mem_slitPlane {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hre : 0 ≤ q.re) (hne : q - cepsMorseMin D θ ρW μ ≠ 0) :
    q - cepsMorseMin D θ ρW μ ∈ slitPlane := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hnon : 0 ≤ (q - cepsMorseMin D θ ρW μ).re := by
    rw [sub_re]
    linarith [re_cepsMorseMin_nonpos hW hθ hD (dom.μ_lt_chart hμ')]
  rw [mem_slitPlane_iff]
  by_cases hp : 0 < (q - cepsMorseMin D θ ρW μ).re
  · exact Or.inl hp
  · right
    intro hi
    apply hne
    apply Complex.ext
    · change (q - cepsMorseMin D θ ρW μ).re = 0
      linarith
    · exact hi

include hW hθ hD in
/-- All four actual root jets, with the nonzero slope derived from the discount equation. -/
theorem cepsRootPlus_actual_path_jets {Qcurve : ℝ → ℂ} {μ : ℝ} {t : ℂ}
    (hμ : |μ| ≤ dom.μ₀) (hq : ‖Qcurve μ‖ ≤ dom.q₀) (hre : 0 ≤ (Qcurve μ).re)
    (hne : Qcurve μ - cepsMorseMin D θ ρW μ ≠ 0) (hQ : HasDerivAt Qcurve t μ) :
    let B := fun (x : ℝ) q => cepsRootPlus D θ ρW x q
    let p := cepsNormalRootSlope (cepsCgf ρW) B μ (Qcurve μ)
    let p₂ := deriv (deriv (cepsCgf ρW)) (B μ (Qcurve μ))
    p ≠ 0 ∧
      HasDerivAt (fun x : ℝ => B x (Qcurve x)) (-(B μ (Qcurve μ) - t) / p) μ ∧
      HasDerivAt (fun x : ℝ => cepsNormalRootSlope (cepsCgf ρW) B x (Qcurve x))
        (1 - (B μ (Qcurve μ) - t) * p₂ / p) μ ∧
      HasDerivAt (B μ) (1 / p) (Qcurve μ) ∧
      HasDerivAt (cepsNormalRootSlope (cepsCgf ρW) B μ) (p₂ / p) (Qcurve μ) := by
  dsimp only
  let B := fun (x : ℝ) q => cepsRootPlus D θ ρW x q
  let p := cepsNormalRootSlope (cepsCgf ρW) B μ (Qcurve μ)
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hx := dom.mem_SPRegion hW hθ hD hμ' hq
  have hV := isOpen_cepsSPRegion hW hθ hD
  have hjoint := cepsRootPlus_differentiableAt_joint hW hθ hD (dom.μ_lt_chart hμ')
    (dom.norm_cepsRootR_lt hW hθ hD hμ' hq) (cepsRootR_mem_slitPlane hW hθ hD dom hμ hre hne)
  have hbq : DifferentiableAt ℂ (B μ) (Qcurve μ) := by
    simpa only [Function.comp_def, B] using hjoint.comp (Qcurve μ)
      ((differentiableAt_const (μ : ℂ)).prodMk differentiableAt_id)
  have hm : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 μ := (hasDerivAt_id μ).ofReal_comp
  have hb : DifferentiableAt ℝ (fun x : ℝ => B x (Qcurve x)) μ := by
    simpa only [Function.comp_def, B] using!
      ((hjoint.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt μ (hm.prodMk hQ)).differentiableAt
  have hroot : ∀ᶠ x : ℝ in 𝓝 μ,
      cepsCgf ρW (B x (Qcurve x)) + (x : ℂ) * B x (Qcurve x) = Qcurve x := by
    have hpath := hm.continuousAt.prodMk hQ.continuousAt
    have hmem := hpath.preimage_mem_nhds (hV.mem_nhds hx)
    filter_upwards [hmem] with x hx'
    exact cepsRootPlus_equation_of_mem_SPRegion hW hθ hD hx'
  have hrootq : ∀ᶠ q' : ℂ in 𝓝 (Qcurve μ),
      cepsCgf ρW (B μ q') + (μ : ℂ) * B μ q' = q' := by
    have hpath : ContinuousAt (fun q' : ℂ => ((μ : ℂ), q')) (Qcurve μ) := by fun_prop
    have hmem := hpath.preimage_mem_nhds (hV.mem_nhds hx)
    filter_upwards [hmem] with q' hq'
    exact cepsRootPlus_equation_of_mem_SPRegion hW hθ hD hq'
  have hβball : B μ (Qcurve μ) ∈ ball (0 : ℂ) (cepsCgfRadius D θ) :=
    rootPlus_mem_ball hW hθ hD (dom.μ_lt_chart hμ') (dom.norm_cepsRootR_lt hW hθ hD hμ' hq)
  have hψ := ((differentiableOn_cepsCgf hW hθ hD) _ hβball).differentiableAt
    (isOpen_ball.mem_nhds hβball)
  have hψ' := (((differentiableOn_cepsCgf hW hθ hD).deriv isOpen_ball) _ hβball).differentiableAt
    (isOpen_ball.mem_nhds hβball)
  have hd := ((hψ.hasDerivAt.comp (Qcurve μ) hbq.hasDerivAt).add
    (hbq.hasDerivAt.const_mul (μ : ℂ))).congr_of_eventuallyEq (EventuallyEq.symm hrootq)
  have he := hd.unique (hasDerivAt_id (Qcurve μ))
  have hp : p ≠ 0 := by
    intro hz
    have hep : p * deriv (B μ) (Qcurve μ) = 1 := by
      dsimp [p, cepsNormalRootSlope]
      linear_combination he
    rw [hz, zero_mul] at hep
    exact zero_ne_one hep
  exact ⟨hp, cepsNormal_root_jets (cepsCgf ρW) B Qcurve hb.hasDerivAt hbq.hasDerivAt
    hψ.hasDerivAt hψ'.hasDerivAt hQ hroot hrootq hp⟩

end PGM
