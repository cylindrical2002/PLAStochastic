import PLAStochastic.Index.CEPS.Scaled.ActualScaleChart

/-! # The actual scaled roots at zero scale are the Brownian roots -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseRoot_fderiv_zero_axes :
    fderiv ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2) (0, 0) (1, 0) =
      -(cepsStepVar ρW : ℂ)⁻¹ ∧
    fderiv ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2) (0, 0) (0, 1) =
      Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) := by
  let F := fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2
  have hp : (0 : ℂ × ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ
      ball (0 : ℂ) (cepsChartRho D θ) :=
    ⟨mem_ball_self (cepsChartMu_pos hD hθ), mem_ball_self (cepsChartRho_pos hD hθ)⟩
  have hF := ((differentiableOn_cepsMorseRoot hW hθ hD) (0, 0) hp).differentiableAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hp) |>.hasFDerivAt
  have hm := hF.comp_hasDerivAt (f := fun μ : ℂ => (μ, (0 : ℂ))) (0 : ℂ)
    ((hasDerivAt_id' (0 : ℂ)).prodMk (hasDerivAt_const (0 : ℂ) (0 : ℂ)))
  have hr := hF.comp_hasDerivAt (f := fun r : ℂ => ((0 : ℂ), r)) (0 : ℂ)
    ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id' (0 : ℂ)))
  have he : (fun μ : ℂ => cepsMorseRoot D θ ρW μ 0) =ᶠ[𝓝 0]
      cepsMorseCenter D θ ρW := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (cepsChartMu_pos hD hθ)] with μ hμ
    exact cepsMorseRoot_zero hW hθ hD (mem_ball_zero_iff.mp hμ)
  have hc := ((differentiableOn_cepsMorseCenter hW hθ hD) 0
    (mem_ball_self (cepsChartMu_pos hD hθ))).differentiableAt
      (ball_mem_nhds 0 (cepsChartMu_pos hD hθ)) |>.hasDerivAt
  rw [deriv_cepsMorseCenter_zero hW hθ hD] at hc
  have hz := hasDerivAt_cepsMorseRoot_zero hW hθ hD
    (μ := (0 : ℂ)) (by simpa using cepsChartMu_pos hD hθ)
  rw [cepsMorseCenter_at_zero hW hθ hD, deriv_deriv_cepsCgf_zero hW hθ hD] at hz
  exact ⟨(hm.congr_of_eventuallyEq he.symm).unique hc, hr.unique hz⟩

include dom hW hθ hD in
theorem cepsScaledSignedRoot_zero (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (sign : ℂ) :
    cepsScaledSignedRoot D θ ρW lam z sign 0 =
      -(lam : ℂ) / (cepsStepVar ρW : ℂ) + sign * Complex.sqrt (2 / (cepsStepVar ρW : ℂ)) *
        Complex.sqrt (z + (lam : ℂ) ^ 2 / (2 * (cepsStepVar ρW : ℂ))) := by
  let F := fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2
  let A := fderiv ℂ F (0, 0)
  have hp : (0 : ℂ × ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ
      ball (0 : ℂ) (cepsChartRho D θ) :=
    ⟨mem_ball_self (cepsChartMu_pos hD hθ), mem_ball_self (cepsChartRho_pos hD hθ)⟩
  have hF := ((differentiableOn_cepsMorseRoot hW hθ hD) (0, 0) hp).differentiableAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hp) |>.hasFDerivAt
  obtain ⟨hd, _⟩ := cepsScaledRootCoordinate_budget dom hW hθ hD lam hz
  have hR := (radicandScaleRadius_budget dom hW hθ hD lam).1
  have hc := (hd 0 (mem_ball_self hR)).differentiableAt (ball_mem_nhds 0 hR) |>.hasDerivAt
  have hcurve : HasDerivAt (fun b : ℂ => (b * lam,
      b * sign * cepsScaledRootCoordinate D θ ρW lam z b))
      ((lam : ℂ), sign * cepsScaledRootCoordinate D θ ρW lam z 0) 0 := by
    have ht := ((hasDerivAt_id' (0 : ℂ)).mul_const sign).mul hc
    simpa using!
      ((hasDerivAt_id' (0 : ℂ)).mul_const (lam : ℂ)).prodMk ht
  have hf := hF.comp_hasDerivAt_of_eq (0 : ℂ) hcurve (by simp)
  have hderiv : deriv (fun a : ℂ => cepsMorseRoot D θ ρW (a * lam)
      (a * sign * cepsScaledRootCoordinate D θ ρW lam z a)) 0 =
      A ((lam : ℂ), sign * cepsScaledRootCoordinate D θ ρW lam z 0) := by
    simpa only [Function.comp_apply] using! hf.deriv
  rw [cepsScaledSignedRoot, dslope_same, hderiv]
  change A ((lam : ℂ), sign * cepsScaledRootCoordinate D θ ρW lam z 0) = _
  have hv : ((lam : ℂ), sign * cepsScaledRootCoordinate D θ ρW lam z 0) =
      (lam : ℂ) • ((1 : ℂ), (0 : ℂ)) +
        (sign * cepsScaledRootCoordinate D θ ρW lam z 0) • ((0 : ℂ), (1 : ℂ)) := by
    ext <;> simp
  obtain ⟨hA, hB⟩ := cepsMorseRoot_fderiv_zero_axes hW hθ hD
  rw [hv, map_add, map_smul, map_smul]
  change (lam : ℂ) * A (1, 0) + (sign * cepsScaledRootCoordinate D θ ρW lam z 0) * A (0, 1) = _
  dsimp only [A, F]
  rw [hA, hB, cepsScaledRootCoordinate, cepsScaledMorseRadicand_zero hW hθ hD]
  ring

end PGM
