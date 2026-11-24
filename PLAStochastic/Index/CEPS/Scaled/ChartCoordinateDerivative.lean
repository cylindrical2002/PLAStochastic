import PLAStochastic.Index.CEPS.Scaled.MorseCoordinateDerivative
import PLAStochastic.Index.CEPS.Scaled.MorseChartJoint

/-! # Coordinate derivatives of the removable scaled Morse chart -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMorseChart_zero_linear (lam r : ℂ) :
    cepsScaledMorseChart D θ ρW lam r 0 =
      fderiv ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2) (0, 0) (lam, r) := by
  have hp : (0, 0) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ
      ball (0 : ℂ) (cepsChartRho D θ) :=
    ⟨mem_ball_self (cepsChartMu_pos hD hθ), mem_ball_self (cepsChartRho_pos hD hθ)⟩
  have hF := ((differentiableOn_cepsMorseRoot hW hθ hD) (0, 0) hp).differentiableAt
    ((isOpen_ball.prod isOpen_ball).mem_nhds hp) |>.hasFDerivAt
  have hc : HasDerivAt (fun a : ℂ => (a * lam, a * r)) (lam, r) 0 := by
    simpa only [one_mul] using!
      (((hasDerivAt_id' (0 : ℂ)).mul_const lam).prodMk
        ((hasDerivAt_id' (0 : ℂ)).mul_const r))
  have h := hF.comp_hasDerivAt_of_eq (0 : ℂ) hc (by simp)
  simpa only [cepsScaledMorseChart, dslope_same, Function.comp_def] using h.deriv

include hW hθ hD in
theorem cepsScaledMorseChart_coordinate_hasDerivAt {lam r b : ℂ}
    (hμ : ‖b * lam‖ ≤ dom.μ₀) (hr : ‖b * r‖ < dom.rmax) :
    HasDerivAt (fun s => cepsScaledMorseChart D θ ρW lam s b)
      (deriv (cepsMorseRoot D θ ρW (b * lam)) (b * r)) r := by
  by_cases hb : b = 0
  · subst b
    let A := fderiv ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2) (0, 0)
    have he : (fun s => cepsScaledMorseChart D θ ρW lam s 0) =
        (fun s => A (lam, 0) + s * A (0, 1)) := by
      funext s
      rw [cepsScaledMorseChart_zero_linear hW hθ hD]
      change A (lam, s) = _
      rw [show (lam, s) = (lam, 0) + s • ((0 : ℂ), (1 : ℂ)) by ext <;> simp,
        map_add, map_smul]
      rfl
    have hp : (0, 0) ∈ ball (0 : ℂ) (cepsChartMu D θ) ×ˢ
        ball (0 : ℂ) (cepsChartRho D θ) :=
      ⟨mem_ball_self (cepsChartMu_pos hD hθ), mem_ball_self (cepsChartRho_pos hD hθ)⟩
    have hF := ((differentiableOn_cepsMorseRoot hW hθ hD) (0, 0) hp).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds hp) |>.hasFDerivAt
    have hx := hF.comp_hasDerivAt_of_eq (0 : ℂ)
      ((hasDerivAt_const (0 : ℂ) (0 : ℂ)).prodMk (hasDerivAt_id' (0 : ℂ))) (by simp)
    have hA : A (0, 1) = deriv (cepsMorseRoot D θ ρW 0) 0 := by
      simpa only [Function.comp_def, A] using hx.deriv.symm
    simp only [zero_mul]
    rw [he, ← hA]
    simpa only [one_mul] using!
      (((hasDerivAt_id' r).mul_const (A (0, 1))).const_add (A (lam, 0)))
  · have hm := mem_ball_zero_iff.mpr (dom.μ_lt_chart hμ)
    have hr' := mem_ball_zero_iff.mpr (hr.trans_le
      (by have := dom.rmax_r1; have := dom.rmax_pos; linarith : dom.rmax ≤ cepsChartRho D θ))
    have hd : DifferentiableOn ℂ (cepsMorseRoot D θ ρW (b * lam))
        (ball 0 (cepsChartRho D θ)) :=
      (differentiableOn_cepsMorseRoot hW hθ hD).comp
        (f := fun s : ℂ => (b * lam, s)) (by fun_prop) (fun _ hs => ⟨hm, hs⟩)
    have hΘ := (hd _ hr').differentiableAt (isOpen_ball.mem_nhds hr')
    have h := (hΘ.hasDerivAt.comp r ((hasDerivAt_id' r).const_mul b)).div_const b
    have he : (fun s => cepsScaledMorseChart D θ ρW lam s b) =
        (fun s => cepsMorseRoot D θ ρW (b * lam) (b * s) / b) :=
      funext fun s => cepsScaledMorseChart_eq_div hW hθ hD lam s hb
    rw [he]
    simpa only [Function.comp_def, mul_one, mul_div_cancel_right₀ _ hb] using h

include hW hθ hD in
theorem cepsScaledMorseChart_coordinate_deriv_budget {lam r b : ℂ}
    (hμ : ‖b * lam‖ ≤ dom.μ₀) (hr : ‖b * r‖ < dom.rmax) :
    ‖deriv (fun s => cepsScaledMorseChart D θ ρW lam s b) r‖ ≤ 4 * cepsChartK D := by
  rw [(cepsScaledMorseChart_coordinate_hasDerivAt dom hW hθ hD hμ hr).deriv]
  exact cepsMorseRoot_coordinate_deriv_budget dom hW hθ hD hμ hr

end PGM
