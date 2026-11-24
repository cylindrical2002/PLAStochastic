import PLAStochastic.Index.CEPS.Scaled.MorseChart
import PLAStochastic.Index.CEPS.Normal.ActualMorseData

/-! # The actual Morse minimum has a second-order zero in the drift -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM

def cepsMorseMinUnit (D θ : ℝ) (ρW : Measure ℝ) (μ : ℂ) : ℂ :=
  hadamard2 (cepsMorseMin D θ ρW) 0 μ

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem hasDerivAt_cepsMorseMin_center {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    HasDerivAt (cepsMorseMin D θ ρW) (cepsMorseCenter D θ ρW μ) μ := by
  have hc := ((differentiableOn_cepsMorseCenter hW hθ hD) μ
    (mem_ball_zero_iff.mpr hμ)).differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hμ))
  have hb : cepsMorseCenter D θ ρW μ ∈ ball (0 : ℂ) (cepsCgfRadius D θ) :=
    mem_ball_zero_iff.mpr ((norm_cepsMorseCenter_lt hW hθ hD hμ).trans_le
      (by have := cepsChartRadius_le_r0 (D := D) (θ := θ); have := cepsCgfRadius_pos hD hθ; linarith))
  have hψ := ((differentiableOn_cepsCgf hW hθ hD) _ hb).differentiableAt
    (isOpen_ball.mem_nhds hb) |>.hasDerivAt
  rw [deriv_cepsCgf_cepsMorseCenter hW hθ hD hμ] at hψ
  have hm := (hψ.comp μ hc.hasDerivAt).add ((hasDerivAt_id' μ).mul hc.hasDerivAt)
  change HasDerivAt (fun μ => cepsCgf ρW (cepsMorseCenter D θ ρW μ) +
    μ * cepsMorseCenter D θ ρW μ) _ μ
  convert! hm using 1
  ring

include hW hθ hD in
theorem deriv_cepsMorseCenter_zero : deriv (cepsMorseCenter D θ ρW) 0 =
    -(cepsStepVar ρW : ℂ)⁻¹ := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) :=
    mem_ball_self (cepsChartMu_pos hD hθ)
  have hc := ((differentiableOn_cepsMorseCenter hW hθ hD) 0 h0).differentiableAt
    (isOpen_ball.mem_nhds h0) |>.hasDerivAt
  have hψ := (((differentiableOn_cepsCgf hW hθ hD).deriv isOpen_ball) 0
    (mem_ball_self (cepsCgfRadius_pos hD hθ))).differentiableAt
      (ball_mem_nhds 0 (cepsCgfRadius_pos hD hθ)) |>.hasDerivAt
  rw [deriv_deriv_cepsCgf_zero hW hθ hD] at hψ
  have hp := hψ.comp_of_eq (0 : ℂ) hc (cepsMorseCenter_at_zero hW hθ hD).symm
  have he : (fun μ => deriv (cepsCgf ρW) (cepsMorseCenter D θ ρW μ)) =ᶠ[𝓝 0]
      (fun μ : ℂ => -μ) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (cepsChartMu_pos hD hθ)] with μ hμ
    exact deriv_cepsCgf_cepsMorseCenter hW hθ hD (mem_ball_zero_iff.mp hμ)
  have hu := (hp.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id' (0 : ℂ)).neg
  have hv : (cepsStepVar ρW : ℂ) ≠ 0 := by exact_mod_cast (cepsStepVar_pos hW hθ hD).ne'
  apply (eq_neg_iff_add_eq_zero).mpr
  apply (mul_left_cancel₀ hv)
  rw [mul_zero, mul_add, hu, mul_inv_cancel₀ hv]
  ring

include hW hθ hD in
theorem cepsMorseMin_zero_jets : cepsMorseMin D θ ρW 0 = 0 ∧
    deriv (cepsMorseMin D θ ρW) 0 = 0 ∧
      deriv (deriv (cepsMorseMin D θ ρW)) 0 = -(cepsStepVar ρW : ℂ)⁻¹ := by
  refine ⟨by simp [cepsMorseMin, cepsCgfShift, cepsMorseCenter_at_zero hW hθ hD,
    cepsCgf_zero hW], ?_, ?_⟩
  · rw [(hasDerivAt_cepsMorseMin_center hW hθ hD
      (by simpa using cepsChartMu_pos hD hθ)).deriv, cepsMorseCenter_at_zero hW hθ hD]
  · have he : deriv (cepsMorseMin D θ ρW) =ᶠ[𝓝 0] cepsMorseCenter D θ ρW := by
      filter_upwards [ball_mem_nhds (0 : ℂ) (cepsChartMu_pos hD hθ)] with μ hμ
      exact (hasDerivAt_cepsMorseMin_center hW hθ hD (mem_ball_zero_iff.mp hμ)).deriv
    rw [he.deriv_eq, deriv_cepsMorseCenter_zero hW hθ hD]

include hW hθ hD in
theorem cepsMorseMinUnit_zero : cepsMorseMinUnit D θ ρW 0 =
    -1 / (2 * (cepsStepVar ρW : ℂ)) := by
  rw [cepsMorseMinUnit, hadamard2_zero, (cepsMorseMin_zero_jets hW hθ hD).2.2]
  ring

include hW hθ hD in
theorem cepsMorseMin_eq_sq_mul_unit {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    cepsMorseMin D θ ρW μ = μ ^ 2 * cepsMorseMinUnit D θ ρW μ := by
  have hs : ∀ t ∈ Icc (0 : ℝ) 1, (0 : ℂ) + t * μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by
    intro t ht
    rw [mem_ball, dist_zero_right, zero_add, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg μ) ht.2).trans_lt hμ
  have he := hadamard2_spec isOpen_ball (differentiableOn_cepsMorseMin hW hθ hD) hs
  simpa only [cepsMorseMinUnit, zero_add, (cepsMorseMin_zero_jets hW hθ hD).1,
    (cepsMorseMin_zero_jets hW hθ hD).2.1, zero_mul] using he

end PGM
