import PLAStochastic.Index.CEPS.Scaled.MorseChart

/-! # Uniform derivative in the actual Morse root coordinate -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseRoot_coordinate_deriv_budget {μ r : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hr : ‖r‖ < dom.rmax) :
    ‖deriv (cepsMorseRoot D θ ρW μ) r‖ ≤ 4 * cepsChartK D := by
  let R := cepsChartRho D θ
  have hR : 0 < R := cepsChartRho_pos hD hθ
  have hK := cepsChartK_pos hD
  have hμc : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := mem_ball_zero_iff.mpr (dom.μ_lt_chart hμ)
  have hd : DifferentiableOn ℂ (cepsMorseRoot D θ ρW μ) (ball 0 R) :=
    (differentiableOn_cepsMorseRoot hW hθ hD).comp
      (f := fun r : ℂ => (μ, r)) (by fun_prop) (fun r hr => ⟨hμc, hr⟩)
  have hg := hd.sub_const (cepsMorseCenter D θ ρW μ)
  have hbound : ∀ r' ∈ ball (0 : ℂ) R,
      ‖cepsMorseRoot D θ ρW μ r' - cepsMorseCenter D θ ρW μ‖ ≤ cepsChartK D * R := by
    intro r' hr'
    exact (norm_cepsMorseRoot_sub_center_le hW hθ hD (dom.μ_lt_chart hμ)
      (mem_ball_zero_iff.mp hr')).trans
        (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hr').le hK.le)
  have hrball : r ∈ ball (0 : ℂ) (R / 2) := by
    apply mem_ball_zero_iff.mpr
    exact hr.trans_le ((le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      (by simpa only [R, mul_comm] using dom.rmax_r1))
  have h := norm_deriv_le_of_ball_half hR hg hbound hrball
  rw [deriv_sub_const] at h
  exact h.trans_eq (by field_simp [hR.ne'])

end PGM
