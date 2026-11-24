import PLAStochastic.Index.CEPS.Scaled.CanonWeight
import PLAStochastic.Index.CEPS.Normal.ActualQuotientDisc

/-! # Joint discount and spatial holomorphy at a fixed complex drift -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonSurrogateWeight_complex_differentiableOn_joint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀ / 8) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonSurrogateWeight dom ρW N μ x.1 x.2)
      (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖μ‖ ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hQ := (cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμ').mono
    (show ball (0 : ℂ) (dom.q₀ / 2) ×ˢ ball (0 : ℂ) (dom.c₀ / 2) ⊆
      {q | ‖q - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2} ×ˢ ball 0 dom.ρA from by
      intro x hx
      constructor
      · change ‖x.1 - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2
        have hq := mem_ball_zero_iff.mp hx.1
        have hm := cepsMorseMin_norm_le_class dom hW hθ hD hμ'
        have hn := norm_sub_le x.1 (cepsMorseMin D θ ρW μ)
        rw [dom.q₀_def] at hq
        nlinarith [sq_pos_of_pos dom.rmax_pos]
      · apply mem_ball_zero_iff.mpr
        have hz := mem_ball_zero_iff.mp hx.2
        linarith [dom.c₀_le, dom.ρA_pos])
  have hL : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftTaylor dom ρW N μ x.1 x.2)
      (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) := by
    have hcurve : DifferentiableOn ℂ (fun x : ℂ × ℂ => (μ, (x.1, x.2)))
        (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) := by fun_prop
    have hc := (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp
      (f := fun x : ℂ × ℂ => (μ, (x.1, x.2))) hcurve
      (fun x hx => ⟨by
        have := mem_ball_zero_iff.mp hx.2
        linarith [re_le_norm x.2, dom.c₀_pos], mem_ball_zero_iff.mp hx.1⟩)
    simpa only [Function.comp_def] using! hc
  exact hQ.mul ((hL.const_mul (-2)).cexp)

end PGM
