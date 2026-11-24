import PLAStochastic.Index.CEPS.Normal.ActualMorseData

/-! # Joint holomorphy of the actual Morse-coordinate factor data -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseNormalData_Q_differentiableOn {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => (cepsMorseNormalData D θ ρW μ x.1).Q x.2)
      (ball 0 (dom.rmax / 4) ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hQ := cepsQ_differentiableOn_joint_q_spatial dom hW hθ hD hμ
  have hp : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (cepsMorseDiscount D θ ρW μ x.1, x.2))
      (ball 0 (dom.rmax / 4) ×ˢ ball 0 (dom.c₀ / 2)) := by
    unfold cepsMorseDiscount
    fun_prop
  refine hQ.comp (f := fun x : ℂ × ℂ => (cepsMorseDiscount D θ ρW μ x.1, x.2)) hp ?_
  intro x hx
  refine ⟨?_, ?_⟩
  · have hr : ‖x.1‖ < dom.rmax := by
      have := mem_ball_zero_iff.mp hx.1; have := dom.rmax_pos; linarith
    change ‖cepsMorseMin D θ ρW μ + x.1 ^ 2 - cepsMorseMin D θ ρW μ‖ < dom.rmax ^ 2
    rw [add_sub_cancel_left, norm_pow]
    exact pow_lt_pow_left₀ hr (norm_nonneg _) (by norm_num)
  · apply mem_ball_zero_iff.mpr
    have := mem_ball_zero_iff.mp hx.2
    have := dom.c₀_le; have := dom.ρA_pos; linarith

include hW hθ hD in
theorem cepsMorse_canonL_differentiableOn {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      dom.canonL ρW μ (cepsMorseDiscount D θ ρW μ x.1) x.2)
      (ball 0 (dom.rmax / 4) ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hL := dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ)
  have hp : DifferentiableOn ℂ (fun x : ℂ × ℂ =>
      (x.2, cepsMorseDiscount D θ ρW μ x.1))
      (ball 0 (dom.rmax / 4) ×ˢ ball 0 (dom.c₀ / 2)) := by
    unfold cepsMorseDiscount
    fun_prop
  refine hL.comp (f := fun x : ℂ × ℂ => (x.2, cepsMorseDiscount D θ ρW μ x.1)) hp ?_
  intro x hx
  exact ⟨by have := mem_ball_zero_iff.mp hx.2; linarith [re_le_norm x.2, dom.c₀_pos],
    cepsMorseDiscount_norm_lt dom hW hθ hD hμ' (mem_ball_zero_iff.mp hx.1)⟩

end PGM
