import PLAStochastic.Index.CEPS.Scaled.CanonDiscountTaylor
import PLAStochastic.Index.CEPS.Scaled.CanonWeightError
import PLAStochastic.Index.CEPS.Normal.ActualQuotientDisc
import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Joint discount-spatial Taylor errors for the actual canonical weight -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonWeights_differentiableOn_joint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonTrueWeight dom ρW μ x.1 x.2)
      (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) ∧
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonSurrogateWeight dom ρW N μ x.1 x.2)
      (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
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
  have hA : DifferentiableOn ℂ (fun x : ℂ × ℂ => dom.canonL ρW μ x.1 x.2)
      (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) :=
    (dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
      (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ)).comp
      (f := fun x : ℂ × ℂ => (x.2, x.1)) (by fun_prop)
      (fun x hx => ⟨by have hz := mem_ball_zero_iff.mp hx.2; linarith [re_le_norm x.2, dom.c₀_pos],
        (mem_ball_zero_iff.mp hx.1).trans (half_lt_self dom.q₀_pos)⟩)
  have hB : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonDriftTaylor dom ρW N μ x.1 x.2)
      (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)) :=
    (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp
      (f := fun x : ℂ × ℂ => ((μ : ℂ), (x.1, x.2))) (by fun_prop)
      (fun x hx => ⟨by have hz := mem_ball_zero_iff.mp hx.2; linarith [re_le_norm x.2, dom.c₀_pos],
        mem_ball_zero_iff.mp hx.1⟩)
  exact ⟨hQ.mul ((hA.const_mul (-2)).cexp), hQ.mul ((hB.const_mul (-2)).cexp)⟩

include hW hθ hD in
theorem cepsCanonWeight_error_mixed_jet_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀ / 8) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 4) (hζ : ‖ζ‖ ≤ dom.c₀ / 4) (j k : ℕ) :
    ‖iteratedDeriv k (fun q' => iteratedDeriv j (fun ζ' =>
      cepsCanonTrueWeight dom ρW μ q' ζ' - cepsCanonSurrogateWeight dom ρW N μ q' ζ') ζ) q‖ ≤
        (k.factorial : ℝ) * ((j.factorial : ℝ) *
          (dom.canonWeightErrorBound N M * |μ| ^ (N + 1)) / (dom.c₀ / 8) ^ j) /
            (dom.q₀ / 8) ^ k := by
  have hμD : |μ| ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  obtain ⟨hA, hB⟩ := cepsCanonWeights_differentiableOn_joint dom hW hθ hD hf hη N (by omega) hμD
  have hqsub : ball q (dom.q₀ / 4) ⊆ ball (0 : ℂ) (dom.q₀ / 2) := by
    intro q' hq'
    apply mem_ball_zero_iff.mpr
    have hn := norm_add_le (q' - q) q
    rw [sub_add_cancel] at hn
    have hdist := mem_ball.mp hq'
    rw [dist_eq_norm] at hdist
    linarith
  have hζsub : ball ζ (dom.c₀ / 4) ⊆ ball (0 : ℂ) (dom.c₀ / 2) := by
    intro ζ' hζ'
    apply mem_ball_zero_iff.mpr
    have hn := norm_add_le (ζ' - ζ) ζ
    rw [sub_add_cancel] at hn
    have hdist := mem_ball.mp hζ'
    rw [dist_eq_norm] at hdist
    linarith
  have hd : DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonTrueWeight dom ρW μ x.2 x.1 -
      cepsCanonSurrogateWeight dom ρW N μ x.2 x.1) (ball ζ (dom.c₀ / 4) ×ˢ ball q (dom.q₀ / 4)) :=
    (hA.sub hB).comp (f := fun x : ℂ × ℂ => (x.2, x.1)) (by fun_prop)
      (fun x hx => ⟨hqsub hx.2, hζsub hx.1⟩)
  have h := norm_iteratedDeriv_iteratedDeriv_le
    (show 0 < dom.c₀ / 4 by have := dom.c₀_pos; positivity)
    (show 0 < dom.q₀ / 4 by have := dom.q₀_pos; positivity) hd
    (fun x hx => cepsCanonTrueWeight_approx dom hW hθ hD hf hη hM N hN hμ
      (mem_ball_zero_iff.mp (hqsub hx.2)).le (mem_ball_zero_iff.mp (hζsub hx.1)).le) j k
  simpa only [show dom.c₀ / 4 / 2 = dom.c₀ / 8 by ring,
    show dom.q₀ / 4 / 2 = dom.q₀ / 8 by ring] using h

end PGM
