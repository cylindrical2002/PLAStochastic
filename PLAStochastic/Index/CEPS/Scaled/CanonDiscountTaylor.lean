import PLAStochastic.Index.CEPS.Scaled.CanonDriftTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound

/-! # Discount derivatives preserve the actual real-drift Taylor error order

All differentiability here is in complex discount and spatial variables.
The actual drift remains real; no complex-drift holomorphy is assumed.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonDriftTaylor_discount_differentiableOn {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (μ ζ : ℂ) (hζ : ζ.re < dom.c₀) :
    DifferentiableOn ℂ (fun q => cepsCanonDriftTaylor dom ρW N μ q ζ)
      (ball 0 (dom.q₀ / 2)) := by
  exact (cepsCanonDriftTaylor_differentiableOn dom hW hθ hD hf hη N hN).comp
    (f := fun q : ℂ => (μ, (q, ζ))) (by fun_prop)
    (fun q hq => ⟨hζ, mem_ball_zero_iff.mp hq⟩)

include hW hθ hD in
theorem cepsCanonL_discount_differentiableOn {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    (ζ : ℂ) (hζ : ζ.re < dom.c₀) :
    DifferentiableOn ℂ (fun q => dom.canonL ρW μ q ζ) (ball 0 dom.q₀) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  exact (dom.differentiableOn_cepsCanonL hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμ' (ofReal_im μ)).comp
    (f := fun q : ℂ => (ζ, q)) (by fun_prop)
    (fun q hq => ⟨hζ, mem_ball_zero_iff.mp hq⟩)

include hW hθ hD in
theorem cepsCanonDriftTaylor_discount_error_jet_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) {q ζ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀ / 4) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) (k : ℕ) :
    ‖iteratedDeriv k (fun q' => dom.canonL ρW μ q' ζ -
      cepsCanonDriftTaylor dom ρW N μ q' ζ) q‖ ≤
        (k.factorial : ℝ) * (dom.canonDriftCoeffBound (N + 1) M * |μ| ^ (N + 1)) /
          (dom.q₀ / 8) ^ k := by
  have hzr : ζ.re < dom.c₀ := by linarith [re_le_norm ζ, dom.c₀_pos]
  have hμD : |μ| ≤ dom.μ₀ := by linarith [dom.μ₀_pos]
  have hsub : ball q (dom.q₀ / 4) ⊆ ball (0 : ℂ) (dom.q₀ / 2) := by
    intro q' hq'
    apply mem_ball_zero_iff.mpr
    have hn := norm_add_le (q' - q) q
    rw [sub_add_cancel] at hn
    have hdist := mem_ball.mp hq'
    rw [dist_eq_norm] at hdist
    linarith
  have hA := (cepsCanonL_discount_differentiableOn dom hW hθ hD hμD ζ hzr).mono
    (hsub.trans (ball_subset_ball (half_le_self dom.q₀_pos.le)))
  have hB := (cepsCanonDriftTaylor_discount_differentiableOn dom hW hθ hD hf hη N
    (by omega) μ ζ hzr).mono hsub
  have h := norm_iteratedDeriv_le_of_ball k (show 0 < dom.q₀ / 4 by have := dom.q₀_pos; positivity)
    (hA.sub hB) (fun q' hq' => cepsCanonDriftTaylor_approx dom hW hθ hD hf hη hM N hN hμ
      (mem_ball_zero_iff.mp (hsub hq')).le hζ)
  simpa only [Pi.sub_def, show dom.q₀ / 4 / 2 = dom.q₀ / 8 by ring] using! h

end PGM
