import PLAStochastic.Index.CEPS.Scaled.CanonCurveDerivativeError

/-! # Weighted canonical error along moving discount and root curves -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonWeight_error_curve_differentiableAt {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ξ : ℂ → ℂ} {z : ℂ} (hq : DifferentiableAt ℂ q z)
    (hξ : DifferentiableAt ℂ ξ z) (hq0 : ‖q z‖ ≤ dom.q₀ / 4)
    (hξ0 : ‖ξ z‖ ≤ dom.c₀ / 4) :
    DifferentiableAt ℂ (fun u => cepsCanonTrueWeight dom ρW μ (q u) (ξ u) -
      cepsCanonSurrogateWeight dom ρW N μ (q u) (ξ u)) z := by
  obtain ⟨hA, hB⟩ := cepsCanonWeights_differentiableOn_joint dom hW hθ hD hf hη N hN hμ
  have hx : (q z, ξ z) ∈ ball (0 : ℂ) (dom.q₀ / 2) ×ˢ ball (0 : ℂ) (dom.c₀ / 2) :=
    ⟨mem_ball_zero_iff.mpr (hq0.trans_lt (by linarith [dom.q₀_pos])),
      mem_ball_zero_iff.mpr (hξ0.trans_lt (by linarith [dom.c₀_pos]))⟩
  have hF := ((hA.sub hB) _ hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)
  simpa only [Function.comp_def, Pi.sub_def] using hF.comp z (hq.prodMk hξ)

include hW hθ hD in
theorem cepsCanonWeight_exponential_curve_deriv_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀ / 8) {q r : ℂ → ℂ} {z b w : ℂ}
    (hq : DifferentiableAt ℂ q z) (hr : DifferentiableAt ℂ r z)
    (hq0 : ‖q z‖ ≤ dom.q₀ / 4) (hr0 : ‖b * r z‖ ≤ dom.c₀ / 4) :
    ‖deriv (fun u => exp (-r u * w) *
      (cepsCanonTrueWeight dom ρW μ (q u) (b * r u) -
        cepsCanonSurrogateWeight dom ρW N μ (q u) (b * r u))) z‖ ≤
      Real.exp (-(r z * w).re) * (dom.canonWeightErrorBound N M * |μ| ^ (N + 1)) *
        (‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (dom.q₀ / 8) +
          ‖b‖ * ‖deriv r z‖ / (dom.c₀ / 8)) := by
  let E : ℂ → ℂ := fun u => cepsCanonTrueWeight dom ρW μ (q u) (b * r u) -
    cepsCanonSurrogateWeight dom ρW N μ (q u) (b * r u)
  have hξ : DifferentiableAt ℂ (fun u => b * r u) z := hr.const_mul b
  have hμD : |μ| ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hE : DifferentiableAt ℂ E z :=
    cepsCanonWeight_error_curve_differentiableAt dom hW hθ hD hf hη N (by omega) hμD hq hξ hq0 hr0
  have hED := cepsCanonWeight_error_curve_deriv_budget dom hW hθ hD hf hη hM N hN hμ hq hξ hq0 hr0
  have hE0 := cepsCanonTrueWeight_approx dom hW hθ hD hf hη hM N hN hμ
    (hq0.trans (by linarith [dom.q₀_pos])) (hr0.trans (by linarith [dom.c₀_pos]))
  have hExp := ((hr.hasDerivAt.neg).mul_const w).cexp
  have hd := hExp.mul hE.hasDerivAt
  simp only [Pi.mul_def, Pi.neg_def] at hd
  change ‖deriv (fun u => exp (-r u * w) * E u) z‖ ≤ _
  rw [hd.deriv]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_neg, norm_exp,
    neg_mul, neg_re]
  have hED' : ‖deriv E z‖ ≤ (dom.canonWeightErrorBound N M * |μ| ^ (N + 1)) *
      (‖deriv q z‖ / (dom.q₀ / 8) + ‖b‖ * ‖deriv r z‖ / (dom.c₀ / 8)) := by
    simpa only [(hr.hasDerivAt.const_mul b).deriv, norm_mul, E] using hED
  apply (add_le_add
    (mul_le_mul_of_nonneg_left hE0 (by positivity : 0 ≤ Real.exp (-(r z * w).re) * (‖deriv r z‖ * ‖w‖)))
    (mul_le_mul_of_nonneg_left hED' (Real.exp_pos _).le)).trans_eq
  ring

end PGM
