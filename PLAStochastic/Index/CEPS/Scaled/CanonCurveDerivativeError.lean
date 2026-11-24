import PLAStochastic.Index.CEPS.Scaled.CanonMixedTaylor
import PLAStochastic.ForMathlib.Analysis.Complex.PartialDerivChain

/-! # Actual canonical-weight derivative error along a discount-spatial curve -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsCanonWeight_error_curve_deriv_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀ / 8) {q ξ : ℂ → ℂ} {z : ℂ}
    (hq : DifferentiableAt ℂ q z) (hξ : DifferentiableAt ℂ ξ z)
    (hq0 : ‖q z‖ ≤ dom.q₀ / 4) (hξ0 : ‖ξ z‖ ≤ dom.c₀ / 4) :
    ‖deriv (fun u => cepsCanonTrueWeight dom ρW μ (q u) (ξ u) -
      cepsCanonSurrogateWeight dom ρW N μ (q u) (ξ u)) z‖ ≤
        (dom.canonWeightErrorBound N M * |μ| ^ (N + 1)) *
          (‖deriv q z‖ / (dom.q₀ / 8) + ‖deriv ξ z‖ / (dom.c₀ / 8)) := by
  have hμD : |μ| ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  obtain ⟨hA, hB⟩ := cepsCanonWeights_differentiableOn_joint dom hW hθ hD hf hη N (by omega) hμD
  have hx : (q z, ξ z) ∈ ball (0 : ℂ) (dom.q₀ / 2) ×ˢ ball (0 : ℂ) (dom.c₀ / 2) :=
    ⟨mem_ball_zero_iff.mpr (hq0.trans_lt (by linarith [dom.q₀_pos])),
      mem_ball_zero_iff.mpr (hξ0.trans_lt (by linarith [dom.c₀_pos]))⟩
  have hF := ((hA.sub hB) _ hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)
  have hd := hasDerivAt_comp_complex_partials hF hq.hasDerivAt hξ.hasDerivAt
  simp only [Pi.sub_def] at hd
  have hqjet := cepsCanonWeight_error_mixed_jet_budget dom hW hθ hD hf hη hM N hN hμ hq0 hξ0 0 1
  have hξjet := cepsCanonWeight_error_mixed_jet_budget dom hW hθ hD hf hη hM N hN hμ hq0 hξ0 1 0
  simp only [iteratedDeriv_zero, iteratedDeriv_one, Nat.factorial_zero, Nat.factorial_one,
    Nat.cast_one, one_mul, pow_zero, pow_one, div_one] at hqjet hξjet
  rw [hd.deriv]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  apply (add_le_add (mul_le_mul_of_nonneg_right hqjet (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hξjet (norm_nonneg _))).trans_eq
  ring

end PGM
