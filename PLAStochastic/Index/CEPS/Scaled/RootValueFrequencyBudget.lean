import PLAStochastic.Index.CEPS.Scaled.RootEvaluationDifferential

/-! # Moving-root value and value-error budgets on the fixed actual frequency domain -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledG_root_frequency_value_budgets {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    ‖cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤
        (v * Real.exp (2 * dom.normalLogBound)) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) ∧
    ‖cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤
        (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) ∧
    ‖cepsScaledTrueG dom ρW lam z b (cepsScaledSignedRoot D θ ρW lam z sign b) -
      cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z sign b)‖ ≤
        dom.canonWeightErrorBound N M *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) *
            |b * lam| ^ (N + 1) := by
  obtain ⟨hμ, hq0, _, _, hp, hm⟩ :=
    cepsScaledTrueFrequency_small_canonical_domain dom hW hθ hD M lam hz hb hbs
  have hr0 : ‖(b : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b‖ ≤ dom.c₀ / 4 := by
    rcases hsign with rfl | rfl
    · exact hp
    · exact hm
  have hq : ‖cepsComplexScaledDiscount lam z b‖ ≤ dom.q₀ / 2 := hq0.trans (by linarith [dom.q₀_pos])
  have hr : ‖(b : ℂ) * cepsScaledSignedRoot D θ ρW lam z sign b‖ ≤ dom.c₀ / 2 :=
    hr0.trans (by linarith [dom.c₀_pos])
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ / 8 := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hA := cepsCanonTrueWeight_norm_le dom hW hθ hD (hμ.trans (by linarith [dom.μ₀_pos]))
    (hq.trans (half_le_self dom.q₀_pos.le)) hr
  have hB := (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N (by omega) hμn hq hr).2
  have hE := cepsCanonTrueWeight_approx dom hW hθ hD hf hη hM N hN hμ hq hr
  rw [ofReal_mul] at hB hE
  refine ⟨?_, ?_, ?_⟩
  · rw [cepsScaledTrueG, norm_mul, norm_exp, neg_mul, neg_re]
    exact (mul_le_mul_of_nonneg_left hA (Real.exp_pos _).le).trans_eq (by ring)
  · rw [cepsScaledSurrogateG, norm_mul, norm_exp, neg_mul, neg_re]
    exact (mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le).trans_eq (by ring)
  · unfold cepsScaledTrueG cepsScaledSurrogateG
    rw [← mul_sub, norm_mul, norm_exp, neg_mul, neg_re]
    exact (mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le).trans_eq (by ring)

end PGM
