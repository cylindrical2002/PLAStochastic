import PLAStochastic.Index.CEPS.Scaled.RootEvaluationFrequencyBudget

/-! # Actual frequency differentiability of the two moving root values -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledG_root_frequency_differentiableAt {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (N : ℕ) (hN : N + 1 ≤ m)
    (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    DifferentiableAt ℂ (fun ζ => cepsScaledTrueG dom ρW lam ζ b
      (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z ∧
    DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b
      (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z := by
  let r : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  have hs : ‖sign‖ ≤ 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hr : DifferentiableAt ℂ r z :=
    (cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz hne hb hbs hs).differentiableAt
  have hq : DifferentiableAt ℂ q z := by unfold q cepsComplexScaledDiscount; fun_prop
  obtain ⟨hμ, hq0, _, _, hp, hm⟩ :=
    cepsScaledTrueFrequency_small_canonical_domain dom hW hθ hD M lam hz hb hbs
  have hr0 : ‖(b : ℂ) * r z‖ ≤ dom.c₀ / 4 := by
    rcases hsign with rfl | rfl
    · exact hp
    · exact hm
  have hx : (q z, (b : ℂ) * r z) ∈ ball (0 : ℂ) (dom.q₀ / 2) ×ˢ ball (0 : ℂ) (dom.c₀ / 2) :=
    ⟨mem_ball_zero_iff.mpr (hq0.trans_lt (by linarith [dom.q₀_pos])),
      mem_ball_zero_iff.mpr (hr0.trans_lt (by linarith [dom.c₀_pos]))⟩
  obtain ⟨hA, hB⟩ := cepsCanonWeights_differentiableOn_joint dom hW hθ hD hf hη N hN
    (hμ.trans (by linarith [dom.μ₀_pos]))
  have hcurve : DifferentiableAt ℂ (fun ζ => (q ζ, (b : ℂ) * r ζ)) z := hq.prodMk (hr.const_mul b)
  have hAd := ((hA _ hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)).comp z hcurve
  have hBd := ((hB _ hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)).comp z hcurve
  have hE : DifferentiableAt ℂ (fun ζ => exp (-r ζ * (1 + (b : ℂ) * lam))) z :=
    (hr.neg.mul_const _).cexp
  constructor
  · simpa only [Function.comp_def, Pi.mul_def, cepsScaledTrueG, r, q] using! hE.mul hAd
  · simpa only [Function.comp_def, Pi.mul_def, cepsScaledSurrogateG, r, q, ofReal_mul] using! hE.mul hBd

end PGM
