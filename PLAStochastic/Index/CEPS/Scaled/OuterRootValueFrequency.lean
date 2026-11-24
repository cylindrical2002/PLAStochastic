import PLAStochastic.Index.CEPS.Scaled.OuterFrequencyRegion
import PLAStochastic.Index.CEPS.Scaled.ComplexSurrogateWeightJoint
import PLAStochastic.ForMathlib.Analysis.Complex.ExponentialCurveDerivative

/-! # Weighted frequency derivatives of surrogate moving-root values -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerRootValueFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
    (2 * dom.outerRootFrequencyConstant N M + 2 / (dom.q₀ / 8) +
      dom.outerRootFrequencyConstant N M / (dom.c₀ / 8))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerRootValueFrequencyConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.outerRootValueFrequencyConstant N M := by
  have := (outerFrequency_constants dom hW hθ hD N M).2.1
  have := dom.q₀_pos
  have := dom.c₀_pos
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.outerRootValueFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateG_complex_frequency_differentiableAt {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (hne : lam ≠ 0 ∨ z ≠ 0) {b sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    DifferentiableAt ℂ (fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b
      (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z := by
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hr := (cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz hne hsign hbC).differentiableAt
  obtain ⟨hμ, hq, hξ, _, _⟩ := complexFrequencyCurve_small dom hW hθ hD N M lam hz hsign hb
  have hF := cepsCanonSurrogateWeight_complex_differentiableOn_joint dom hW hθ hD hf hη N hN hμ
  have hx : (cepsComplexScaledDiscount lam z b, b * cepsScaledSignedRoot D θ ρW lam z sign b) ∈
      ball (0 : ℂ) (dom.q₀ / 2) ×ˢ ball (0 : ℂ) (dom.c₀ / 2) :=
    ⟨mem_ball_zero_iff.mpr (hq.trans_lt (by linarith [dom.q₀_pos])),
      mem_ball_zero_iff.mpr (hξ.trans_lt (by linarith [dom.c₀_pos]))⟩
  have hFd := (hF _ hx).differentiableAt ((isOpen_ball.prod isOpen_ball).mem_nhds hx)
  have hqD : DifferentiableAt ℂ (fun ζ => cepsComplexScaledDiscount lam ζ b) z := by
    unfold cepsComplexScaledDiscount
    fun_prop
  have hcomp := hFd.comp z (hqD.prodMk (hr.const_mul b))
  have hExp := ((hr.neg).mul_const (1 + b * lam)).cexp
  simpa only [Function.comp_def, cepsScaledSurrogateG] using! hExp.mul hcomp

include hW hθ hD in
theorem cepsScaledSurrogateG_outer_frequency_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b
      (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z‖ ≤
        dom.outerRootValueFrequencyConstant N M *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + b * lam)).re) := by
  let r : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  let w : ℂ := 1 + b * lam
  let B := v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  let K := dom.outerRootFrequencyConstant N M
  have hB : 0 ≤ B := by have := CepsCanonDomain.v_pos hW hθ hD; dsimp [B]; positivity
  have hK : 0 ≤ K := (outerFrequency_constants dom hW hθ hD N M).2.1.le
  obtain ⟨hμ, hq0, hr0, hb1, hw⟩ := complexFrequencyCurve_small dom hW hθ hD N M lam hz hsign hb
  have hF := cepsCanonSurrogateWeight_complex_differentiableOn_joint dom hW hθ hD hf hη N hN hμ
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hr := (cepsScaledSignedRoot_complex_frequency_hasDerivAt dom hW hθ hD lam hz
    (outerFrequency_ne_origin dom hW hθ hD N M lam z houter) hsign hbC).differentiableAt
  have hqD : HasDerivAt q (b ^ 2 * w) z := by
    simpa only [q, cepsComplexScaledDiscount, w, one_mul, mul_one] using!
      ((hasDerivAt_id' z).const_mul (b ^ 2)).mul_const w
  have hd := norm_deriv_exponential_curve_le (half_pos dom.q₀_pos) (half_pos dom.c₀_pos) hF
    (fun x hx => (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμ
      (mem_ball_zero_iff.mp hx.1).le (mem_ball_zero_iff.mp hx.2).le).2)
    (w := w) hqD.differentiableAt hr
    (by simpa only [show dom.q₀ / 2 / 2 = dom.q₀ / 4 by ring] using hq0)
    (by simpa only [show dom.c₀ / 2 / 2 = dom.c₀ / 4 by ring] using hr0)
  simp only [show dom.q₀ / 2 / 4 = dom.q₀ / 8 by ring,
    show dom.c₀ / 2 / 4 = dom.c₀ / 8 by ring] at hd
  have hdr : ‖deriv r z‖ ≤ K := cepsScaledSignedRoot_outer_frequency_budget dom hW hθ hD N M lam hz houter hsign hb
  have hdq : ‖deriv q z‖ ≤ 2 := by
    rw [hqD.deriv, norm_mul, norm_pow]
    calc
      ‖b‖ ^ 2 * ‖w‖ ≤ 1 ^ 2 * 2 := by gcongr
      _ = 2 := by norm_num
  have ht : ‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (dom.q₀ / 8) +
      ‖b‖ * ‖deriv r z‖ / (dom.c₀ / 8) ≤ 2 * K + 2 / (dom.q₀ / 8) + K / (dom.c₀ / 8) := by
    have := dom.q₀_pos
    have := dom.c₀_pos
    calc
      _ ≤ K * 2 + 2 / (dom.q₀ / 8) + 1 * K / (dom.c₀ / 8) := by gcongr
      _ = _ := by ring
  apply hd.trans
  apply (mul_le_mul_of_nonneg_left ht (mul_nonneg (Real.exp_pos _).le hB)).trans_eq
  unfold CepsCanonDomain.outerRootValueFrequencyConstant
  dsimp only [r, w, B, K]
  ring

end PGM
