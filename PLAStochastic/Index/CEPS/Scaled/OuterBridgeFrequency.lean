import PLAStochastic.Index.CEPS.Scaled.OuterInverseFrequency
import PLAStochastic.ForMathlib.Analysis.Complex.ProductDerivativeNorm

/-! # Full and subtracted bridge frequency derivatives on complex scale disks -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerBridgeFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  2 * dom.outerRootValueFrequencyConstant N M *
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        dom.surrogateSlopePolynomialConstant N M +
    (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) ^ 2 *
      dom.outerInverseFrequencyConstant N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerBridgeFrequencyConstant_pos (N : ℕ) (M : ℝ) :
    0 < dom.outerBridgeFrequencyConstant N M := by
  have := outerRootValueFrequencyConstant_pos dom hW hθ hD N M
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  have := outerInverseFrequencyConstant_pos dom hW hθ hD N M
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.outerBridgeFrequencyConstant
  positivity

include hW hθ hD in
theorem cepsScaledSurrogateRootProduct_outer_frequency_profile {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b sign₁ sign₂ : ℂ} (hs₁ : ‖sign₁‖ ≤ 1) (hs₂ : ‖sign₂‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    let A := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b
      (cepsScaledSignedRoot D θ ρW lam ζ sign₁ b) *
        cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign₂ b) *
          (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹
    DifferentiableAt ℂ A z ∧ ‖deriv A z‖ ≤
      dom.outerBridgeFrequencyConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign₁ b * (1 + b * lam)).re -
          (cepsScaledSignedRoot D θ ρW lam z sign₂ b * (1 + b * lam)).re +
            (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  let f : ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign₁ b)
  let g : ℂ → ℂ := fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign₂ b)
  let i : ℂ → ℂ := fun ζ => (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹
  let w : ℂ := 1 + b * lam
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let W := v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  let P := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign₁ b * w).re)
  let Q := Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign₂ b * w).re)
  let T := Real.exp ((cepsScaledSignedRoot D θ ρW lam z (-1) b * w).re)
  have hW0 : 0 ≤ W := by have := CepsCanonDomain.v_pos hW hθ hD; dsimp [W]; positivity
  have hV := (outerRootValueFrequencyConstant_pos dom hW hθ hD N M).le
  have hI := (surrogateSlopePolynomialConstant_pos dom hW hθ hD N M).le
  have hJ := (outerInverseFrequencyConstant_pos dom hW hθ hD N M).le
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hbC := ball_subset_ball (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)
    (complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb)
  have hne := outerFrequency_ne_origin dom hW hθ hD N M lam z houter
  have hfD : DifferentiableAt ℂ f z := cepsScaledSurrogateG_complex_frequency_differentiableAt dom hW hθ hD hf hη N hN lam hz hne hs₁ hb
  have hgD : DifferentiableAt ℂ g z := cepsScaledSurrogateG_complex_frequency_differentiableAt dom hW hθ hD hf hη N hN lam hz hne hs₂ hb
  obtain ⟨hiD, hiBound⟩ := cepsScaledSurrogateDenominator_outer_inverse_frequency_profile dom hW hθ hD hf hη hM N hN lam hz houter hb
  have hfv : ‖f z‖ ≤ W * P := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hs₁ hbC
  have hgv : ‖g z‖ ≤ W * Q := cepsScaledSurrogateG_root_weighted_budget dom hW hθ hD hf hη hM N hN lam hz hs₂ hbC
  have hiv : ‖i z‖ ≤ dom.surrogateSlopePolynomialConstant N M * X * T :=
    cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N hN lam hz (ball_subset_ball (min_le_left _ _) hb)
  have hfd : ‖deriv f z‖ ≤ dom.outerRootValueFrequencyConstant N M * P :=
    cepsScaledSurrogateG_outer_frequency_budget dom hW hθ hD hf hη hM N hN lam hz houter hs₁ hb
  have hgd : ‖deriv g z‖ ≤ dom.outerRootValueFrequencyConstant N M * Q :=
    cepsScaledSurrogateG_outer_frequency_budget dom hW hθ hD hf hη hM N hN lam hz houter hs₂ hb
  have hd := norm_deriv_three_factor_weighted_le (f := f) (g := g) (h := i)
    hfD hgD hiD hX hW0 hV hI hJ (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _).le
    hfv hgv hiv hfd hgd hiBound
  refine ⟨(hfD.mul hgD).mul hiD, hd.trans_eq ?_⟩
  change dom.outerBridgeFrequencyConstant N M * X ^ 2 * P * Q * T = _
  rw [mul_assoc _ P Q, mul_assoc _ (P * Q) T]
  dsimp only [P, Q, T]
  rw [← Real.exp_add, ← Real.exp_add]
  rfl

include hW hθ hD in
theorem cepsScaledSurrogateBridge_outer_frequency_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) z‖ ≤
      dom.outerBridgeFrequencyConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re) := by
  obtain ⟨_, hd⟩ := cepsScaledSurrogateRootProduct_outer_frequency_profile dom hW hθ hD hf hη hM N hN lam hz houter
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hb
  have he : (fun ζ => cepsScaledSurrogateBridge dom ρW N lam ζ b) =
      -(fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b) *
        cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ (-1) b) *
          (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹) := by
    funext ζ
    simp only [cepsScaledSurrogateBridge, Pi.neg_apply, div_eq_mul_inv, neg_mul]
  rw [he, deriv.neg, norm_neg]
  simpa only [sub_add_cancel] using hd

theorem cepsScaledSurrogateBridgeCorrection_eq_square_of_ne (N : ℕ) (lam : ℝ) (z b : ℂ)
    (hS : cepsScaledSurrogateDenominator dom ρW N lam z b ≠ 0) :
    cepsScaledSurrogateBridgeCorrection dom ρW N lam z b =
      -(cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) ^ 2 /
        cepsScaledSurrogateDenominator dom ρW N lam z b := by
  have hid := sub_smul_dslope (cepsScaledSurrogateG dom ρW N lam z b)
    (cepsScaledSignedRoot D θ ρW lam z (-1) b) (cepsScaledSignedRoot D θ ρW lam z 1 b)
  simp only [smul_eq_mul] at hid
  change (_ - _) * cepsScaledSurrogateDenominator dom ρW N lam z b = _ at hid
  unfold cepsScaledSurrogateBridgeCorrection cepsScaledSurrogateBridge cepsScaledSurrogateHalfBridge
  field_simp
  linear_combination -(cepsScaledSurrogateG dom ρW N lam z b (cepsScaledSignedRoot D θ ρW lam z 1 b)) * hid

include hW hθ hD in
theorem cepsScaledSurrogateBridgeCorrection_outer_frequency_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨ dom.centralFrequencyRadius N M ≤ ‖z‖)
    {b : ℂ} (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) z‖ ≤
      dom.outerBridgeFrequencyConstant N M * (1 + |lam| + Real.sqrt ‖z‖) ^ 2 *
        Real.exp (-(2 * cepsScaledSignedRoot D θ ρW lam z 1 b * (1 + b * lam)).re +
          (cepsScaledSignedRoot D θ ρW lam z (-1) b * (1 + b * lam)).re) := by
  obtain ⟨_, hd⟩ := cepsScaledSurrogateRootProduct_outer_frequency_profile dom hW hθ hD hf hη hM N hN lam hz houter
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hb
  have hS := (cepsScaledSurrogateDenominator_outer_frequency_profile dom hW hθ hD hf hη hM N hN lam hz houter hb).1
  have hS0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N hN lam hz (ball_subset_ball (min_le_left _ _) hb)
  have hev := hS.continuousAt.eventually_ne hS0
  have he : (fun ζ => cepsScaledSurrogateBridgeCorrection dom ρW N lam ζ b) =ᶠ[𝓝 z]
      -(fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b) *
        cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ 1 b) *
          (cepsScaledSurrogateDenominator dom ρW N lam ζ b)⁻¹) := by
    filter_upwards [hev] with ζ hζ
    rw [cepsScaledSurrogateBridgeCorrection_eq_square_of_ne dom N lam ζ b hζ]
    simp only [Pi.neg_apply, div_eq_mul_inv, pow_two, neg_mul]
  rw [he.deriv_eq, deriv.neg, norm_neg]
  apply hd.trans_eq
  congr 2
  rw [two_mul, add_mul, Complex.add_re]
  ring

end PGM
