import PLAStochastic.Index.CEPS.Scaled.RootEvaluationDerivativeError
import PLAStochastic.ForMathlib.Analysis.Complex.ExponentialCurveDerivative

/-! # Weighted frequency budgets for actual and surrogate root values -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.rootFrequencyChainConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  2 * dom.rootFrequencyConstant + dom.rootFrequencyConstant / (dom.c₀ / 8) + 2 / (dom.q₀ / 8)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootEvaluation_frequency_deriv_budget {F : ℂ × ℂ → ℂ} {B : ℝ}
    (hF : DifferentiableOn ℂ F (ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2)))
    (hB : ∀ x ∈ ball 0 (dom.q₀ / 2) ×ˢ ball 0 (dom.c₀ / 2), ‖F x‖ ≤ B)
    (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    ‖deriv (fun ζ => exp (-cepsScaledSignedRoot D θ ρW lam ζ sign b * (1 + (b : ℂ) * lam)) *
      F (cepsComplexScaledDiscount lam ζ b, (b : ℂ) * cepsScaledSignedRoot D θ ρW lam ζ sign b)) z‖ * |lam| ≤
        B * dom.rootFrequencyChainConstant * (1 + |lam|) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) := by
  have hR : 0 ≤ dom.rootFrequencyConstant := by
    have := cepsChartK_pos hD
    unfold CepsCanonDomain.rootFrequencyConstant
    positivity
  have hqpos := dom.q₀_pos
  have hcpos := dom.c₀_pos
  have hB0 : 0 ≤ B := (norm_nonneg _).trans
    (hB (0, 0) ⟨mem_ball_self (half_pos hqpos), mem_ball_self (half_pos hcpos)⟩)
  have hs : ‖sign‖ ≤ 1 := by rcases hsign with rfl | rfl <;> norm_num
  let r : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  let w : ℂ := 1 + (b : ℂ) * lam
  obtain ⟨_, hq0, hb1, hw, hp, hm⟩ :=
    cepsScaledTrueFrequency_small_canonical_domain dom hW hθ hD M lam hz hb hbs
  have hr0 : ‖(b : ℂ) * r z‖ ≤ dom.c₀ / 4 := by
    rcases hsign with rfl | rfl
    · exact hp
    · exact hm
  have hr : DifferentiableAt ℂ r z :=
    (cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz hne hb hbs hs).differentiableAt
  have hqD : HasDerivAt q ((b : ℂ) ^ 2 * w) z := by
    simpa only [q, cepsComplexScaledDiscount, w, one_mul, mul_one] using!
      ((hasDerivAt_id' z).const_mul ((b : ℂ) ^ 2)).mul_const w
  have hd := norm_deriv_exponential_curve_le (half_pos hqpos) (half_pos hcpos) hF hB
    (w := w) hqD.differentiableAt hr
    (by simpa only [show dom.q₀ / 2 / 2 = dom.q₀ / 4 by ring] using hq0)
    (by simpa only [show dom.c₀ / 2 / 2 = dom.c₀ / 4 by ring] using hr0)
  simp only [show dom.q₀ / 2 / 4 = dom.q₀ / 8 by ring,
    show dom.c₀ / 2 / 4 = dom.c₀ / 8 by ring] at hd
  have hdr : ‖deriv r z‖ * |lam| ≤ dom.rootFrequencyConstant :=
    cepsScaledSignedRoot_frequency_deriv_drift_budget dom hW hθ hD M lam hz hne hb hbs hs
  have hbN : ‖(b : ℂ)‖ ≤ 1 := by simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hb] using hb1
  have hdq : ‖deriv q z‖ ≤ 2 := by
    rw [hqD.deriv, norm_mul, norm_pow]
    calc
      ‖(b : ℂ)‖ ^ 2 * ‖w‖ ≤ 1 ^ 2 * 2 := by gcongr
      _ = 2 := by norm_num
  have hT : (‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (dom.q₀ / 8) +
      ‖(b : ℂ)‖ * ‖deriv r z‖ / (dom.c₀ / 8)) * |lam| ≤
      dom.rootFrequencyChainConstant * (1 + |lam|) := by
    calc
      _ = ‖w‖ * (‖deriv r z‖ * |lam|) + ‖deriv q z‖ * |lam| / (dom.q₀ / 8) +
          ‖(b : ℂ)‖ * (‖deriv r z‖ * |lam|) / (dom.c₀ / 8) := by ring
      _ ≤ 2 * dom.rootFrequencyConstant + 2 * |lam| / (dom.q₀ / 8) +
          1 * dom.rootFrequencyConstant / (dom.c₀ / 8) := by gcongr
      _ ≤ _ := by
        have hqc : 0 ≤ 2 / (dom.q₀ / 8) := by positivity
        have hrc : 0 ≤ dom.rootFrequencyConstant / (dom.c₀ / 8) := by positivity
        unfold CepsCanonDomain.rootFrequencyChainConstant
        rw [show 2 * |lam| / (dom.q₀ / 8) = (2 / (dom.q₀ / 8)) * |lam| by ring, one_mul]
        nlinarith [abs_nonneg lam, mul_nonneg hR (abs_nonneg lam), mul_nonneg hrc (abs_nonneg lam)]
  calc
    _ ≤ (Real.exp (-(r z * w).re) * B) *
        ((‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (dom.q₀ / 8) +
          ‖(b : ℂ)‖ * ‖deriv r z‖ / (dom.c₀ / 8)) * |lam|) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (abs_nonneg lam)
    _ ≤ (Real.exp (-(r z * w).re) * B) * (dom.rootFrequencyChainConstant * (1 + |lam|)) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by dsimp only [r, w]; ring

include hW hθ hD in
theorem cepsCanonTrueWeight_norm_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ξ : ℂ}
    (hq : ‖q‖ ≤ dom.q₀) (hξ : ‖ξ‖ ≤ dom.c₀ / 2) :
    ‖cepsCanonTrueWeight dom ρW μ q ξ‖ ≤ v * Real.exp (2 * dom.normalLogBound) := by
  have hμn : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith [dom.c₀_pos]) hμn (ofReal_im μ) hq hξ
  have hQ := cepsQ_norm_le_on_rootZone dom hW hθ hD hμn hq
    (show ‖ξ‖ < dom.ρA by have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have he : ‖exp (-2 * dom.canonL ρW μ q ξ)‖ ≤ Real.exp (2 * dom.normalLogBound) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    have hh := (abs_re_le_norm (dom.canonL ρW μ q ξ)).trans hL
    change |(dom.canonL ρW μ q ξ).re| ≤ dom.normalLogBound at hh
    rw [neg_mul, neg_re, show (2 * dom.canonL ρW μ q ξ).re =
      2 * (dom.canonL ρW μ q ξ).re by simp [mul_re]]
    linarith [neg_le_abs (dom.canonL ρW μ q ξ).re]
  rw [cepsCanonTrueWeight, norm_mul]
  exact mul_le_mul hQ he (norm_nonneg _) (CepsCanonDomain.v_pos hW hθ hD).le

include hW hθ hD in
theorem cepsScaledTrueG_root_frequency_deriv_budget {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 1 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    ‖deriv (fun ζ => cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z‖ * |lam| ≤
      (v * Real.exp (2 * dom.normalLogBound)) * dom.rootFrequencyChainConstant * (1 + |lam|) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) := by
  have hμ := (cepsScaledTrueFrequency_small_canonical_domain dom hW hθ hD M lam hz hb hbs).1
  have hμD : |b * lam| ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hF := (cepsCanonWeights_differentiableOn_joint dom hW hθ hD hf hη 0 hm hμD).1
  simpa only [cepsScaledTrueG] using cepsScaledRootEvaluation_frequency_deriv_budget dom hW hθ hD hF
    (fun x hx => cepsCanonTrueWeight_norm_le dom hW hθ hD hμD
      ((mem_ball_zero_iff.mp hx.1).le.trans (half_le_self dom.q₀_pos.le))
      (mem_ball_zero_iff.mp hx.2).le) M lam hz hne hb hbs hsign

include hW hθ hD in
theorem cepsScaledSurrogateG_root_frequency_deriv_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η) (hM : cepsSobolev m η fW ≤ M)
    (N : ℕ) (hN : N + 1 ≤ m) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) (hne : lam ≠ 0 ∨ z ≠ 0)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    ‖deriv (fun ζ => cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z‖ * |lam| ≤
      (v * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        dom.rootFrequencyChainConstant * (1 + |lam|) *
          Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) := by
  have hμ := (cepsScaledTrueFrequency_small_canonical_domain dom hW hθ hD M lam hz hb hbs).1
  have hμn : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ / 8 := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hμD : |b * lam| ≤ dom.μ₀ := hμ.trans (by linarith [dom.μ₀_pos])
  have hF := (cepsCanonWeights_differentiableOn_joint dom hW hθ hD hf hη N hN hμD).2
  simpa only [cepsScaledSurrogateG, ofReal_mul] using
    cepsScaledRootEvaluation_frequency_deriv_budget dom hW hθ hD hF
      (fun x hx => (cepsCanonSurrogateWeight_bounds dom hW hθ hD hf hη hM N hN hμn
        (mem_ball_zero_iff.mp hx.1).le (mem_ball_zero_iff.mp hx.2).le).2) M lam hz hne hb hbs hsign

end PGM
