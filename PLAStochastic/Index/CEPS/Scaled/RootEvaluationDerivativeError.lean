import PLAStochastic.Index.CEPS.Scaled.CanonExponentialCurveError
import PLAStochastic.Index.CEPS.Scaled.TrueFrequencySmallDomain
import PLAStochastic.Index.CEPS.Scaled.RootFrequencyDerivativeBudget
import PLAStochastic.Index.CEPS.Scaled.TrueZero

/-! # Actual versus surrogate frequency errors at the moving roots -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.rootFrequencyConstant {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  4 * cepsChartK D * Real.sqrt (8 * v + 8)

def CepsCanonDomain.rootEvaluationFrequencyErrorConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  dom.canonWeightErrorBound N M *
    (2 * dom.rootFrequencyConstant + dom.rootFrequencyConstant / (dom.c₀ / 8) + 2 / (dom.q₀ / 8))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledRootEvaluation_frequency_deriv_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) :
    ‖deriv (fun ζ =>
      cepsScaledTrueG dom ρW lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b) -
        cepsScaledSurrogateG dom ρW N lam ζ b (cepsScaledSignedRoot D θ ρW lam ζ sign b)) z‖ * |lam| ≤
      dom.rootEvaluationFrequencyErrorConstant N M * (1 + |lam|) *
        Real.exp (-(cepsScaledSignedRoot D θ ρW lam z sign b * (1 + (b : ℂ) * lam)).re) *
          |b * lam| ^ (N + 1) := by
  have hK : 0 ≤ dom.canonWeightErrorBound N M := by
    have hM0 := (cepsSobolev_nonneg m η fW).trans hM
    have := CepsCanonDomain.v_pos hW hθ hD
    have := dom.jetC_nonneg hD (N + 1)
    have := dom.jetC_nonneg hD N
    have := dom.c₀_pos
    unfold CepsCanonDomain.canonWeightErrorBound CepsCanonDomain.canonDriftCoeffBound
    positivity
  have hR : 0 ≤ dom.rootFrequencyConstant := by
    have := cepsChartK_pos hD
    unfold CepsCanonDomain.rootFrequencyConstant
    positivity
  have hqpos : 0 < dom.q₀ / 8 := by exact div_pos dom.q₀_pos (by norm_num)
  have hcpos : 0 < dom.c₀ / 8 := by exact div_pos dom.c₀_pos (by norm_num)
  have hKroot : 0 ≤ 2 * dom.rootFrequencyConstant +
      dom.rootFrequencyConstant / (dom.c₀ / 8) + 2 / (dom.q₀ / 8) := by positivity
  by_cases hl : lam = 0
  · subst lam
    simp only [abs_zero, mul_zero, add_zero, zero_pow (by omega : N + 1 ≠ 0)]
    simp
  have hs : ‖sign‖ ≤ 1 := by rcases hsign with rfl | rfl <;> norm_num
  let r : ℂ → ℂ := fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b
  let q : ℂ → ℂ := fun ζ => cepsComplexScaledDiscount lam ζ b
  let w : ℂ := 1 + (b : ℂ) * lam
  obtain ⟨hμ, hq0, hb1, hw, hp, hm⟩ :=
    cepsScaledTrueFrequency_small_canonical_domain dom hW hθ hD M lam hz hb hbs
  have hr0 : ‖(b : ℂ) * r z‖ ≤ dom.c₀ / 4 := by
    rcases hsign with rfl | rfl
    · exact hp
    · exact hm
  have hr : DifferentiableAt ℂ r z :=
    (cepsScaledSignedRoot_frequency_hasDerivAt dom hW hθ hD M lam hz (Or.inl hl) hb hbs hs).differentiableAt
  have hqD : HasDerivAt q ((b : ℂ) ^ 2 * w) z := by
    simpa only [q, cepsComplexScaledDiscount, w, one_mul, mul_one] using!
      ((hasDerivAt_id' z).const_mul ((b : ℂ) ^ 2)).mul_const w
  have hd := cepsCanonWeight_exponential_curve_deriv_error_budget dom hW hθ hD hf hη hM
    N hN hμ (w := w) hqD.differentiableAt hr hq0 hr0
  have heq : (fun ζ => exp (-r ζ * w) *
      (cepsCanonTrueWeight dom ρW (b * lam) (q ζ) ((b : ℂ) * r ζ) -
        cepsCanonSurrogateWeight dom ρW N (b * lam : ℝ) (q ζ) ((b : ℂ) * r ζ))) =
      (fun ζ => cepsScaledTrueG dom ρW lam ζ b (r ζ) -
        cepsScaledSurrogateG dom ρW N lam ζ b (r ζ)) := by
    funext ζ
    simp only [cepsScaledTrueG, cepsScaledSurrogateG, ofReal_mul, q, w, mul_sub]
  rw [heq] at hd
  have hdr : ‖deriv r z‖ * |lam| ≤ dom.rootFrequencyConstant :=
    cepsScaledSignedRoot_frequency_deriv_drift_budget dom hW hθ hD M lam hz (Or.inl hl) hb hbs hs
  have hbN : ‖(b : ℂ)‖ ≤ 1 := by simpa only [norm_real, Real.norm_eq_abs, abs_of_pos hb] using hb1
  have hdq : ‖deriv q z‖ ≤ 2 := by
    rw [hqD.deriv, norm_mul, norm_pow]
    calc
      ‖(b : ℂ)‖ ^ 2 * ‖w‖ ≤ 1 ^ 2 * 2 := by gcongr
      _ = 2 := by norm_num
  have hT : (‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (dom.q₀ / 8) +
      ‖(b : ℂ)‖ * ‖deriv r z‖ / (dom.c₀ / 8)) * |lam| ≤
      (2 * dom.rootFrequencyConstant + dom.rootFrequencyConstant / (dom.c₀ / 8) +
        2 / (dom.q₀ / 8)) * (1 + |lam|) := by
    calc
      _ = ‖w‖ * (‖deriv r z‖ * |lam|) +
          ‖deriv q z‖ * |lam| / (dom.q₀ / 8) +
          ‖(b : ℂ)‖ * (‖deriv r z‖ * |lam|) / (dom.c₀ / 8) := by ring
      _ ≤ 2 * dom.rootFrequencyConstant + 2 * |lam| / (dom.q₀ / 8) +
          1 * dom.rootFrequencyConstant / (dom.c₀ / 8) := by gcongr
      _ ≤ _ := by
        have hqc : 0 ≤ 2 / (dom.q₀ / 8) := by positivity
        have hrc : 0 ≤ dom.rootFrequencyConstant / (dom.c₀ / 8) := by positivity
        rw [show 2 * |lam| / (dom.q₀ / 8) = (2 / (dom.q₀ / 8)) * |lam| by ring, one_mul]
        nlinarith [abs_nonneg lam, mul_nonneg hR (abs_nonneg lam), mul_nonneg hrc (abs_nonneg lam)]
  calc
    _ ≤ (Real.exp (-(r z * w).re) * (dom.canonWeightErrorBound N M * |b * lam| ^ (N + 1))) *
        ((‖deriv r z‖ * ‖w‖ + ‖deriv q z‖ / (dom.q₀ / 8) +
          ‖(b : ℂ)‖ * ‖deriv r z‖ / (dom.c₀ / 8)) * |lam|) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hd (abs_nonneg lam)
    _ ≤ (Real.exp (-(r z * w).re) * (dom.canonWeightErrorBound N M * |b * lam| ^ (N + 1))) *
        ((2 * dom.rootFrequencyConstant + dom.rootFrequencyConstant / (dom.c₀ / 8) +
          2 / (dom.q₀ / 8)) * (1 + |lam|)) :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ = _ := by unfold CepsCanonDomain.rootEvaluationFrequencyErrorConstant; dsimp only [r, w]; ring

end PGM
