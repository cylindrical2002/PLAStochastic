import PLAStochastic.Index.CEPS.Scaled.TrueFrequencyDisc

/-! # Scale-uniform actual bridge frequency derivative budgets

The physical root-size gain is retained before Cauchy differentiation.
Consequently no negative power of the real scale remains in the budget.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueFrequencyBridgeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.normalNegativeBridgeBound * (dom.frequencyRootBound + 2)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueFrequencyBridgeConstant_pos : 0 < dom.trueFrequencyBridgeConstant := by
  have := frequencyRootBound_pos dom hD
  have := cepsChartK_pos hD
  have := cepsNormal_sectorConst_pos dom hW hθ hD
  have := CepsCanonDomain.v_pos hW hθ hD
  unfold CepsCanonDomain.trueFrequencyBridgeConstant CepsCanonDomain.normalNegativeBridgeBound
    CepsCanonDomain.normalBridgeBound
  positivity

include hW hθ hD in
theorem cepsScaledTrueBridge_frequency_disc_budget (M lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.scaledFrequencyRadius) :
    ‖cepsScaledTrueBridge dom ρW lam ζ b‖ ≤
      dom.trueFrequencyBridgeConstant * (1 + |lam| + Real.sqrt ‖z‖) := by
  let μ := b * lam
  let l := (1 + b * lam) / b
  let q := cepsComplexScaledDiscount lam ζ b
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let K := dom.normalNegativeBridgeBound
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  obtain ⟨hμ, _, _, hbMin, hwlo, _, hl⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  obtain ⟨hq, hre⟩ := cepsScaledTrueFrequency_discount_disc dom hW hθ hD M lam hz hb hbs hζ
  have hK : 0 ≤ K := by
    have := cepsChartK_pos hD
    have := cepsNormal_sectorConst_pos dom hW hθ hD
    have := CepsCanonDomain.v_pos hW hθ hD
    dsimp [K, CepsCanonDomain.normalNegativeBridgeBound, CepsCanonDomain.normalBridgeBound]
    positivity
  have hU := cepsNormal_actual_regularBridge_bound_negative dom hW hθ hD hμ hq.le hl hre
  have hμnorm : ‖((b * lam : ℝ) : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hR := cepsScaledRootCoordinate_actual hW hθ hD hb (z := ζ) (dom.μ_lt_chart hμnorm)
  have hqeq : cepsScaledDiscount b lam ζ = q := by
    simp only [q, cepsScaledDiscount, cepsComplexScaledDiscount, ofReal_mul]
  have hRnorm : ‖cepsRootR D θ ρW μ q‖ = b * ‖cepsScaledRootCoordinate D θ ρW lam ζ b‖ := by
    dsimp only [μ]
    rw [← hqeq, ofReal_mul, hR, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  have hroot := cepsScaledRootCoordinate_near_frequency_budget dom hW hθ hD lam z hbMin hζ
  have hinv : 1 / l ≤ 2 * b := by
    have hw : 0 < 1 + b * lam := by linarith
    rw [show 1 / l = b / (1 + b * lam) by dsimp [l]; field_simp]
    exact (div_le_iff₀ hw).mpr (by nlinarith)
  have he := cepsScaledTrueBridge_eq_actual_on_discount_disc dom hW hθ hD hb hμ hq.le
  have he' : (b : ℂ) * cepsScaledTrueBridge dom ρW lam ζ b =
      (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l := by
    simpa only [μ, q, l, ofReal_mul, ofReal_div, ofReal_add, ofReal_one] using! he
  have hn := congrArg norm he'
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hb] at hn
  apply le_of_mul_le_mul_left (a := b) _ hb
  calc
    _ = _ := hn
    _ ≤ K * (‖cepsRootR D θ ρW μ q‖ + 1 / l) := hU
    _ ≤ K * (b * (dom.frequencyRootBound * X) + 2 * b) := by
      rw [hRnorm]
      gcongr
    _ ≤ b * (dom.trueFrequencyBridgeConstant * X) := by
      unfold CepsCanonDomain.trueFrequencyBridgeConstant
      dsimp [K]
      nlinarith [mul_nonneg (mul_nonneg hK hb.le) (by linarith : 0 ≤ X - 1)]

include hW hθ hD in
theorem cepsScaledTrueBridge_frequency_derivative_budget (M lam : ℝ)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z)) (n : ℕ) :
    ‖iteratedDeriv n (fun ζ => cepsScaledTrueBridge dom ρW lam ζ b) z‖ ≤
      ((n.factorial : ℝ) * dom.trueFrequencyBridgeConstant / (dom.scaledFrequencyRadius / 2) ^ n) *
        (1 + |lam| + Real.sqrt ‖z‖) := by
  have hd := cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M lam hz hb hbs
  have he := norm_iteratedDeriv_le_of_ball n (scaledFrequencyRadius_pos dom hD) hd
    (fun ζ hζ => cepsScaledTrueBridge_frequency_disc_budget dom hW hθ hD M lam hz hb hbs hζ)
  exact he.trans_eq (by ring)

end PGM
