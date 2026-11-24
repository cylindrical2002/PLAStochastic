import PLAStochastic.Index.CEPS.Scaled.TruePositiveBridge
import PLAStochastic.Index.CEPS.Normal.ActualRootDifferential

/-! # A common non-merging frequency disc on the positive drift tail -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.positiveFrequencyRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  min dom.scaledFrequencyRadius (cepsVarLo D / (72 * v ^ 2))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem positiveFrequencyRadius_pos : 0 < dom.positiveFrequencyRadius := by
  have := CepsCanonDomain.v_pos hW hθ hD
  have := cepsVarLo_pos hD
  exact lt_min (scaledFrequencyRadius_pos dom hD) (by positivity)

theorem positiveFrequencyRadius_le : dom.positiveFrequencyRadius ≤ dom.scaledFrequencyRadius :=
  min_le_left _ _

include hW hθ hD in
theorem cepsMorseMin_drift_squared_lower {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) :
    cepsVarLo D / (9 * v ^ 2) * μ ^ 2 ≤ -(cepsMorseMin D θ ρW μ).re := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hlo := cepsVarLo_pos hD
  have hμn : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc := cepsMorseCenter_drift_le dom hW hθ hD hμn
  rw [norm_real, Real.norm_eq_abs] at hc
  have hc2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg μ) hc 2) hlo.le
  rw [mul_pow, div_pow, sq_abs] at hc2
  have hm := mul_le_mul_of_nonneg_left (cepsMorseMin_center_lower dom hW hθ hD hμ)
    (sq_nonneg (3 * v))
  have hs : cepsVarLo D * μ ^ 2 ≤ 9 * v ^ 2 * (-(cepsMorseMin D θ ρW μ).re) := by
    nlinarith
  rw [div_mul_eq_mul_div]
  exact (div_le_iff₀ (by positivity : 0 < 9 * v ^ 2)).mpr (by nlinarith [hs])

include hW hθ hD in
theorem cepsScaledPositiveFrequency_mem_slitPlane (M lam : ℝ) (hlam : 1 ≤ lam)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M lam z))
    {ζ : ℂ} (hζ : ζ ∈ ball z dom.positiveFrequencyRadius) :
    cepsComplexScaledDiscount lam ζ b - cepsMorseMin D θ ρW (b * lam : ℝ) ∈ slitPlane := by
  obtain ⟨hμ, _, _, _, hwlo, hwhi, _⟩ :=
    cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M lam hz hb hbs
  have hr := positiveFrequencyRadius_pos dom hW hθ hD
  have hdist : ‖ζ - z‖ < dom.positiveFrequencyRadius := by
    simpa only [dist_eq_norm] using mem_ball.mp hζ
  have hζre : -dom.positiveFrequencyRadius < ζ.re := by
    have hneg := (neg_le_abs (ζ - z).re).trans (abs_re_le_norm _)
    rw [sub_re] at hneg
    linarith
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have ha : 0 < cepsVarLo D / (9 * v ^ 2) := div_pos (cepsVarLo_pos hD) (by positivity)
  have hmin := cepsMorseMin_drift_squared_lower dom hW hθ hD hμ
  have hmin' : (cepsVarLo D / (9 * v ^ 2)) * b ^ 2 ≤
      -(cepsMorseMin D θ ρW (b * lam : ℝ)).re := by
    have hLamSq : 1 ≤ lam ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hLamSq (mul_nonneg ha.le (sq_nonneg b))
    nlinarith
  have hrsmall : dom.positiveFrequencyRadius ≤ (cepsVarLo D / (9 * v ^ 2)) / 8 := by
    exact (min_le_right _ _).trans_eq (by ring)
  have hw : 0 < 1 + b * lam := by linarith
  have hqre : -(2 * b ^ 2 * dom.positiveFrequencyRadius) <
      (cepsComplexScaledDiscount lam ζ b).re := by
    have hh := mul_lt_mul_of_pos_left hζre (mul_pos (sq_pos_of_pos hb) hw)
    have hh' := mul_le_mul_of_nonneg_left hwhi (mul_nonneg (sq_nonneg b) hr.le)
    unfold cepsComplexScaledDiscount
    simp only [mul_re, ofReal_re, ofReal_im, mul_im, pow_two, mul_zero, zero_mul,
      sub_zero, add_re, one_re, add_im, one_im, add_zero]
    nlinarith
  rw [mem_slitPlane_iff]
  left
  rw [sub_re]
  have hh := mul_le_mul_of_nonneg_left hrsmall (sq_nonneg b)
  nlinarith [mul_pos ha (sq_pos_of_pos hb)]

end PGM
