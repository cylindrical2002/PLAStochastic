import PLAStochastic.Index.CEPS.Scaled.TrueNegativeBridge
import PLAStochastic.ForMathlib.Analysis.Complex.OneSidedDerivative

/-! # Rightward frequency shifts in a fixed actual scale disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.frequencyShiftFactor {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  2 + Real.sqrt dom.scaledFrequencyRadius

def CepsCanonDomain.trueDecayScaleRadius {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (M lam : ℝ) (z : ℂ) : ℝ :=
  min (dom.trueFrequencyScaleRadius M lam z)
    (dom.trueFrequencyScaleBase M / (dom.frequencyShiftFactor * (1 + |lam| + Real.sqrt ‖z‖)))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

theorem frequencyShiftFactor_pos : 0 < dom.frequencyShiftFactor := by
  unfold CepsCanonDomain.frequencyShiftFactor
  positivity

include hW hθ hD in
theorem trueDecayScaleRadius_pos {M : ℝ} (hM : 0 ≤ M) (lam : ℝ) (z : ℂ) :
    0 < dom.trueDecayScaleRadius M lam z := by
  have hR := trueFrequencyScaleRadius_pos dom hW hθ hD hM lam z
  have hbase : 0 < dom.trueFrequencyScaleBase M := by
    simpa only [CepsCanonDomain.trueFrequencyScaleRadius, abs_zero, norm_zero, Real.sqrt_zero,
      add_zero, div_one] using trueFrequencyScaleRadius_pos dom hW hθ hD hM 0 0
  have := frequencyShiftFactor_pos dom
  unfold CepsCanonDomain.trueDecayScaleRadius
  positivity

theorem trueDecayScaleRadius_le_frequency (M lam : ℝ) (z : ℂ) :
    dom.trueDecayScaleRadius M lam z ≤ dom.trueFrequencyScaleRadius M lam z := min_le_left _ _

include hD in
theorem cepsFrequency_sqrt_shift {z : ℂ} {s : ℝ} (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    Real.sqrt ‖z + (s : ℂ)‖ ≤ Real.sqrt ‖z‖ + Real.sqrt dom.scaledFrequencyRadius ∧
      Real.sqrt ‖z‖ ≤ Real.sqrt ‖z + (s : ℂ)‖ + Real.sqrt dom.scaledFrequencyRadius := by
  have hδ := scaledFrequencyRadius_pos dom hD
  have hsδ : s ≤ dom.scaledFrequencyRadius := by linarith [hs.2]
  have hn := norm_add_le z (s : ℂ)
  rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at hn
  have hm := norm_sub_le (z + (s : ℂ)) (s : ℂ)
  rw [add_sub_cancel_right, norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at hm
  have hz := Real.sq_sqrt (norm_nonneg z)
  have hζ := Real.sq_sqrt (norm_nonneg (z + (s : ℂ)))
  have hδsq := Real.sq_sqrt hδ.le
  have hz0 := Real.sqrt_nonneg ‖z‖
  have hζ0 := Real.sqrt_nonneg ‖z + (s : ℂ)‖
  have hδ0 := Real.sqrt_nonneg dom.scaledFrequencyRadius
  constructor <;> nlinarith [mul_nonneg hz0 hδ0, mul_nonneg hζ0 hδ0]

include hD in
theorem cepsFrequency_polynomial_shift (lam : ℝ) (z : ℂ) {s : ℝ}
    (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    1 + |lam| + Real.sqrt ‖z + (s : ℂ)‖ ≤
      dom.frequencyShiftFactor * (1 + |lam| + Real.sqrt ‖z‖) := by
  have hh := (cepsFrequency_sqrt_shift dom hD (z := z) hs).1
  have hX : 1 ≤ 1 + |lam| + Real.sqrt ‖z‖ := by linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  unfold CepsCanonDomain.frequencyShiftFactor
  nlinarith [mul_nonneg (Real.sqrt_nonneg dom.scaledFrequencyRadius) (by linarith :
    0 ≤ (1 + |lam| + Real.sqrt ‖z‖) - 1)]

include hD in
theorem cepsScaledTrueDecay_shift_mem_denominator (M lam : ℝ) (z : ℂ) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z)) {s : ℝ}
    (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    b ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M lam (z + (s : ℂ))) := by
  have hf := frequencyShiftFactor_pos dom
  have ht := (lt_div_iff₀ (mul_pos hf (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖))).mp
    ((mem_ball_zero_iff.mp hb).trans_le (min_le_right _ _))
  have hbase : dom.trueFrequencyScaleBase M ≤ dom.trueDenominatorScaleBase M :=
    (min_le_left _ _).trans (min_le_left _ _)
  apply mem_ball_zero_iff.mpr
  apply (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z + (s : ℂ)‖)).mpr
  exact (mul_le_mul_of_nonneg_left (cepsFrequency_polynomial_shift dom hD lam z hs)
    (norm_nonneg b)).trans_lt (ht.trans_le hbase)

end PGM
