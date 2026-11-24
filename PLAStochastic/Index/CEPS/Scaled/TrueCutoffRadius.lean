import PLAStochastic.Index.CEPS.Scaled.TrueSubtractedPair

/-! # A fixed physical drift cutoff pays the actual decay disc -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.trueDecayScaleBase {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (M : ℝ) : ℝ := dom.trueFrequencyScaleBase M / dom.frequencyShiftFactor

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem trueDecayScaleBase_pos {M : ℝ} (hM : 0 ≤ M) : 0 < dom.trueDecayScaleBase M := by
  have hbase : 0 < dom.trueFrequencyScaleBase M := by
    simpa only [CepsCanonDomain.trueFrequencyScaleRadius, abs_zero, norm_zero, Real.sqrt_zero,
      add_zero, div_one] using trueFrequencyScaleRadius_pos dom hW hθ hD hM 0 0
  exact div_pos hbase (frequencyShiftFactor_pos dom)

include hW hθ hD in
theorem cepsScaledTrueDecay_mem_of_cutoff {M : ℝ} (hM : 0 ≤ M) {b δ : ℝ}
    (hb : 0 < b) (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ}
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) {lam : ℝ}
    (hlam : |lam| ≤ δ / b) :
    (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z) := by
  have hB := trueDecayScaleBase_pos dom hW hθ hD hM
  have hH : 1 ≤ dom.frequencyShiftFactor := by
    unfold CepsCanonDomain.frequencyShiftFactor
    linarith [Real.sqrt_nonneg dom.scaledFrequencyRadius]
  have hbase : dom.trueDecayScaleBase M ≤ dom.trueFrequencyScaleBase M :=
    div_le_self (by
      have := mul_pos hB (frequencyShiftFactor_pos dom)
      simpa only [CepsCanonDomain.trueDecayScaleBase, div_mul_cancel₀ _ (frequencyShiftFactor_pos dom).ne'] using this.le) hH
  have hprod := (le_div_iff₀ hb).mp hlam
  have hx : b * (1 + |lam| + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M := by
    nlinarith
  have hdiv := (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z‖)).mpr hx
  rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  apply lt_min
  · exact hdiv.trans_le (div_le_div_of_nonneg_right hbase (by positivity))
  · simpa only [CepsCanonDomain.trueDecayScaleBase, div_div] using hdiv

end PGM
