import PLAStochastic.Index.CEPS.Scaled.TrueCutoffRadius
import PLAStochastic.Index.CEPS.Scaled.PairPolynomialRadius
import PLAStochastic.Index.CEPS.Scaled.TrueDriftFrequencyShift

/-! # Approximation cutoffs inside the fixed actual drift domain -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.pairComparisonScaleBase {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.trueDecayScaleBase M)
    (dom.pairPolynomialScaleBase N M / dom.frequencyShiftFactor)

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem pairComparisonScaleBase_pos (N : ℕ) {M : ℝ} (hM : 0 ≤ M) :
    0 < dom.pairComparisonScaleBase N M :=
  lt_min (trueDecayScaleBase_pos dom hW hθ hD hM)
    (div_pos (pairPolynomialScaleBase_pos dom hW hθ hD N M) (frequencyShiftFactor_pos dom))

include hW hθ hD in
theorem cepsScaledPairComparison_mem_of_cutoff (N : ℕ) {M : ℝ} (hM : 0 ≤ M)
    {b δ : ℝ} (hb : 0 < b) (hδ : δ ≤ dom.pairComparisonScaleBase N M / 4)
    {z : ℂ} (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M / 4)
    {lam : ℝ} (hlam : |lam| ≤ δ / b) :
    (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M lam z) ∧
      ∀ s ∈ Icc 0 (dom.scaledFrequencyRadius / 4),
        (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam (z + (s : ℂ))) := by
  have hbase := pairComparisonScaleBase_pos dom hW hθ hD N hM
  have hle : dom.pairComparisonScaleBase N M ≤ dom.trueDecayScaleBase M := min_le_left _ _
  refine ⟨cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD hM hb
    (hδ.trans (div_le_div_of_nonneg_right hle (by norm_num)))
    (hbz.trans_le (div_le_div_of_nonneg_right hle (by norm_num))) hlam, ?_⟩
  have hx : b * (1 + |lam| + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M := by
    have hp := (le_div_iff₀ hb).mp hlam
    nlinarith
  have hp := (lt_div_iff₀ (frequencyShiftFactor_pos dom)).mp
    (hx.trans_le (min_le_right _ _))
  intro s hs
  have hshift := cepsFrequency_polynomial_shift dom hD lam z hs
  have hxs : b * (1 + |lam| + Real.sqrt ‖z + (s : ℂ)‖) < dom.pairPolynomialScaleBase N M :=
    (mul_le_mul_of_nonneg_left hshift hb.le).trans_lt (by nlinarith)
  apply ball_subset_ball (pairPolynomialScaleRadius_le dom hW hθ hD N M lam (z + (s : ℂ))).2
  rw [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb]
  exact (lt_div_iff₀ (by positivity : 0 < 1 + |lam| + Real.sqrt ‖z + (s : ℂ)‖)).mpr hxs

end PGM
