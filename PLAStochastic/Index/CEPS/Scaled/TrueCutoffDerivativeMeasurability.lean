import PLAStochastic.Index.CEPS.Scaled.TrueDriftShiftContinuity
import PLAStochastic.Index.CEPS.Scaled.PositiveHalfFrequency
import PLAStochastic.ForMathlib.Analysis.Complex.CutoffParameterDerivative

/-! # Actual frequency derivatives with measurable drift cutoffs -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueBridge_deriv_aestronglyMeasurable_cutoff {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) {S : Set ℝ} (hS : MeasurableSet S)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M a z)) :
    AEStronglyMeasurable (S.indicator (fun a => deriv (fun ζ => cepsScaledTrueBridge dom ρW a ζ b) z)) := by
  have hδ := scaledFrequencyRadius_pos dom hD
  obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ (show 0 < dom.scaledFrequencyRadius / 4 by positivity)
  have hs : ∀ n : ℕ, dom.scaledFrequencyRadius / 4 / ((n : ℝ) + 1) ∈
      Icc 0 (dom.scaledFrequencyRadius / 4) := by
    intro n
    exact ⟨by positivity, div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hc := fun n => (cepsScaledTrueFactors_continuousOn_shift dom hW hθ hD hf hm hη hM
    hz hb hbs (hs n)).1
  have hc0 : ContinuousOn (fun a => cepsScaledTrueBridge dom ρW a z b) S := by
    simpa only [ofReal_zero, add_zero] using
      (cepsScaledTrueFactors_continuousOn_shift dom hW hθ hD hf hm hη hM hz hb hbs
        (show (0 : ℝ) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) by constructor <;> positivity)).1
  apply aestronglyMeasurable_cutoff_deriv_param hS hne hlim hc hc0
  intro a ha
  have hbF := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M a z) (hbs a ha)
  exact (cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M a hz hb hbF).differentiableAt
    (ball_mem_nhds z hδ)

include hW hθ hD in
theorem cepsScaledTrueHalfBridge_deriv_aestronglyMeasurable_cutoff {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) {S : Set ℝ} (hS : MeasurableSet S)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M a z))
    (hpos : ∀ a ∈ S, 1 ≤ a) :
    AEStronglyMeasurable (S.indicator (fun a => deriv (fun ζ => cepsScaledTrueHalfBridge dom ρW a ζ b) z)) := by
  have hδ := scaledFrequencyRadius_pos dom hD
  obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ (show 0 < dom.scaledFrequencyRadius / 4 by positivity)
  have hs : ∀ n : ℕ, dom.scaledFrequencyRadius / 4 / ((n : ℝ) + 1) ∈
      Icc 0 (dom.scaledFrequencyRadius / 4) := by
    intro n
    exact ⟨by positivity, div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hc := fun n => (cepsScaledTrueFactors_continuousOn_shift dom hW hθ hD hf hm hη hM
    hz hb hbs (hs n)).2.2.1
  have hc0 : ContinuousOn (fun a => cepsScaledTrueHalfBridge dom ρW a z b) S := by
    simpa only [ofReal_zero, add_zero] using
      (cepsScaledTrueFactors_continuousOn_shift dom hW hθ hD hf hm hη hM hz hb hbs
        (show (0 : ℝ) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) by constructor <;> positivity)).2.2.1
  apply aestronglyMeasurable_cutoff_deriv_param hS hne hlim hc hc0
  intro a ha
  have hbF := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M a z) (hbs a ha)
  exact (cepsScaledTrueHalfBridge_positive_frequency_differentiableOn dom hW hθ hD M a (hpos a ha)
    hz hb hbF).differentiableAt (ball_mem_nhds z (positiveFrequencyRadius_pos dom hW hθ hD))

end PGM
