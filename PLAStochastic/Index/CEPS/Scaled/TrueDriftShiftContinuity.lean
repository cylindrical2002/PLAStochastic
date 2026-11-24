import PLAStochastic.Index.CEPS.Scaled.TrueDriftFactors
import PLAStochastic.Index.CEPS.Scaled.TrueDriftFrequencyShift

/-! # Actual factors on parameter sets admitting the fixed rightward shifts -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueFactors_continuousOn_shift {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) {S : Set ℝ} {z : ℂ} (hz : 0 ≤ z.re)
    {b : ℝ} (hb : 0 < b)
    (hbs : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M a z))
    {s : ℝ} (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    ContinuousOn (fun a : ℝ => cepsScaledTrueBridge dom ρW a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledTrueEntrance dom ρW a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledTrueHalfBridge dom ρW a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledTrueMarkPrefactor dom ρW a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledSignedRoot D θ ρW a (z + (s : ℂ)) (-1) b) S := by
  have hzs : 0 ≤ (z + (s : ℂ)).re := by simpa only [add_re, ofReal_re] using add_nonneg hz hs.1
  have hF : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M a (z + (s : ℂ))) :=
    fun a ha => cepsScaledTrueDecay_shift_mem_frequency dom hD M a z (hbs a ha) hs
  have hc := fun a ha => cepsScaledTrueFactors_continuousAt_drift dom hW hθ hD hf hm hη hM
    a hzs hb (hF a ha)
  refine ⟨fun a ha => (hc a ha).1.continuousWithinAt,
    fun a ha => (hc a ha).2.1.continuousWithinAt,
    fun a ha => (hc a ha).2.2.1.continuousWithinAt,
    fun a ha => (hc a ha).2.2.2.continuousWithinAt, ?_⟩
  intro a ha
  obtain ⟨hμ, hq, hre, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M a hzs hb (hF a ha)
  exact (cepsScaledSignedRootPlusMinus_continuousAt_drift dom hW hθ hD hb hμ
    (hq.trans (half_le_self dom.q₀_pos.le)) hre).2.continuousWithinAt

end PGM
