import PLAStochastic.Index.CEPS.Scaled.TrueCutoffDerivativeMeasurability
import PLAStochastic.Index.CEPS.Scaled.TrueCutoffIntegral

/-! # Measurability of the actual complete pair, including its time operator -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTruePair_aestronglyMeasurable_cutoff {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) {S : Set ℝ} (hS : MeasurableSet S)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M a z)) :
    AEStronglyMeasurable (S.indicator (fun a => cepsScaledTruePair dom ρW a z b)) := by
  classical
  have hδ := scaledFrequencyRadius_pos dom hD
  obtain ⟨hB, hH, _, _, _⟩ := cepsScaledTrueFactors_continuousOn_shift dom hW hθ hD hf hm hη hM
    hz hb hbs (s := 0) (by constructor; exact le_rfl; positivity)
  simp only [ofReal_zero, add_zero] at hB hH
  have hmB : AEStronglyMeasurable (S.indicator (fun a => cepsScaledTrueBridge dom ρW a z b)) :=
    (hB.measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hmH : AEStronglyMeasurable (S.indicator (fun a => cepsScaledTrueEntrance dom ρW a z b)) :=
    (hH.measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hmD := cepsScaledTrueBridge_deriv_aestronglyMeasurable_cutoff dom hW hθ hD hf hm hη hM hS hz hb hbs
  have hmE : AEStronglyMeasurable (fun a : ℝ => exp (((b : ℂ) * z) * (1 + (b : ℂ) * a))) :=
    (show Continuous (fun a : ℝ => exp (((b : ℂ) * z) * (1 + (b : ℂ) * a))) by fun_prop).aestronglyMeasurable
  have hmW : AEStronglyMeasurable (fun a : ℝ => (1 / (1 + (b : ℂ) * a) : ℂ)) :=
    (measurable_const.div (show Measurable (fun a : ℝ => (1 + (b : ℂ) * a : ℂ)) from
      (by fun_prop : Continuous (fun a : ℝ => (1 + (b : ℂ) * a : ℂ))).measurable)).aestronglyMeasurable
  have hmP := (hmE.mul (hmH.pow 2)).mul ((hmW.neg.mul hmD).sub (hmB.const_mul (b : ℂ)))
  refine hmP.congr (ae_of_all _ fun a => ?_)
  by_cases ha : a ∈ S <;> simp [ha, cepsScaledTruePair]

include hW hθ hD in
theorem cepsScaledTrueHalfPair_aestronglyMeasurable_cutoff {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) {S : Set ℝ} (hS : MeasurableSet S)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M a z))
    (hpos : ∀ a ∈ S, 1 ≤ a) :
    AEStronglyMeasurable (S.indicator (fun a => cepsScaledTrueHalfPair dom ρW a z b)) := by
  classical
  have hδ := scaledFrequencyRadius_pos dom hD
  obtain ⟨_, _, hB, hP, hA⟩ := cepsScaledTrueFactors_continuousOn_shift dom hW hθ hD hf hm hη hM
    hz hb hbs (s := 0) (by constructor; exact le_rfl; positivity)
  simp only [ofReal_zero, add_zero] at hB hP hA
  have hmB : AEStronglyMeasurable (S.indicator (fun a => cepsScaledTrueHalfBridge dom ρW a z b)) :=
    (hB.measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hmP : Measurable (S.indicator (fun a => cepsScaledTrueMarkPrefactor dom ρW a z b)) :=
    hP.measurable_piecewise continuous_const.continuousOn hS
  have hmA : Measurable (S.indicator (fun a => cepsScaledSignedRoot D θ ρW a z (-1) b)) :=
    hA.measurable_piecewise continuous_const.continuousOn hS
  have hmH : AEStronglyMeasurable (S.indicator (fun a => cepsScaledTrueHalfEntrance dom ρW a z b)) := by
    have hh : AEStronglyMeasurable (fun a : ℝ =>
        S.indicator (fun a => cepsScaledTrueMarkPrefactor dom ρW a z b) a /
          ((b : ℂ) * z - S.indicator (fun a => cepsScaledSignedRoot D θ ρW a z (-1) b) a)) :=
      (hmP.div (measurable_const.sub hmA)).aestronglyMeasurable
    refine hh.congr (ae_of_all _ fun a => ?_)
    by_cases ha : a ∈ S <;> simp [ha, cepsScaledTrueHalfEntrance]
  have hmD := cepsScaledTrueHalfBridge_deriv_aestronglyMeasurable_cutoff dom hW hθ hD hf hm hη hM hS hz hb hbs hpos
  have hmE : AEStronglyMeasurable (fun a : ℝ => exp (((b : ℂ) * z) * (1 + (b : ℂ) * a))) :=
    (show Continuous (fun a : ℝ => exp (((b : ℂ) * z) * (1 + (b : ℂ) * a))) by fun_prop).aestronglyMeasurable
  have hmW : AEStronglyMeasurable (fun a : ℝ => (1 / (1 + (b : ℂ) * a) : ℂ)) :=
    (measurable_const.div (show Measurable (fun a : ℝ => (1 + (b : ℂ) * a : ℂ)) from
      (by fun_prop : Continuous (fun a : ℝ => (1 + (b : ℂ) * a : ℂ))).measurable)).aestronglyMeasurable
  have hmK := (hmE.mul (hmH.pow 2)).mul ((hmW.neg.mul hmD).sub (hmB.const_mul (b : ℂ)))
  refine hmK.congr (ae_of_all _ fun a => ?_)
  by_cases ha : a ∈ S <;> simp [ha, cepsScaledTrueHalfPair, cepsScaledTimeOperator]

include hW hθ hD in
theorem cepsScaledTrueCutoffPair_aestronglyMeasurable {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) {b δ : ℝ} (hb : 0 < b)
    (hδ : δ ≤ dom.trueDecayScaleBase M / 4) {z : ℂ} (hz : 0 ≤ z.re)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.trueDecayScaleBase M / 4) :
    AEStronglyMeasurable (cepsScaledTrueCutoffPair dom ρW b δ z) := by
  classical
  let S : Set ℝ := {a | |a| ≤ δ / b}
  have hS : MeasurableSet S := isClosed_le continuous_abs continuous_const |>.measurableSet
  have hbs : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDecayScaleRadius M a z) := fun _ ha =>
    cepsScaledTrueDecay_mem_of_cutoff dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) hb hδ hbz ha
  have hmP := cepsScaledTruePair_aestronglyMeasurable_cutoff dom hW hθ hD hf hm hη hM hS hz hb hbs
  have hmH := cepsScaledTrueHalfPair_aestronglyMeasurable_cutoff dom hW hθ hD hf hm hη hM
    (hS.inter measurableSet_Ici) hz hb (fun a ha => hbs a ha.1) (fun _ ha => ha.2)
  refine (hmP.sub hmH).congr (ae_of_all _ fun a => ?_)
  by_cases ha : |a| ≤ δ / b <;> by_cases hpos : 1 ≤ a <;>
    simp [cepsScaledTrueCutoffPair, cepsScaledTrueSubtractedPair, S, ha, hpos]

end PGM
