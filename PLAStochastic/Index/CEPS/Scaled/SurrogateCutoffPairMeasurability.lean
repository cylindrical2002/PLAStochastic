import PLAStochastic.Index.CEPS.Scaled.SurrogateCutoffDerivativeMeasurability
import PLAStochastic.Index.CEPS.Scaled.CutoffPairError

/-! # Measurability of the complete surrogate approximation integral -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateCutoffPair_aestronglyMeasurable {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {b δ : ℝ} (hb : 0 < b) (hδ : δ ≤ dom.pairComparisonScaleBase N M / 4)
    {z : ℂ} (hz : 0 ≤ z.re)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M / 4) :
    AEStronglyMeasurable (cepsScaledSurrogateCutoffPair dom ρW N b δ z) := by
  classical
  let S : Set ℝ := {a | |a| ≤ δ / b}
  let T : Set ℝ := S ∩ Ici 1
  have hS : MeasurableSet S := isClosed_le continuous_abs continuous_const |>.measurableSet
  have hT : MeasurableSet T := hS.inter measurableSet_Ici
  have hcut : ∀ a ∈ S, |a| ≤ δ / b := fun _ ha => ha
  have hcutT : ∀ a ∈ T, |a| ≤ δ / b := fun _ ha => ha.1
  have hpos : ∀ a ∈ T, 1 ≤ a := fun _ ha => ha.2
  obtain ⟨hB, hH, hBh, hP, hA⟩ := cepsScaledSurrogateFactors_continuousOn_comparison_shift
    dom hW hθ hD hf hη hM N (by omega) hb hδ hz hbz hcut
    (show (0 : ℝ) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) by
      have := scaledFrequencyRadius_pos dom hD
      constructor <;> positivity)
  simp only [ofReal_zero, add_zero] at hB hH hBh hP hA
  have hmB : AEStronglyMeasurable (S.indicator (fun a => cepsScaledSurrogateBridge dom ρW N a z b)) :=
    (hB.measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hmH : AEStronglyMeasurable (S.indicator (fun a => cepsScaledSurrogateEntrance dom ρW N a z b)) :=
    (hH.measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hmD := cepsScaledSurrogateBridge_deriv_aestronglyMeasurable_comparison_cutoff
    dom hW hθ hD hf hη hM N hN hb hδ hz hbz hS hcut
  have hBhT : ContinuousOn (fun a => cepsScaledSurrogateHalfBridge dom ρW N a z b) T :=
    hBh.mono (fun _ ha => ha.1)
  have hPT : ContinuousOn (fun a => cepsScaledSurrogateMarkPrefactor dom ρW N a z b) T :=
    hP.mono (fun _ ha => ha.1)
  have hAT : ContinuousOn (fun a => cepsScaledSignedRoot D θ ρW a z (-1) b) T :=
    hA.mono (fun _ ha => ha.1)
  have hmBh : AEStronglyMeasurable (T.indicator (fun a => cepsScaledSurrogateHalfBridge dom ρW N a z b)) := by
    have hm := (hBhT.measurable_piecewise (g := fun _ => (0 : ℂ)) continuous_const.continuousOn hT).aestronglyMeasurable (μ := volume)
    convert hm using 1
    ext a
    by_cases ha : a ∈ T <;> simp [ha]
  have hmP : Measurable (T.indicator (fun a => cepsScaledSurrogateMarkPrefactor dom ρW N a z b)) := by
    have hm := hPT.measurable_piecewise (g := fun _ => (0 : ℂ)) continuous_const.continuousOn hT
    convert hm using 1
    ext a
    by_cases ha : a ∈ T <;> simp [ha]
  have hmA : Measurable (T.indicator (fun a => cepsScaledSignedRoot D θ ρW a z (-1) b)) := by
    have hm := hAT.measurable_piecewise (g := fun _ => (0 : ℂ)) continuous_const.continuousOn hT
    convert hm using 1
    ext a
    by_cases ha : a ∈ T <;> simp [ha]
  have hmHh : AEStronglyMeasurable (T.indicator (fun a => cepsScaledSurrogateHalfEntrance dom ρW N a z b)) := by
    have hh : AEStronglyMeasurable (fun a : ℝ =>
        T.indicator (fun a => cepsScaledSurrogateMarkPrefactor dom ρW N a z b) a /
          ((b : ℂ) * z - T.indicator (fun a => cepsScaledSignedRoot D θ ρW a z (-1) b) a)) :=
      (hmP.div (measurable_const.sub hmA)).aestronglyMeasurable
    refine hh.congr (ae_of_all _ fun a => ?_)
    by_cases ha : a ∈ T
    · simp only [indicator_of_mem ha]
      exact (cepsScaledSurrogateHalfEntrance_eq_prefactor dom ρW N a z b).symm
    · simp [ha]
  have hmDh := cepsScaledSurrogateHalfBridge_deriv_aestronglyMeasurable_comparison_cutoff
    dom hW hθ hD hf hη hM N hN hb hδ hz hbz hT hcutT hpos
  have hmE : AEStronglyMeasurable (fun a : ℝ => exp (((b : ℂ) * z) * (1 + (b : ℂ) * a))) :=
    (show Continuous (fun a : ℝ => exp (((b : ℂ) * z) * (1 + (b : ℂ) * a))) by fun_prop).aestronglyMeasurable
  have hmW : AEStronglyMeasurable (fun a : ℝ => (1 / (1 + (b : ℂ) * a) : ℂ)) :=
    (measurable_const.div (show Measurable (fun a : ℝ => (1 + (b : ℂ) * a : ℂ)) from
      (by fun_prop : Continuous (fun a : ℝ => (1 + (b : ℂ) * a : ℂ))).measurable)).aestronglyMeasurable
  have hmFull := (hmE.mul (hmH.pow 2)).mul ((hmW.neg.mul hmD).sub (hmB.const_mul (b : ℂ)))
  have hmHalf := (hmE.mul (hmHh.pow 2)).mul ((hmW.neg.mul hmDh).sub (hmBh.const_mul (b : ℂ)))
  refine (hmFull.sub hmHalf).congr (ae_of_all _ fun a => ?_)
  by_cases ha : |a| ≤ δ / b <;> by_cases hpos : 1 ≤ a <;>
    simp [cepsScaledSurrogateCutoffPair, cepsScaledSurrogateSubtractedPair,
      cepsScaledSurrogatePair, cepsScaledSurrogateHalfPair, S, T, ha, hpos]

end PGM
