import PLAStochastic.Index.CEPS.Scaled.SurrogateDriftShiftContinuity
import PLAStochastic.Index.CEPS.Scaled.KernelFrequencyDifferential
import PLAStochastic.ForMathlib.Analysis.Complex.CutoffParameterDerivative

/-! # Measurability of the surrogate frequency derivatives at approximation cutoff -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateBridge_deriv_aestronglyMeasurable_comparison_cutoff {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {b δ : ℝ} (hb : 0 < b) (hδ : δ ≤ dom.pairComparisonScaleBase N M / 4)
    {z : ℂ} (hz : 0 ≤ z.re)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M / 4)
    {S : Set ℝ} (hS : MeasurableSet S) (hcut : ∀ a ∈ S, |a| ≤ δ / b) :
    AEStronglyMeasurable (S.indicator (fun a => deriv (fun ζ => cepsScaledSurrogateBridge dom ρW N a ζ b) z)) := by
  have hδ0 := scaledFrequencyRadius_pos dom hD
  obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ (show 0 < dom.scaledFrequencyRadius / 4 by positivity)
  have hs : ∀ n : ℕ, dom.scaledFrequencyRadius / 4 / ((n : ℝ) + 1) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) :=
    fun n => ⟨by positivity, div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hc := fun n => (cepsScaledSurrogateFactors_continuousOn_comparison_shift dom hW hθ hD hf hη hM
    N (by omega) hb hδ hz hbz hcut (hs n)).1
  have hc0 : ContinuousOn (fun a => cepsScaledSurrogateBridge dom ρW N a z b) S := by
    simpa only [ofReal_zero, add_zero] using
      (cepsScaledSurrogateFactors_continuousOn_comparison_shift dom hW hθ hD hf hη hM N (by omega)
        hb hδ hz hbz hcut (show (0 : ℝ) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) by constructor <;> positivity)).1
  apply aestronglyMeasurable_cutoff_deriv_param
    (G := fun a ζ => cepsScaledSurrogateBridge dom ρW N a ζ b) (z := z) hS hne hlim hc hc0
  intro a ha
  obtain ⟨hbT, hbS⟩ := cepsScaledPairComparison_mem_of_cutoff dom hW hθ hD N
    ((cepsSobolev_nonneg m η fW).trans hM) hb hδ hbz (hcut a ha)
  have hbF := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M a z) hbT
  have hbE : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M a z) := by
    simpa only [ofReal_zero, add_zero] using hbS 0 (by constructor <;> positivity)
  by_cases ha0 : a = 0
  · subst a
    have heq : (fun ζ => cepsScaledSurrogateBridge dom ρW N 0 ζ b) =
        (fun ζ => cepsScaledTrueBridge dom ρW 0 ζ b) := by
      funext ζ
      exact (cepsScaledTrueBridge_eq_surrogate_of_drift_zero dom ρW N 0 ζ (by simp)).symm
    rw [heq]
    exact (cepsScaledTrueBridge_differentiableOn_frequency_disc dom hW hθ hD M 0 hz hb hbF).differentiableAt
      (ball_mem_nhds z hδ0)
  exact (cepsScaledBridges_frequency_differentiableAt dom hW hθ hD hf hη hM N hN a ha0 hz hb hbF hbE).2.1

include hW hθ hD in
theorem cepsScaledSurrogateHalfBridge_deriv_aestronglyMeasurable_comparison_cutoff {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {b δ : ℝ} (hb : 0 < b) (hδ : δ ≤ dom.pairComparisonScaleBase N M / 4)
    {z : ℂ} (hz : 0 ≤ z.re)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M / 4)
    {S : Set ℝ} (hS : MeasurableSet S) (hcut : ∀ a ∈ S, |a| ≤ δ / b) (hpos : ∀ a ∈ S, 1 ≤ a) :
    AEStronglyMeasurable (S.indicator (fun a => deriv (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N a ζ b) z)) := by
  have hδ0 := scaledFrequencyRadius_pos dom hD
  obtain ⟨hne, hlim⟩ := tendsto_ofReal_div_succ (show 0 < dom.scaledFrequencyRadius / 4 by positivity)
  have hs : ∀ n : ℕ, dom.scaledFrequencyRadius / 4 / ((n : ℝ) + 1) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) :=
    fun n => ⟨by positivity, div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩
  have hc := fun n => (cepsScaledSurrogateFactors_continuousOn_comparison_shift dom hW hθ hD hf hη hM
    N (by omega) hb hδ hz hbz hcut (hs n)).2.2.1
  have hc0 : ContinuousOn (fun a => cepsScaledSurrogateHalfBridge dom ρW N a z b) S := by
    simpa only [ofReal_zero, add_zero] using
      (cepsScaledSurrogateFactors_continuousOn_comparison_shift dom hW hθ hD hf hη hM N (by omega)
        hb hδ hz hbz hcut (show (0 : ℝ) ∈ Icc 0 (dom.scaledFrequencyRadius / 4) by constructor <;> positivity)).2.2.1
  apply aestronglyMeasurable_cutoff_deriv_param
    (G := fun a ζ => cepsScaledSurrogateHalfBridge dom ρW N a ζ b) (z := z) hS hne hlim hc hc0
  intro a ha
  obtain ⟨hbT, hbS⟩ := cepsScaledPairComparison_mem_of_cutoff dom hW hθ hD N
    ((cepsSobolev_nonneg m η fW).trans hM) hb hδ hbz (hcut a ha)
  have hbF := ball_subset_ball (trueDecayScaleRadius_le_frequency dom M a z) hbT
  have hbE : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M a z) := by
    simpa only [ofReal_zero, add_zero] using hbS 0 (by constructor <;> positivity)
  obtain ⟨_, hB, _, hC⟩ := cepsScaledBridges_frequency_differentiableAt dom hW hθ hD hf hη hM N hN a
    (by linarith [hpos a ha]) hz hb hbF hbE
  have heq : (fun ζ => cepsScaledSurrogateHalfBridge dom ρW N a ζ b) =
      (fun ζ => cepsScaledSurrogateBridge dom ρW N a ζ b - cepsScaledSurrogateBridgeCorrection dom ρW N a ζ b) := by
    funext ζ
    unfold cepsScaledSurrogateBridgeCorrection
    ring
  rw [heq]
  exact hB.sub hC

end PGM
