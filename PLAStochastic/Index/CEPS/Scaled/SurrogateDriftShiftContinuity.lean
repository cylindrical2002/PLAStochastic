import PLAStochastic.Index.CEPS.Scaled.SurrogateDriftFactors
import PLAStochastic.Index.CEPS.Scaled.PairComparisonRadius

/-! # Surrogate factors on a cutoff admitting every fixed rightward shift -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledSurrogateFactors_continuousOn_comparison_shift {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 1 ≤ m)
    {b δ : ℝ} (hb : 0 < b) (hδ : δ ≤ dom.pairComparisonScaleBase N M / 4)
    {z : ℂ} (hz : 0 ≤ z.re)
    (hbz : b * (1 + Real.sqrt ‖z‖) < dom.pairComparisonScaleBase N M / 4)
    {S : Set ℝ} (hS : ∀ a ∈ S, |a| ≤ δ / b)
    {s : ℝ} (hs : s ∈ Icc 0 (dom.scaledFrequencyRadius / 4)) :
    ContinuousOn (fun a : ℝ => cepsScaledSurrogateBridge dom ρW N a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledSurrogateEntrance dom ρW N a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledSurrogateHalfBridge dom ρW N a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledSurrogateMarkPrefactor dom ρW N a (z + (s : ℂ)) b) S ∧
      ContinuousOn (fun a : ℝ => cepsScaledSignedRoot D θ ρW a (z + (s : ℂ)) (-1) b) S := by
  have hzs : 0 ≤ (z + (s : ℂ)).re := by simpa only [add_re, ofReal_re] using add_nonneg hz hs.1
  have hcomp := fun a ha => cepsScaledPairComparison_mem_of_cutoff dom hW hθ hD N
    ((cepsSobolev_nonneg m η fW).trans hM) hb hδ hbz (hS a ha)
  have hF : ∀ a ∈ S, (b : ℂ) ∈ ball (0 : ℂ) (dom.trueFrequencyScaleRadius M a (z + (s : ℂ))) :=
    fun a ha => cepsScaledTrueDecay_shift_mem_frequency dom hD M a z (hcomp a ha).1 hs
  have hc := fun a ha => cepsScaledSurrogateFactors_continuousAt_drift dom hW hθ hD hf hη hM
    N hN a hzs hb (hF a ha) ((hcomp a ha).2 s hs)
  refine ⟨fun a ha => (hc a ha).1.continuousWithinAt,
    fun a ha => (hc a ha).2.1.continuousWithinAt,
    fun a ha => (hc a ha).2.2.1.continuousWithinAt,
    fun a ha => (hc a ha).2.2.2.continuousWithinAt, ?_⟩
  intro a ha
  obtain ⟨hμ, hq, hre, _⟩ := cepsScaledTrueFrequency_curve_bounds dom hW hθ hD M a hzs hb (hF a ha)
  exact (cepsScaledSignedRootPlusMinus_continuousAt_drift dom hW hθ hD hb hμ
    (hq.trans (half_le_self dom.q₀_pos.le)) hre).2.continuousWithinAt

end PGM
