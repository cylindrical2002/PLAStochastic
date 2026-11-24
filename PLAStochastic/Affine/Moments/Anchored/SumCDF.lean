import PLAStochastic.Affine.Moments.Anchored.SupremumSum
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.WedgeSeries.SumCDFSeries
import PLAStochastic.Affine.Moments.Anchored.LaplaceInverseMoments

/-!
# The distribution series of the actual dependent Brownian supremum sum

The integrated wedge probability is differentiated through positive-part
expectations. This proves the closed CDF first and then removes atoms.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem measureReal_realDriftedSum_le (hB : IsBrownianReal B μ) {s : ℝ} (hs : 0 < s) :
    μ.real {ω | realDriftedSum (B · ω) 1 ≤ s} = sumCDFSeries s := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let S : Ω → ℝ := fun ω => realDriftedSum (B · ω) 1
  have hS : AEMeasurable S μ := aemeasurable_realDriftedSum hB
  have hν : ∀ᵐ x ∂μ.map S, 0 ≤ x := (ae_map_iff hS measurableSet_Ici).mpr
    ((realDriftedSum_positive_ae hB).mono (fun _ h => h.le))
  have he : positivePartMean (μ.map S) =ᶠ[𝓝 s] wedgeIntegrated := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact (integral_wedgeSeries_eq_positivePartMean hB hx).symm
  have hd := (hasDerivAt_wedgeIntegrated hs).congr_of_eventuallyEq he
  have h := cdf_eq_of_hasDerivAt_positivePartMean (μ.map S) hν hd
  rw [map_measureReal_apply_of_aemeasurable hS measurableSet_Iic] at h
  exact h

/-- The manuscript's sum CDF series, now attached to the actual Brownian path. -/
theorem measure_realDriftedSum_le (hB : IsBrownianReal B μ) {s : ℝ} (hs : 0 < s) :
    μ {ω | realDriftedSum (B · ω) 1 ≤ s} = ENNReal.ofReal (sumCDFSeries s) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [← measureReal_realDriftedSum_le hB hs, measureReal_def, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

theorem continuousAt_cdf_realDriftedSum (hB : IsBrownianReal B μ) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (cdf (μ.map (fun ω => realDriftedSum (B · ω) 1))) s := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hS := aemeasurable_realDriftedSum hB
  have : IsProbabilityMeasure (μ.map (fun ω => realDriftedSum (B · ω) 1)) :=
    Measure.isProbabilityMeasure_map hS
  have he : (fun x => cdf (μ.map (fun ω => realDriftedSum (B · ω) 1)) x) =ᶠ[𝓝 s]
      sumCDFSeries := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hS measurableSet_Iic]
    exact measureReal_realDriftedSum_le hB hx
  have hv := he.self_of_nhds
  dsimp only at hv
  change Tendsto _ (𝓝 s) (𝓝 _)
  rw [hv]
  exact (continuousAt_sumCDFSeries hs).congr' he.symm

/-- The actual supremum sum has no atoms, including zero and negative values. -/
theorem measure_realDriftedSum_eq_zero (hB : IsBrownianReal B μ) (s : ℝ) :
    μ {ω | realDriftedSum (B · ω) 1 = s} = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hS := aemeasurable_realDriftedSum hB
  let ν := μ.map (fun ω => realDriftedSum (B · ω) 1)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hS
  by_cases hs : 0 < s
  · have hc := continuousAt_cdf_realDriftedSum hB hs
    have hm : ν {s} = 0 := by
      rw [← measure_cdf ν, StieltjesFunction.measure_singleton,
        hc.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]
    rw [Measure.map_apply_of_aemeasurable hS (measurableSet_singleton s)] at hm
    exact hm
  · have he : {ω | realDriftedSum (B · ω) 1 = s} =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [realDriftedSum_positive_ae hB] with ω hω
      apply propext
      change (realDriftedSum (B · ω) 1 = s) ↔ False
      constructor
      · intro h
        exact hs (h ▸ hω)
      · exact False.elim
    rw [measure_congr he, measure_empty]

/-- The inverse-sum law transfers atomlessness to the actual anchored lifetime. -/
theorem measure_anchoredUnitLifetime_eq_zero (hB : IsBrownianReal B μ) (t : ℝ) :
    μ {ω | anchoredUnitLifetime B ω = t} = 0 := by
  by_cases ht : 0 < t
  · have hn : ∀ᵐ ω ∂μ, realDriftedSum (B · ω) 1 ≠ 2 / t := by
      simpa only [ae_iff, not_not] using measure_realDriftedSum_eq_zero hB (2 / t)
    have hi : ∀ᵐ ω ∂μ, 2 / realDriftedSum (B · ω) 1 ≠ t := by
      filter_upwards [hn, realDriftedSum_positive_ae hB] with ω hn hS
      intro he
      apply hn
      apply (eq_div_iff ht.ne').mpr
      nlinarith [(div_eq_iff hS.ne').mp he]
    have he := (identDistrib_anchoredLifetime_real_two_div_realDriftedSum hB).symm.ae_snd
      (p := fun x : ℝ => x ≠ t) (measurableSet_singleton t).compl hi
    simpa only [anchoredUnitLifetime, ae_iff, not_not] using he
  · have he : ∀ᵐ ω ∂μ, anchoredUnitLifetime B ω ≠ t := by
      filter_upwards [anchoredUnitLifetime_positive_ae hB] with ω hω
      intro he
      exact ht (he ▸ hω)
    simpa only [ae_iff, not_not] using he

end BrownianAffine
