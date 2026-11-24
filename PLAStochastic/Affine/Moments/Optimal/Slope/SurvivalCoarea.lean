import PLAStochastic.Affine.Extrema.ExtremalTimeMoment

/-! # The actual optimal-range distribution tested by coarea

The test function is arbitrary, nonnegative and Borel. Thus this is a
distributional identity rather than a formula limited to inverse powers.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def slopeCoareaTest (h : ℝ → ℝ≥0∞) (g : Path 1) : ℝ≥0∞ :=
  ENNReal.ofReal |deriv (slopeRange g) 0| * h (slopeRange g 0)

theorem measurable_slopeCoareaTest {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    Measurable (slopeCoareaTest h) := by
  have hd : Measurable (fun g : Path 1 => deriv (slopeRange g) 0) :=
    measurable_slopeRange_deriv_joint.comp (measurable_id.prodMk measurable_const)
  have hr : Measurable (fun g : Path 1 => slopeRange g 0) :=
    measurable_slopeRange_joint.comp (measurable_id.prodMk measurable_const)
  exact hd.abs.ennreal_ofReal.mul (hh.comp hr)

theorem lintegral_drift_slopeCoareaTest (g : Path 1) (h : ℝ → ℝ≥0∞) :
    (∫⁻ y : ℝ, slopeCoareaTest h (g + y • timePath 1)) =
      2 * ∫⁻ r in Ioi (slopeMinimum g), h r := by
  simp only [slopeCoareaTest, slopeRange_deriv_add_drift, slopeRange_add_drift, zero_sub]
  rw [lintegral_neg_eq_self (μ := volume)
    (fun a : ℝ => ENNReal.ofReal |deriv (slopeRange g) a| * h (slopeRange g a))]
  exact slopeRange_coarea g h

theorem measurable_slopeMinimum : Measurable (slopeMinimum : Path 1 → ℝ) := by
  change Measurable (fun g : Path 1 => slopeMinimum g)
  simp_rw [slopeMinimum_eq_two_optimal]
  exact measurable_const.mul (continuous_optimalError 1).measurable

theorem lintegral_coarea_levels (ν : Measure (Path 1)) [SFinite ν]
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ g, ∫⁻ r in Ioi (slopeMinimum g), h r ∂volume ∂ν) =
      ∫⁻ r : ℝ, h r * ν {g | slopeMinimum g < r} := by
  let K : Path 1 × ℝ → ℝ≥0∞ := fun p =>
    if slopeMinimum p.1 < p.2 then h p.2 else 0
  have hK : Measurable K :=
    (hh.comp measurable_snd).ite
      (measurableSet_lt (measurable_slopeMinimum.comp measurable_fst) measurable_snd)
      measurable_const
  have he (g : Path 1) : (∫⁻ r in Ioi (slopeMinimum g), h r) = ∫⁻ r : ℝ, K (g, r) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    rfl
  simp_rw [he]
  rw [lintegral_lintegral_swap hK.aemeasurable]
  apply lintegral_congr
  intro r
  have hm : MeasurableSet {g : Path 1 | slopeMinimum g < r} :=
    measurable_slopeMinimum measurableSet_Iio
  change (∫⁻ g, ({g | slopeMinimum g < r}.indicator (fun _ => h r)) g ∂ν) = _
  rw [lintegral_indicator hm, lintegral_const, Measure.restrict_apply_univ]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem brownian_bridge_test_swap (hB : IsBrownianReal B μ)
    {Φ : Path 1 → ℝ≥0∞} (hΦ : Measurable Φ) :
    (∫⁻ ω, ∫⁻ y : ℝ, Φ (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ) =
      ∫⁻ y : ℝ, ∫⁻ ω, Φ (bridgeUnitPath B ω + y • timePath 1) ∂μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hG : Measurable (fun p : Path 1 × ℝ => Φ (p.1 + p.2 • timePath 1)) :=
    hΦ.comp measurable_add_endpoint_path
  have hb := aemeasurable_bridgeUnitPath hB
  have hm : Measurable (fun g : Path 1 => ∫⁻ y : ℝ, Φ (g + y • timePath 1)) :=
    hG.lintegral_prod_right
  calc
    _ = ∫⁻ g, ∫⁻ y : ℝ, Φ (g + y • timePath 1) ∂volume ∂μ.map (bridgeUnitPath B) :=
      (lintegral_map' hm.aemeasurable hb).symm
    _ = ∫⁻ y : ℝ, ∫⁻ g, Φ (g + y • timePath 1) ∂μ.map (bridgeUnitPath B) :=
      lintegral_lintegral_swap hG.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro y
      exact lintegral_map' (hG.comp measurable_prodMk_right).aemeasurable hb

/-- Endpoint cancellation applied to the complete coarea test family. -/
theorem brownian_coarea_test_lintegral (hB : IsBrownianReal B μ)
    {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    2 * (∫⁻ r : ℝ, h r * μ {ω | 2 * optimalProcessError B 1 ω < r}) =
      ∫⁻ ω, gaussianEndpointWeight (B 1 ω) *
        slopeCoareaTest h (unitPath (processPath B ω) 1) ∂μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hb := aemeasurable_bridgeUnitPath hB
  have : IsProbabilityMeasure (μ.map (bridgeUnitPath B)) :=
    Measure.isProbabilityMeasure_map hb
  have hG : Measurable (fun p : Path 1 × ℝ =>
      slopeCoareaTest h (p.1 + p.2 • timePath 1)) :=
    (measurable_slopeCoareaTest hh).comp measurable_add_endpoint_path
  have hm : Measurable (fun g : Path 1 =>
      ∫⁻ y : ℝ, slopeCoareaTest h (g + y • timePath 1)) := hG.lintegral_prod_right
  have hmap (r : ℝ) : μ.map (bridgeUnitPath B) {g | slopeMinimum g < r} =
      μ {ω | 2 * optimalProcessError B 1 ω < r} := by
    have hr : MeasurableSet {g : Path 1 | slopeMinimum g < r} :=
      measurable_slopeMinimum measurableSet_Iio
    rw [Measure.map_apply_of_aemeasurable hb hr]
    congr 1
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, slopeMinimum_eq_two_optimal, optimalError_bridgeUnitPath]
  symm
  calc
    _ = ∫⁻ ω, ∫⁻ y : ℝ, slopeCoareaTest h (bridgeUnitPath B ω + y • timePath 1) ∂volume ∂μ := by
      rw [brownian_bridge_test_swap hB (measurable_slopeCoareaTest hh)]
      exact (brownian_bridge_endpoint_lintegral hB (measurable_slopeCoareaTest hh)).symm
    _ = ∫⁻ g, ∫⁻ y : ℝ, slopeCoareaTest h (g + y • timePath 1) ∂volume
        ∂μ.map (bridgeUnitPath B) := (lintegral_map' hm.aemeasurable hb).symm
    _ = 2 * ∫⁻ g, ∫⁻ r in Ioi (slopeMinimum g), h r ∂volume ∂μ.map (bridgeUnitPath B) := by
      simp_rw [lintegral_drift_slopeCoareaTest]
      exact lintegral_const_mul' _ _ (by norm_num)
    _ = _ := by rw [lintegral_coarea_levels _ hh]; simp_rw [hmap]

end BrownianAffine
