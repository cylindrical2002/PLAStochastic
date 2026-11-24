import PLAStochastic.Index.GEP.Kernel.Influence.Pins.Mass
import PLAStochastic.Index.GEP.Kernel.Output.Identification.FacetSeries

/-! # Absolute mass bounds for the original signed IF series -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem kernel_fluxPositiveDensity_enorm_le (d : ℝ → ℝ≥0∞) (x : ℝ) :
    ‖fluxPositiveDensity d x‖ₑ ≤ d x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · rw [fluxPositiveDensity, indicator_of_mem hx, Real.enorm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  · rw [fluxPositiveDensity, indicator_of_notMem hx, enorm_zero]
    exact bot_le

theorem kernel_IF_oriented_signs_le (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) :
    kernelIFOrientedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) W x +
      kernelIFOrientedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W x ≤
        kernelIFOrientedDensity ν f eps k i (fun _ => True) W x := by
  classical
  unfold kernelIFOrientedDensity
  rw [← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro r
  by_cases hn : fluxFacetCoef eps ((Fintype.equivFin (FluxFacetIndex k)).symm r) i < 0
  · have hp : ¬ 0 < fluxFacetCoef eps ((Fintype.equivFin (FluxFacetIndex k)).symm r) i := by linarith
    simp only [if_pos hn, if_neg hp, if_true, add_zero, le_refl]
  · by_cases hp : 0 < fluxFacetCoef eps ((Fintype.equivFin (FluxFacetIndex k)).symm r) i
    · simp only [if_neg hn, if_pos hp, if_true, zero_add, le_refl]
    · simp only [if_neg hn, if_neg hp, if_true, zero_add, zero_le]

theorem kernel_IF_prefix_enorm_le_mass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (x : ℝ) :
    ‖kernelIFPrefixKernel ν f eps k i x‖ₑ ≤
      kernelIFOrientedDensity ν f eps k i (fun _ => True) (fun _ => 1) x := by
  unfold kernelIFPrefixKernel
  apply enorm_sub_le.trans
  exact (add_le_add (kernel_fluxPositiveDensity_enorm_le _ x)
    (kernel_fluxPositiveDensity_enorm_le _ x)).trans (kernel_IF_oriented_signs_le ν f eps k i _ x)

/-- The original signed infinite series is controlled before `toReal` or any
potential rearrangement. No separate summability hypothesis is needed here. -/
theorem kernel_IF_influence_enorm_le_mass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps x : ℝ) :
    ‖kernelIFInfluence ν f eps x‖ₑ ≤ ∑' b : FluxInfluenceIndex,
      kernelIFOrientedDensity ν f eps b.1 b.2 (fun _ => True) (fun _ => 1) x :=
  enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_le_tsum fun b => kernel_IF_prefix_enorm_le_mass ν f eps b.1 b.2 x)

/-- The mass bound is for the original influence itself and the actual
physical block sum, with all zero-length and Dirac cases already included. -/
theorem kernel_IF_influence_enorm_le_blocks_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u) {eps : ℝ} (heps : 0 ≤ eps) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      ‖kernelIFInfluence ν (fun u => ENNReal.ofReal (f u)) eps x‖ₑ ≤
        kernelIFPinBlockMass ν f eps (fun _ => True) x := by
  filter_upwards [kernel_IF_actual_oriented_mass_eq_blocks_ae ν hf hf0 hfD hfneg hν hpos heps (fun _ => True)] with x hx
  exact (kernel_IF_influence_enorm_le_mass ν _ eps x).trans_eq hx

theorem kernel_IF_influence_abs_le_blocks_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u) {eps : ℝ} (heps : 0 ≤ eps)
    (hfinite : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), kernelIFPinBlockMass ν f eps (fun _ => True) x ≠ ∞) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      |kernelIFInfluence ν (fun u => ENNReal.ofReal (f u)) eps x| ≤
        (kernelIFPinBlockMass ν f eps (fun _ => True) x).toReal := by
  filter_upwards [kernel_IF_influence_enorm_le_blocks_ae ν hf hf0 hfD hfneg hν hpos heps, hfinite] with x hx hfin
  have hh := ENNReal.toReal_mono hfin hx
  simpa only [Real.enorm_eq_ofReal_abs, ENNReal.toReal_ofReal (abs_nonneg _)] using hh

end
end PGM
