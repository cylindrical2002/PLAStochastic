import PLAStochastic.Index.GEP.Kernel.Influence.Pins.AllFacets
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.InfluenceSeries
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.BlockIndex

/-! # The actual infinite influence represented entirely by physical pins -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

def kernelIFPinOrientedDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (x : ℝ) : ℝ≥0∞ :=
  ∑' r : Fin (Fintype.card (FluxFacetIndex k)),
    if A ((Fintype.equivFin (FluxFacetIndex k)).symm r) then
      kernelIFFacetPinDensity ν f eps ((Fintype.equivFin (FluxFacetIndex k)).symm r) i (fun _ => 1) x
    else 0

def kernelIFPinPrefix (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ)
    (k i : ℕ) (x : ℝ) : ℝ :=
  fluxPositiveDensity (kernelIFPinOrientedDensity ν f eps k i
    (fun q => fluxFacetCoef eps q i < 0)) x -
  fluxPositiveDensity (kernelIFPinOrientedDensity ν f eps k i
    (fun q => 0 < fluxFacetCoef eps q i)) x

def kernelIFPinInfluence (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps x : ℝ) : ℝ :=
  ∑' b : FluxInfluenceIndex, kernelIFPinPrefix ν f eps b.1 b.2 x

theorem kernel_IF_oriented_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k)
    (A : FluxFacetIndex k → Prop) [DecidablePred A] :
    kernelIFOrientedDensity ν (fun u => ENNReal.ofReal (f u)) eps k i A (fun _ => 1)
      =ᵐ[volume.restrict (Ioi 0)] kernelIFPinOrientedDensity ν f eps k i A := by
  have hh : ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), ∀ q : FluxFacetIndex k,
      kernelFacetCandidateDensity ν (fun u => ENNReal.ofReal (f u)) eps k i q
        (kernelIFActiveWeight eps k i q (fun _ => 1)) x =
          kernelIFFacetPinDensity ν f eps q i (fun _ => 1) x :=
    (ae_all_iff).mpr fun q =>
      kernel_IF_candidate_facet_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi q measurable_const
  filter_upwards [hh] with x hx
  apply tsum_congr
  intro r
  split_ifs <;> simp only [hx]

theorem kernel_IF_prefix_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k) :
    kernelIFPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps k i =ᵐ[volume]
      kernelIFPinPrefix ν f eps k i := by
  exact (kernel_IF_positiveDensity_congr (kernel_IF_oriented_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi
    (fun q => fluxFacetCoef eps q i < 0))).sub
      (kernel_IF_positiveDensity_congr (kernel_IF_oriented_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi
        (fun q => 0 < fluxFacetCoef eps q i)))

theorem kernel_IF_influence_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) :
    kernelIFInfluence ν (fun u => ENNReal.ofReal (f u)) eps =ᵐ[volume]
      kernelIFPinInfluence ν f eps := by
  have hh : ∀ᵐ x ∂volume, ∀ b : FluxInfluenceIndex,
      kernelIFPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2 x =
        kernelIFPinPrefix ν f eps b.1 b.2 x :=
    (ae_all_iff).mpr fun b => kernel_IF_prefix_pins_ae ν hf hf0 hfD hfneg hν hpos heps b.2.isLt
  filter_upwards [hh] with x hx
  exact tsum_congr hx

/-- Every regular law has the concrete row/pin influence primitive. The finite
prefix series converges absolutely in global `L¹` before its use as a derivative. -/
theorem kernel_IF_pin_influence_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 0 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ f : ℝ → ℝ, Measurable f →
        (∀ u, 0 ≤ f u) → (∀ u, f u ≤ D) → (∀ u ≤ 0, f u = 0) →
        (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)) →
        AEPrimitive (lawJC eps ν) (kernelIFPinInfluence ν f eps) ∧
          Integrable (kernelIFPinInfluence ν f eps) ∧
          Summable (fun b : FluxInfluenceIndex => ∫ x, ‖kernelIFPinPrefix ν f eps b.1 b.2 x‖) := by
  obtain ⟨e0, he0⟩ := kernel_IF_influence_regLaw D θ vlo vhi hD hθ hvlo hv
  refine ⟨max e0 0, le_max_right _ _, ?_⟩
  intro eps heps ν hν f hf hf0 hfD hfneg hνf
  have heps0 : 0 ≤ eps := (le_max_right e0 0).trans heps
  obtain ⟨hp, hi, hs⟩ := he0 eps ((le_max_left _ _).trans heps) ν hν
    (fun u => ENNReal.ofReal (f u)) hf.ennreal_ofReal hνf
  have hh := kernel_IF_influence_pins_ae ν hf hf0 hfD hfneg hνf hν.ae_pos heps0
  refine ⟨flux_aePrimitive_congr_derivative hp hh, hi.congr hh, ?_⟩
  apply hs.congr
  intro b
  exact integral_congr_ae ((kernel_IF_prefix_pins_ae ν hf hf0 hfD hfneg hνf hν.ae_pos heps0 b.2.isLt).fun_comp
    (fun u => ‖u‖))

end
end PGM
