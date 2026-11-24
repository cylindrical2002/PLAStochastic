import PLAStochastic.Index.GEP.Kernel.Influence.Reward.Mass
import PLAStochastic.Index.GEP.Kernel.Output.Identification.FacetSeries

/-! # The original signed output boundary as the same physical pin series -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

def kernelIFTotalPinSignedDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  fluxPositiveDensity (kernelIFTotalPinOrientedDensity ν f eps k i A
    (fun s => ENNReal.ofReal (H s))) x -
  fluxPositiveDensity (kernelIFTotalPinOrientedDensity ν f eps k i A
    (fun s => ENNReal.ofReal (-H s))) x

def kernelIFTotalPinPrefix (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (k i : ℕ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  kernelIFTotalPinSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) H x -
  kernelIFTotalPinSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) H x

def kernelIFTotalPinBoundary (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' b : FluxInfluenceIndex, kernelIFTotalPinPrefix ν f eps b.1 b.2 H x

theorem kernel_IF_total_signed_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k)
    (A : FluxFacetIndex k → Prop) [DecidablePred A]
    {H : ℝ → ℝ} (hH : Measurable H) :
    kernelIFSignedDensity ν (fun u => ENNReal.ofReal (f u)) eps k i A
        (fun g => H (gapKeys g k)) =ᵐ[volume]
      kernelIFTotalPinSignedDensity ν f eps k i A H := by
  have hp := kernel_IF_total_oriented_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi A
    (H := fun s => ENNReal.ofReal (H s)) hH.ennreal_ofReal
  have hn := kernel_IF_total_oriented_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi A
    (H := fun s => ENNReal.ofReal (-H s)) hH.neg.ennreal_ofReal
  filter_upwards [kernel_IF_positiveDensity_congr hp, kernel_IF_positiveDensity_congr hn] with x hpx hnx
  exact congrArg₂ (· - ·) hpx hnx

theorem kernel_IF_total_prefix_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {k i : ℕ} (hi : i < k)
    {H : ℝ → ℝ} (hH : Measurable H) :
    kernelIFWeightedPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps k i
        (fun g => H (gapKeys g k)) =ᵐ[volume]
      kernelIFTotalPinPrefix ν f eps k i H := by
  unfold kernelIFWeightedPrefixKernel kernelIFTotalPinPrefix
  exact (kernel_IF_total_signed_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi
    (fun q => fluxFacetCoef eps q i < 0) hH).sub
      (kernel_IF_total_signed_pins_ae ν hf hf0 hfD hfneg hν hpos heps hi
        (fun q => 0 < fluxFacetCoef eps q i) hH)

def kernelIFTriangleEquiv : FluxInfluenceIndex ≃ {a : ℕ × ℕ // a.2 < a.1} where
  toFun b := ⟨(b.1,b.2),b.2.isLt⟩
  invFun a := ⟨a.1.1,⟨a.1.2,a.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem kernel_IF_real_tsum_triangle (F : ℕ → ℕ → ℝ) :
    (∑' a : ℕ × ℕ, if a.2 < a.1 then F a.1 a.2 else 0) =
      ∑' b : FluxInfluenceIndex, F b.1 b.2 := by
  calc
    _ = ∑' a : {a : ℕ × ℕ // a.2 < a.1}, F a.1.1 a.1.2 :=
      by
        convert (tsum_subtype {a : ℕ × ℕ | a.2 < a.1} (fun a => F a.1 a.2)).symm using 1
        apply tsum_congr
        intro a
        by_cases ha : a.2 < a.1
        · simp [Set.indicator, ha]
        · simp [Set.indicator, ha]
        all_goals rfl
    _ = _ := (kernelIFTriangleEquiv.tsum_eq (fun a => F a.1.1 a.1.2)).symm

/-- The original infinite boundary uses exactly these physical pins, with
positive and negative parts of the actual reward retained separately. -/
theorem output_IF_boundary_eq_total_pins_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u)
    (hfD : ∀ u, f u ≤ D) (hfneg : ∀ u, u ≤ 0 → f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u)
    {eps : ℝ} (heps : 0 ≤ eps) {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) :
    outputIFBoundary eps ν (fun u => ENNReal.ofReal (f u)) ψ C =ᵐ[volume]
      kernelIFTotalPinBoundary ν f eps (kernelBoundaryReward ν C ψ) := by
  have hh : ∀ᵐ x ∂volume, ∀ b : FluxInfluenceIndex,
      kernelIFWeightedPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps b.1 b.2
          (fun g => kernelBoundaryReward ν C ψ (gapKeys g b.1)) x =
        kernelIFTotalPinPrefix ν f eps b.1 b.2 (kernelBoundaryReward ν C ψ) x :=
    ae_all_iff.mpr fun b => kernel_IF_total_prefix_pins_ae ν hf hf0 hfD hfneg hν hpos heps b.2.isLt
      (measurable_kernelBoundaryReward hψ ν C)
  filter_upwards [hh] with x hx
  unfold outputIFBoundary outputIFTerm kernelIFTotalPinBoundary
  rw [kernel_IF_real_tsum_triangle (fun k i =>
    kernelIFWeightedPrefixKernel ν (fun u => ENNReal.ofReal (f u)) eps k i
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x)]
  exact tsum_congr hx

end
end PGM
