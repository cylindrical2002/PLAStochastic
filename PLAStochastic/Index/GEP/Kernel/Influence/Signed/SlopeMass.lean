import PLAStochastic.Index.GEP.Kernel.Influence.Reward.Summation

/-! # Measurable slope partitions of the original physical pin masses -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

def kernelIFLeftTotalPinDensityOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (S : Set ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in S, ENNReal.ofReal (kernelFacetQ eps q) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * H (kernelIFPhysicalSum a q g) ∂iidLaw ν) *
      (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
        (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
          (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) ∂volume.restrict (Ioi (0 : ℝ))

def kernelIFRightTotalPinDensityOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (S : Set ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∫⁻ a in S, ENNReal.ofReal (kernelFacetP eps q) *
    ((∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) * H (kernelIFPhysicalSum a q g) ∂iidLaw ν) *
      (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
        (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) ∂volume.restrict (Ioi (0 : ℝ))

def kernelIFLeftTotalDiracPinDensityOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact if kernelFacetP eps q/x ∈ S then kernelIFLeftTotalDiracPinDensity ν f eps q H x else 0

def kernelIFRightTotalDiracPinDensityOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact if kernelFacetQ eps q/x ∈ S then kernelIFRightTotalDiracPinDensity ν f eps q H x else 0

def kernelIFFacetTotalPinDensityOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (S : Set ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact if kernelFacetEffective eps q then
    if (q.1 : ℕ) ≤ i ∧ i < q.2.1 then
      if (q.1 : ℕ)+1 < q.2.1 then kernelIFLeftTotalPinDensityOn ν f eps S q i H x
      else kernelIFLeftTotalDiracPinDensityOn ν f eps S q H x
    else if (q.2.1 : ℕ) ≤ i ∧ i < q.2.2.1 then
      if (q.2.1 : ℕ)+1 < q.2.2.1 then kernelIFRightTotalPinDensityOn ν f eps S q i H x
      else kernelIFRightTotalDiracPinDensityOn ν f eps S q H x
    else 0
  else 0

def kernelIFTotalPinBlockMassOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (eps : ℝ) (S : Set ℝ)
    (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) (x : ℝ) : ℝ≥0∞ := by
  classical
  exact (∑' p : KernelIFBlockIndex, if A (kernelIFLeftOfBlocks p).1 then
      kernelIFFacetTotalPinDensityOn ν f eps S (kernelIFLeftOfBlocks p).1.2.2
        (kernelIFLeftOfBlocks p).1.2.1 H x else 0) +
    ∑' p : KernelIFBlockIndex, if A (kernelIFRightOfBlocks p).1 then
      kernelIFFacetTotalPinDensityOn ν f eps S (kernelIFRightOfBlocks p).1.2.2
        (kernelIFRightOfBlocks p).1.2.1 H x else 0

def kernelIFTotalPinBoundaryOn (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (H s))
      (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x).toReal -
    (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (-H s))
      (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x).toReal) -
  ((kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (H s))
      (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x).toReal -
    (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (-H s))
      (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x).toReal)

end
end PGM
