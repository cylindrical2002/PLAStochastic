import PLAStochastic.Index.GEP.Kernel.Influence.Pins.Mass

/-! # Scalar physical block densities with both outside rows evaluated exactly -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_left_scalar_pin_density (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hrt : (q.1 : ℕ) ≤ q.2.2.1) (x : ℝ) :
    kernelIFLeftPinDensity ν f eps q i (fun _ => 1) x =
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetQ eps q) *
    (ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-a) q.1 (eps-fluxFacetSign q*eps) *
        krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 a (k-q.2.2.1) (eps-fluxFacetSign q*eps)) *
      (ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
        (i-q.1) (q.2.1-i-1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.2.1-q.2.1)
          (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  unfold kernelIFLeftPinDensity
  simp only [mul_one]
  simp_rw [kernel_IF_outer_lintegral ν eps _ q hrt]

theorem kernel_IF_right_scalar_pin_density (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ)
    (hrt : (q.1 : ℕ) ≤ q.2.2.1) (x : ℝ) :
    kernelIFRightPinDensity ν f eps q i (fun _ => 1) x =
  ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (kernelFacetP eps q) *
    (ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-a) q.1 (eps-fluxFacetSign q*eps) *
        krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 a (k-q.2.2.1) (eps-fluxFacetSign q*eps)) *
      (ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 a (q.2.1-q.1)
        (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps)) *
        ENNReal.ofReal (kernelMarkedFullDens (Icc 0 (2*eps)) ν f 1 a x
          (i-q.2.1) (q.2.2.1-i-1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps)))) := by
  unfold kernelIFRightPinDensity
  simp only [mul_one]
  simp_rw [kernel_IF_outer_lintegral ν eps _ q hrt]

theorem kernel_IF_left_scalar_dirac_density (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (hrt : (q.1 : ℕ) ≤ q.2.2.1) (x : ℝ) :
    kernelIFLeftDiracPinDensity ν f eps q (fun _ => 1) x =
  ENNReal.ofReal (kernelFacetQ eps q/x) *
    (ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-(kernelFacetP eps q/x)) q.1 (eps-fluxFacetSign q*eps) *
        krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 (kernelFacetP eps q/x) (k-q.2.2.1) (eps-fluxFacetSign q*eps)) *
      ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetP eps q/x)
        (q.2.2.1-q.2.1) (eps+fluxFacetSign q*eps) (eps-fluxFacetSign q*eps))) := by
  unfold kernelIFLeftDiracPinDensity
  simp only [mul_one, kernel_IF_outer_lintegral ν eps _ q hrt]

theorem kernel_IF_right_scalar_dirac_density (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (hrt : (q.1 : ℕ) ≤ q.2.2.1) (x : ℝ) :
    kernelIFRightDiracPinDensity ν f eps q (fun _ => 1) x =
  ENNReal.ofReal (kernelFacetP eps q/x) *
    (ENNReal.ofReal (krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) (-1) (-(kernelFacetQ eps q/x)) q.1 (eps-fluxFacetSign q*eps) *
        krSurv (Icc 0 (2*eps)) (ν : Measure ℝ) 1 (kernelFacetQ eps q/x) (k-q.2.2.1) (eps-fluxFacetSign q*eps)) *
      ENNReal.ofReal (krDens (Icc 0 (2*eps)) ν f 1 (kernelFacetQ eps q/x)
        (q.2.1-q.1) (eps-fluxFacetSign q*eps) (eps+fluxFacetSign q*eps))) := by
  unfold kernelIFRightDiracPinDensity
  simp only [mul_one, kernel_IF_outer_lintegral ν eps _ q hrt]

end
end PGM
