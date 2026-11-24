import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopePartition

/-! # The actual signed boundary and its complementary-slope error -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_total_mass_toReal_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ → ℝ≥0∞)
    (A : KernelIFSourceIndex → Prop) (x : ℝ)
    (hfin : kernelIFTotalPinBlockMass ν f eps H A x ≠ ∞) :
    (kernelIFTotalPinBlockMass ν f eps H A x).toReal =
      (kernelIFTotalPinBlockMassOn ν f eps S H A x).toReal +
      (kernelIFTotalPinBlockMassOn ν f eps Sᶜ H A x).toReal := by
  have hh : kernelIFTotalPinBlockMassOn ν f eps S H A x +
      kernelIFTotalPinBlockMassOn ν f eps Sᶜ H A x ≠ ∞ := by
    rwa [kernel_IF_total_block_mass_partition ν f eps hS]
  rw [← kernel_IF_total_block_mass_partition ν f eps hS H A x]
  exact ENNReal.toReal_add (ENNReal.add_ne_top.mp hh).1 (ENNReal.add_ne_top.mp hh).2

theorem kernel_IF_total_signed_slope_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hfin : kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞) :
    kernelIFTotalPinBoundary ν f eps H x =
      kernelIFTotalPinBoundaryOn ν f eps S H x + kernelIFTotalPinBoundaryOn ν f eps Sᶜ H x := by
  have hp (A : KernelIFSourceIndex → Prop) :
      kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (H s)) A x ≠ ∞ :=
    ne_top_of_le_ne_top hfin (kernel_IF_total_block_mass_mono ν f eps x
      (fun s => ENNReal.ofReal_le_ofReal (le_abs_self _)) (fun _ _ => trivial))
  have hn (A : KernelIFSourceIndex → Prop) :
      kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (-H s)) A x ≠ ∞ :=
    ne_top_of_le_ne_top hfin (kernel_IF_total_block_mass_mono ν f eps x
      (fun s => ENNReal.ofReal_le_ofReal (neg_le_abs _)) (fun _ _ => trivial))
  rw [(kernel_IF_total_pin_boundary_eq_masses ν f eps H hx hfin).2]
  rw [kernel_IF_total_mass_toReal_partition ν f eps hS _ _ _ (hp _),
    kernel_IF_total_mass_toReal_partition ν f eps hS _ _ _ (hn _),
    kernel_IF_total_mass_toReal_partition ν f eps hS _ _ _ (hp _),
    kernel_IF_total_mass_toReal_partition ν f eps hS _ _ _ (hn _)]
  unfold kernelIFTotalPinBoundaryOn
  ring

theorem kernel_IF_total_boundaryOn_abs_le (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) (H : ℝ → ℝ) (x : ℝ)
    (hfin : kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞) :
    |kernelIFTotalPinBoundaryOn ν f eps S H x| ≤
      4 * (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal |H s|) (fun _ => True) x).toReal := by
  have hp (A : KernelIFSourceIndex → Prop) := ENNReal.toReal_mono hfin
    (kernel_IF_total_block_massOn_mono ν f eps S x
      (H₁ := fun s => ENNReal.ofReal (H s)) (H₂ := fun s => ENNReal.ofReal |H s|)
      (fun s => ENNReal.ofReal_le_ofReal (le_abs_self _)) (A := A) (B := fun _ => True)
      (fun _ _ => trivial))
  have hn (A : KernelIFSourceIndex → Prop) := ENNReal.toReal_mono hfin
    (kernel_IF_total_block_massOn_mono ν f eps S x
      (H₁ := fun s => ENNReal.ofReal (-H s)) (H₂ := fun s => ENNReal.ofReal |H s|)
      (fun s => ENNReal.ofReal_le_ofReal (neg_le_abs _)) (A := A) (B := fun _ => True)
      (fun _ _ => trivial))
  unfold kernelIFTotalPinBoundaryOn
  apply (abs_sub _ _).trans
  have hL := abs_sub
    (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (H s))
      (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x).toReal
    (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (-H s))
      (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x).toReal
  have hU := abs_sub
    (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (H s))
      (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x).toReal
    (kernelIFTotalPinBlockMassOn ν f eps S (fun s => ENNReal.ofReal (-H s))
      (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x).toReal
  rw [abs_of_nonneg ENNReal.toReal_nonneg, abs_of_nonneg ENNReal.toReal_nonneg] at hL hU
  linarith [hp (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0),
    hn (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0),
    hp (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1),
    hn (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1)]

/-- The far error is controlled by the actual complementary-slope mass;
the deterministic bridge is included according to its real slope. -/
theorem kernel_IF_total_near_error_le (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hfin : kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞) :
    |kernelIFTotalPinBoundary ν f eps H x - kernelIFTotalPinBoundaryOn ν f eps S H x| ≤
      4 * (kernelIFTotalPinBlockMassOn ν f eps Sᶜ (fun s => ENNReal.ofReal |H s|) (fun _ => True) x).toReal := by
  rw [kernel_IF_total_signed_slope_partition ν f eps hS H hx hfin, add_sub_cancel_left]
  exact kernel_IF_total_boundaryOn_abs_le ν f eps Sᶜ H x
    (ne_top_of_le_ne_top hfin (kernel_IF_total_block_massOn_le ν f eps hS.compl _ _ x))

end
end PGM
