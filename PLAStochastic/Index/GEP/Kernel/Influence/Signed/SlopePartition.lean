import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopeMass

/-! # Exact near/far partition before any signed regrouping -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_left_total_pin_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) {k : ℕ} (q : FluxFacetIndex k)
    (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFLeftTotalPinDensityOn ν f eps S q i H x +
      kernelIFLeftTotalPinDensityOn ν f eps Sᶜ q i H x = kernelIFLeftTotalPinDensity ν f eps q i H x :=
  lintegral_add_compl _ hS

theorem kernel_IF_right_total_pin_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) {k : ℕ} (q : FluxFacetIndex k)
    (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFRightTotalPinDensityOn ν f eps S q i H x +
      kernelIFRightTotalPinDensityOn ν f eps Sᶜ q i H x = kernelIFRightTotalPinDensity ν f eps q i H x :=
  lintegral_add_compl _ hS

theorem kernel_IF_left_total_dirac_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFLeftTotalDiracPinDensityOn ν f eps S q H x +
      kernelIFLeftTotalDiracPinDensityOn ν f eps Sᶜ q H x = kernelIFLeftTotalDiracPinDensity ν f eps q H x := by
  classical
  unfold kernelIFLeftTotalDiracPinDensityOn
  by_cases h : kernelFacetP eps q/x ∈ S <;> simp [h]

theorem kernel_IF_right_total_dirac_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k)
    (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFRightTotalDiracPinDensityOn ν f eps S q H x +
      kernelIFRightTotalDiracPinDensityOn ν f eps Sᶜ q H x = kernelIFRightTotalDiracPinDensity ν f eps q H x := by
  classical
  unfold kernelIFRightTotalDiracPinDensityOn
  by_cases h : kernelFacetQ eps q/x ∈ S <;> simp [h]

theorem kernel_IF_total_facet_pin_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) {k : ℕ} (q : FluxFacetIndex k)
    (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFFacetTotalPinDensityOn ν f eps S q i H x +
      kernelIFFacetTotalPinDensityOn ν f eps Sᶜ q i H x = kernelIFFacetTotalPinDensity ν f eps q i H x := by
  classical
  unfold kernelIFFacetTotalPinDensityOn kernelIFFacetTotalPinDensity
  split_ifs
  · exact kernel_IF_left_total_pin_partition ν f eps hS q i H x
  · exact kernel_IF_left_total_dirac_partition ν f eps S q H x
  · exact kernel_IF_right_total_pin_partition ν f eps hS q i H x
  · exact kernel_IF_right_total_dirac_partition ν f eps S q H x
  · exact zero_add 0
  · exact zero_add 0

theorem kernel_IF_total_facet_pin_univ (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (H : ℝ → ℝ≥0∞) (x : ℝ) :
    kernelIFFacetTotalPinDensityOn ν f eps univ q i H x = kernelIFFacetTotalPinDensity ν f eps q i H x := by
  classical
  unfold kernelIFFacetTotalPinDensityOn kernelIFFacetTotalPinDensity
    kernelIFLeftTotalPinDensityOn kernelIFRightTotalPinDensityOn
    kernelIFLeftTotalDiracPinDensityOn kernelIFRightTotalDiracPinDensityOn
    kernelIFLeftTotalPinDensity kernelIFRightTotalPinDensity
  simp only [Measure.restrict_univ, mem_univ, if_true]

theorem kernel_IF_total_block_mass_partition (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ → ℝ≥0∞)
    (A : KernelIFSourceIndex → Prop) (x : ℝ) :
    kernelIFTotalPinBlockMassOn ν f eps S H A x + kernelIFTotalPinBlockMassOn ν f eps Sᶜ H A x =
      kernelIFTotalPinBlockMass ν f eps H A x := by
  classical
  unfold kernelIFTotalPinBlockMassOn kernelIFTotalPinBlockMass
  rw [add_add_add_comm, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
  congr 1 <;> apply tsum_congr <;> intro p <;> split_ifs
  · exact kernel_IF_total_facet_pin_partition ν f eps hS _ _ H x
  · exact zero_add 0
  · exact kernel_IF_total_facet_pin_partition ν f eps hS _ _ H x
  · exact zero_add 0

theorem kernel_IF_total_block_mass_univ (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) (x : ℝ) :
    kernelIFTotalPinBlockMassOn ν f eps univ H A x = kernelIFTotalPinBlockMass ν f eps H A x := by
  unfold kernelIFTotalPinBlockMassOn kernelIFTotalPinBlockMass
  simp_rw [kernel_IF_total_facet_pin_univ]

theorem kernel_IF_total_block_massOn_le (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {S : Set ℝ} (hS : MeasurableSet S) (H : ℝ → ℝ≥0∞)
    (A : KernelIFSourceIndex → Prop) (x : ℝ) :
    kernelIFTotalPinBlockMassOn ν f eps S H A x ≤ kernelIFTotalPinBlockMass ν f eps H A x := by
  rw [← kernel_IF_total_block_mass_partition ν f eps hS H A x]
  exact le_add_right le_rfl

theorem kernel_IF_total_facet_pinOn_mono (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (x : ℝ)
    {H₁ H₂ : ℝ → ℝ≥0∞} (hH : ∀ s, H₁ s ≤ H₂ s) :
    kernelIFFacetTotalPinDensityOn ν f eps S q i H₁ x ≤
      kernelIFFacetTotalPinDensityOn ν f eps S q i H₂ x := by
  classical
  unfold kernelIFFacetTotalPinDensityOn
  split_ifs <;> try exact le_rfl
  · unfold kernelIFLeftTotalPinDensityOn
    gcongr with a g
    exact hH _
  · unfold kernelIFLeftTotalDiracPinDensityOn
    split_ifs
    · unfold kernelIFLeftTotalDiracPinDensity
      gcongr with g
      exact hH _
    · exact le_rfl
  · unfold kernelIFRightTotalPinDensityOn
    gcongr with a g
    exact hH _
  · unfold kernelIFRightTotalDiracPinDensityOn
    split_ifs
    · unfold kernelIFRightTotalDiracPinDensity
      gcongr with g
      exact hH _
    · exact le_rfl

theorem kernel_IF_total_block_massOn_mono (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (S : Set ℝ) (x : ℝ) {H₁ H₂ : ℝ → ℝ≥0∞} (hH : ∀ s, H₁ s ≤ H₂ s)
    {A B : KernelIFSourceIndex → Prop} (hAB : ∀ b, A b → B b) :
    kernelIFTotalPinBlockMassOn ν f eps S H₁ A x ≤ kernelIFTotalPinBlockMassOn ν f eps S H₂ B x := by
  classical
  unfold kernelIFTotalPinBlockMassOn
  apply add_le_add <;> apply ENNReal.tsum_le_tsum <;> intro p
  · by_cases h : A (kernelIFLeftOfBlocks p).1
    · simp only [if_pos h, if_pos (hAB _ h)]
      exact kernel_IF_total_facet_pinOn_mono ν f eps S _ _ x hH
    · simp only [if_neg h]
      exact bot_le
  · by_cases h : A (kernelIFRightOfBlocks p).1
    · simp only [if_pos h, if_pos (hAB _ h)]
      exact kernel_IF_total_facet_pinOn_mono ν f eps S _ _ x hH
    · simp only [if_neg h]
      exact bot_le

end
end PGM
