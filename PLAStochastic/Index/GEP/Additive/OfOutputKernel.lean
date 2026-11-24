import PLAStochastic.Index.GEP.Additive.OfKernelLeaves
import PLAStochastic.Index.GEP.Kernel.Leaves.ScalarFromOutput

/-!
# G-EP additive height with one remaining output-kernel assumption

The admissible constant output test supplies the scalar kernel leaf. This
assembly retains the original `KernelPhi`, exact denominator, and all-input
quantifiers; it does not assert that the remaining analytic leaf is proved.
-/

namespace PGM

open MeasureTheory Finset

theorem jointResponse_of_output_kernel (hPhi : KernelPhi) : JointResponse :=
  jointResponse_of_kernel_leaves (kernelC_of_kernelPhi hPhi) hPhi

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

theorem sum_abs_log_segMean_sub_le_of_output_kernel (hPhi : KernelPhi)
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K :=
  sum_abs_log_segMean_sub_le_of_kernel_leaves (kernelC_of_kernelPhi hPhi) hPhi hg hpos

/-- The actual all-input additive height statement now needs only the original
output kernel leaf, besides the Model G law and positive gaps. -/
theorem H_G_EP_additive_of_output_kernel (hPhi : KernelPhi)
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K :=
  H_G_EP_additive_of_kernel_leaves (kernelC_of_kernelPhi hPhi) hPhi hg hpos x0

end PGM
