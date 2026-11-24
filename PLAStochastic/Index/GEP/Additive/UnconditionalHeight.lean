import PLAStochastic.Index.GEP.Additive.OfOutputKernel
import PLAStochastic.Index.GEP.Kernel.Leaves.Main

/-!
# Unconditional additive Model G endpoint height

The original output kernel is proved by the physical near/far decomposition.
The original scalar kernel follows from its constant test. The existing
actual-algorithm assembly therefore no longer needs any analytic leaf as an
assumption. The denominator remains the exact universal `gepC eps`.
-/

namespace PGM

open MeasureTheory Finset

theorem jointResponse : JointResponse := jointResponse_of_output_kernel kernelPhi

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

theorem sum_abs_log_segMean_sub_le
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K :=
  sum_abs_log_segMean_sub_le_of_output_kernel kernelPhi hg hpos

/-- For the actual ALG-PGM hierarchy, all `n ≥ 2` and all sufficiently large
`eps`, the expected height differs from `log n / log (gepC eps)` by a constant.
Only the Model G law and almost surely positive gaps are assumed. -/
theorem H_G_EP_additive
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K :=
  H_G_EP_additive_of_output_kernel kernelPhi hg hpos x0

end PGM
