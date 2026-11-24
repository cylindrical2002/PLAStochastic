import PLAStochastic.Index.GEP.Additive.OfFiveLeaves
import PLAStochastic.Index.GEP.SurvivalBound.Main
import PLAStochastic.Index.GEP.PointwiseSmall.Main
import PLAStochastic.Index.GEP.QuadResponse.Main
import PLAStochastic.Index.GEP.Universality.Main

/-!
# G-EP additive height: assembly after closing the analytic leaves

Three of the five analytic leaves of `GEPAdditiveScore` are now theorems of the library:

* `directTerm : DirectTerm` (`GEPSurv`, via `survivalBound`);
* `pointwiseSmall_of_univ universality survivalBound : PointwiseSmall`;
* `quadResponse_of_univ universality survivalBound : QuadResponse`,

where `universality : GEPUniversality` is the one-layer strong-approximation rate (WP5).
The additive height theorem therefore depends only on the two kernel leaves `KernelC` and
`KernelPhi` (`influence-lipschitz.md` (AL), (TAIL)).
-/

namespace PGM

open MeasureTheory Finset

/-- Leaf 4A-P, unconditional. -/
theorem pointwiseSmall : PointwiseSmall :=
  pointwiseSmall_of_univ universality survivalBound

/-- Leaf 4A-Q, unconditional. -/
theorem quadResponse : QuadResponse :=
  quadResponse_of_univ universality survivalBound

/-- Joint response from the two remaining kernel leaves. -/
theorem jointResponse_of_kernel_leaves (hC : KernelC) (hP : KernelPhi) : JointResponse :=
  jointResponse_of_five_leaves hC hP directTerm pointwiseSmall quadResponse

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

/-- The summable logarithmic error, conditional only on the two kernel leaves. -/
theorem sum_abs_log_segMean_sub_le_of_kernel_leaves (hC : KernelC) (hP : KernelPhi)
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K :=
  sum_abs_log_segMean_sub_le_of_five_leaves hC hP directTerm pointwiseSmall quadResponse hg hpos

/-- Additive height for every `n ≥ 2`, conditional only on the two kernel leaves. -/
theorem H_G_EP_additive_of_kernel_leaves (hC : KernelC) (hP : KernelPhi)
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K :=
  H_G_EP_additive_of_five_leaves hC hP directTerm pointwiseSmall quadResponse hg hpos x0

end PGM
