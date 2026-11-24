import PLAStochastic.Index.GEP.Additive.OfResponseLeaves
import PLAStochastic.Index.GEP.Response.Score.ScoreCalculus

/-!
# G-EP additive height: assembly after closing the score-calculus leaf

`scoreCalculus` (`GEPResponseScore`) proves leaf 4A-S of `GEPResponseDefs`: differentiability of
the three functionals of (J) along mixture paths of the regular class (`joint-response.md` §5,
`influence-lipschitz.md` §8).  With `orbitClosure`, `kappaBound` and `shadowDefects` already
discharged, the additive height theorem depends only on the five remaining analytic leaves
`KernelC`, `KernelPhi`, `DirectTerm`, `PointwiseSmall`, `QuadResponse`.
-/

namespace PGM

open MeasureTheory Finset

/-- Joint response from the five remaining analytic leaves. -/
theorem jointResponse_of_five_leaves (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm)
    (hS : PointwiseSmall) (hQ : QuadResponse) : JointResponse :=
  jointResponse_of_remaining_leaves scoreCalculus hC hP hD hS hQ

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

/-- The summable logarithmic error, conditional only on the five remaining analytic leaves. -/
theorem sum_abs_log_segMean_sub_le_of_five_leaves
    (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm) (hS : PointwiseSmall) (hQ : QuadResponse)
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K :=
  sum_abs_log_segMean_sub_le_of_response_leaves scoreCalculus hC hP hD hS hQ hg hpos

/-- Additive height for every `n ≥ 2`, conditional only on the five remaining analytic leaves. -/
theorem H_G_EP_additive_of_five_leaves
    (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm) (hS : PointwiseSmall) (hQ : QuadResponse)
    (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K :=
  H_G_EP_additive_of_response_leaves scoreCalculus hC hP hD hS hQ hg hpos x0

end PGM
