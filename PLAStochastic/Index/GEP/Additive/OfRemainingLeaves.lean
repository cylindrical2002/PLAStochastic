import PLAStochastic.Index.GEP.Response.OfLeaves
import PLAStochastic.Index.GEP.Response.KappaBound
import PLAStochastic.Index.GEP.OrbitClosure.Main

/-!
# G-EP additive height: assembly after closing WP2 and leaf 4A-κ

These theorems discharge `OrbitClosure` and `KappaBound` using their proved
implementations.  The six other response leaves and `ShadowDefects` remain
explicit hypotheses; the unconditional additive height theorem is still open.
-/

namespace PGM

open MeasureTheory Finset

/-- Joint response from the six remaining analytic leaves. -/
theorem jointResponse_of_remaining_leaves (hSc : ScoreCalculus) (hC : KernelC)
    (hP : KernelPhi) (hD : DirectTerm) (hS : PointwiseSmall) (hQ : QuadResponse) :
    JointResponse :=
  jointResponse_of_leaves hSc hC hP hD hS hQ kappaBound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

/-- The summable logarithmic error, with orbit closure and the normalization bound discharged. -/
theorem sum_abs_log_segMean_sub_le_of_remaining_leaves
    (hSc : ScoreCalculus) (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm)
    (hS : PointwiseSmall) (hQ : QuadResponse) (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hSh : ShadowDefects P g) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K :=
  sum_abs_log_segMean_sub_le_of_inputs
    (jointResponse_of_remaining_leaves hSc hC hP hD hS hQ) orbitClosure hg hSh

/-- Additive height for every `n ≥ 2`, conditional on exactly the remaining interfaces. -/
theorem H_G_EP_additive_of_remaining_leaves
    (hSc : ScoreCalculus) (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm)
    (hS : PointwiseSmall) (hQ : QuadResponse) (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hSh : ShadowDefects P g) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K :=
  H_G_EP_additive_of_inputs
    (jointResponse_of_remaining_leaves hSc hC hP hD hS hQ) orbitClosure hg hSh x0

end PGM
