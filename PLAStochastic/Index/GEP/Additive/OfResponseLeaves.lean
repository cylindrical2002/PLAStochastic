import PLAStochastic.Index.GEP.Additive.OfRemainingLeaves
import PLAStochastic.Index.GEP.Shadow.AllLayersRegular
import PLAStochastic.Index.GEP.Shadow.TreeSwitch.DefectsOfRegularity

/-!
# G-EP additive height: assembly after closing `ShadowDefects`

`shadowDefects` proves the shadow interface of `TheoremGEPAdditive` for every gap law of
Model G with almost surely positive gaps: the all-layer regularity of the exponential-mark
shadow (`regLaw_shLawPM_all`, `memory-route.md` §3–5) feeds the summable tree-switch defects
(`shadowDefects_of_regLaw`, `memory-route.md` §6–7).  The tree switch uses the polynomial
stopped margin of `PLAStochastic.Index.OneLayer.ThresholdMargin` instead of the full-scale linear margin of the source; see
`research/2026-09-29-lean-gep-shadow-defects/README.md`.

With `orbitClosure` and `kappaBound` already discharged (`GEPAdditiveReduction`), the additive
height theorem now depends only on the six remaining analytic response leaves of WP4.
-/

namespace PGM

open MeasureTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}

/-- **`ShadowDefects` holds unconditionally** for Model G gaps (positive, finite third moment). -/
theorem shadowDefects (hg : GapLaw P g μ₀ σ₀ κ₀) (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ShadowDefects P g :=
  shadowDefects_of_regLaw hg hpos (regLaw_shLawPM_all hg hpos)

/-- The summable logarithmic error, conditional only on the six remaining response leaves. -/
theorem sum_abs_log_segMean_sub_le_of_response_leaves
    (hSc : ScoreCalculus) (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm)
    (hS : PointwiseSmall) (hQ : QuadResponse) (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ L,
      ∑ j ∈ Ico 1 L, |Real.log (segMean P eps (epLayerSeq eps g j)) - gepLogC eps| ≤ K :=
  sum_abs_log_segMean_sub_le_of_remaining_leaves hSc hC hP hD hS hQ hg (shadowDefects hg hpos)

/-- Additive height for every `n ≥ 2`, conditional only on the six remaining response leaves. -/
theorem H_G_EP_additive_of_response_leaves
    (hSc : ScoreCalculus) (hC : KernelC) (hP : KernelPhi) (hD : DirectTerm)
    (hS : PointwiseSmall) (hQ : QuadResponse) (hg : GapLaw P g μ₀ σ₀ κ₀)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (x0 : Ω → ℝ) :
    ∃ eps0 K : ℝ, ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P -
          Real.log n / Real.log (gepC eps)| ≤ K :=
  H_G_EP_additive_of_remaining_leaves hSc hC hP hD hS hQ hg (shadowDefects hg hpos) x0

end PGM
