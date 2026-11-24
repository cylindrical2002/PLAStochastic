import PLAStochastic.Index.CEPS.Ident.Factor
import PLAStochastic.Index.CEPS.Ident.Corollaries

/-! # Actual CEPS Wiener–Hopf identification and its residue corollaries

The factor identity is proved from the step-law class. The two residue
identities below discharge the formerly explicit identification premise.
The remaining corollaries can use `dom.cepsWHIdent hW hθ hD` directly.
-/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- Both actual ladder residues, including the coincident-root case. -/
theorem actual_ladder_residues {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) :
    HasDerivAt (fun ζ => ascTransform (driftStep ρW μ) (cexp (-q)) ζ)
      (cexp (dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)))
      (cepsRootPlus D θ ρW μ q) ∧
    HasDerivAt (fun ζ => descTransform (driftStep ρW μ) (cexp (-q)) ζ)
      (-cexp (dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)))
      (cepsRootMinus D θ ρW μ q) :=
  ⟨dom.hasDerivAt_ascTransform_rootPlus hW hθ hD (dom.cepsWHIdent hW hθ hD) hμ hq0 hq,
   dom.hasDerivAt_descTransform_rootMinus hW hθ hD (dom.cepsWHIdent hW hθ hD) hμ hq0 hq⟩

include hW hθ hD in
/-- The actual ascending overshoot factor, without an identification assumption. -/
theorem actual_overshoot_plus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {s : ℂ} (hs : s ≠ 0)
    (hsc : (cepsRootPlus D θ ρW μ q - s).re < dom.c₀) :
    cepsOvershootPlus D θ ρW μ q s =
      cexp (dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q - s) -
        dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) :=
  dom.cepsOvershootPlus_eq hW hθ hD (dom.cepsWHIdent hW hθ hD) hμ hq0 hq hs hsc

include hW hθ hD in
/-- The actual descending overshoot factor, without an identification assumption. -/
theorem actual_overshoot_minus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {s : ℂ} (hs : s ≠ 0)
    (hsc : |(cepsRootMinus D θ ρW μ q + s).re| < dom.c₀) :
    cepsOvershootMinus D θ ρW μ q s =
      cexp (dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q + s) -
        dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) :=
  dom.cepsOvershootMinus_eq hW hθ hD (dom.cepsWHIdent hW hθ hD) hμ hq0 hq hs hsc

end PGM.CepsCanonDomain
