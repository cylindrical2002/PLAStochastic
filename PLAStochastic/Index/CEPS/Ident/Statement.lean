import PLAStochastic.Index.CEPS.Canonical.Main

/-!
# CEPS WP4: the frozen statement of the Wiener–Hopf identification (C-5)

Blueprint §3.2 (3.4)–(3.5). For a step law `ρW` of the class and the canonical domain
`dom : CepsCanonDomain D θ v` (`γ = 1`, abscissa `c₀`), with `Y = W + μ` (`driftStep ρW μ`, real
`μ`), discount `e^{-q}` and the ladder transforms of the W library

* `A₊(ζ) = ascTransform (driftStep ρW μ) (cexp (-q)) ζ` (strict ascending ladder),
* `A₋(ζ) = descTransform (driftStep ρW μ) (cexp (-q)) ζ` (weak descending ladder; its entry
  position is `-H₋ ≤ 0`, so this is `E[e^{-q σ₋} e^{-ζ H₋}; σ₋ < ∞]`),

the identification on `𝔇₊ = {|μ| ≤ μ₀, Re q ≥ 0, ‖q‖ ≤ q₀}` reads

  `1 - A₊(ζ) = (β₊ - ζ) e^{L(ζ)}` for `Re ζ < c₀`,
  `1 - A₋(ζ) = (ζ - β₋) e^{L₋(ζ)}` for `|Re ζ| < c₀`,

with `L = dom.canonL ρW μ q`, `Q = cepsQ` (`d/((β₊ - ζ)(ζ - β₋))`, both roots removed by iterated
`dslope`) and `L₋ = log Q - L` (`CepsCanonDomain.canonLMinus`, principal logarithm).
`CepsWHIdent dom ρW` is this statement; it is proved in `Ident.Factor`.
-/

noncomputable section

open MeasureTheory Complex
open PGM.WienerHopf

namespace PGM

/-- `Q(ζ) = d(ζ)/((β₊ - ζ)(ζ - β₋))` (blueprint (3.2)), the two roots removed by iterated
`dslope`: `-d = (ζ - β₊)(ζ - β₋) Q` wherever `d` is analytic at the roots. -/
def cepsQ (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ → ℂ :=
  dslope (dslope (fun z => -cepsD ρW μ q z) (cepsRootPlus D θ ρW μ q)) (cepsRootMinus D θ ρW μ q)

namespace CepsCanonDomain

variable {D θ v : ℝ}

/-- The other-side factor `L₋ = log Q - L` (blueprint (3.4)), principal logarithm. -/
def canonLMinus (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ :=
  Complex.log (cepsQ D θ ρW μ q ζ) - dom.canonL ρW μ q ζ

end CepsCanonDomain

/-- **C-5 (frozen statement).** The Wiener–Hopf identification of the two ladder factors by the
canonical factor, on `𝔇₊`. -/
def CepsWHIdent {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) : Prop :=
  ∀ μ : ℝ, |μ| ≤ dom.μ₀ → ∀ q : ℂ, 0 ≤ q.re → ‖q‖ ≤ dom.q₀ →
    (∀ ζ : ℂ, ζ.re < dom.c₀ →
      1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ =
        (cepsRootPlus D θ ρW μ q - ζ) * cexp (dom.canonL ρW μ q ζ)) ∧
    (∀ ζ : ℂ, |ζ.re| < dom.c₀ →
      1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ =
        (ζ - cepsRootMinus D θ ρW μ q) * cexp (dom.canonLMinus ρW μ q ζ))

end PGM
