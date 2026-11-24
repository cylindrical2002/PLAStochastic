import PLAStochastic.Index.CEPS.Canonical.LineZones
import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt

/-!
# Strip normal forms over an abstract factor

The factor argument always has type `ℂ → ℂ → ℂ → ℂ`, in the order `(μ,q,ζ)`.
No canonical-factor theorem is imported. `CepsNormalData` collects the root and
quadratic-quotient data at a fixed parameter point; compatibility assumptions
are stated on the theorems that use them. `cepsNormalData` uses WP3's already
constructed Morse roots and its root-removed quotient `cepsQuotA`.

The raw formulas are used only away from their displayed denominators. Their
holomorphic extensions at merged roots are separate objects, not the value of
Lean's totalized division at a zero denominator.
-/

noncomputable section
open Complex MeasureTheory

namespace PGM

structure CepsNormalData where
  βp : ℂ
  βm : ℂ
  d : ℂ → ℂ
  Q : ℂ → ℂ
  ψp : ℂ
  ψm : ℂ

/-- Morse-chart data, with the removable values of `Q` retained at both roots. -/
def cepsNormalData (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : CepsNormalData where
  βp := cepsRootPlus D θ ρW μ q
  βm := cepsRootMinus D θ ρW μ q
  d := cepsD ρW μ q
  Q := cepsQuotA D θ ρW μ q
  ψp := deriv (cepsCgfShift ρW μ) (cepsRootPlus D θ ρW μ q)
  ψm := deriv (cepsCgfShift ρW μ) (cepsRootMinus D θ ρW μ q)

namespace CepsNormalData

def eta (a : CepsNormalData) : ℂ := a.βp - a.βm

def factorMinus (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q ζ : ℂ) : ℂ :=
  log (a.Q ζ) - L μ q ζ

def meanPlus (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ) : ℂ :=
  exp (L μ q a.βp)

def overshootPlus (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q s : ℂ) : ℂ :=
  exp (L μ q (a.βp - s) - L μ q a.βp)

def overshootMinus (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q s : ℂ) : ℂ :=
  exp (a.factorMinus L μ q (a.βm + s) - a.factorMinus L μ q a.βm)

/-- (3.7), in the quotient form regular at merged roots. -/
def pi (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ) : ℂ :=
  a.Q a.βp / a.Q a.βm * exp (2 * L μ q a.βm - 2 * L μ q a.βp)

def markedN (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t : ℂ) : ℂ :=
  a.Q t / a.Q a.βm * exp (2 * L μ q a.βm - 2 * L μ q t)

def reflectedN (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ) : ℂ :=
  a.Q a.βp / a.Q 0 * exp (2 * L μ q 0 - 2 * L μ q a.βp)

def decay (a : CepsNormalData) (l : ℂ) : ℂ := exp (-a.eta * l)

def delta (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ) : ℂ :=
  1 - a.decay l * a.pi L μ q

def entranceNumerator (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ q t l : ℂ) : ℂ :=
  (a.βp - t) - (a.βm - t) * a.decay l * a.pi L μ q -
    a.eta * exp ((a.βm - t) * l) * a.markedN L μ q t

/-- The marked normal entrance (C16). -/
def entrance (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t l : ℂ) : ℂ :=
  exp (L μ q t) / a.d t * a.entranceNumerator L μ q t l / a.delta L μ q l

def bottomNumerator (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ) : ℂ :=
  -a.βm + a.βp * a.decay l * a.pi L μ q -
    a.eta * exp (-a.βp * l) * a.reflectedN L μ q

/-- Reflection of the unmarked (C16) entrance. -/
def bottomEntrance (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ) : ℂ :=
  exp (a.factorMinus L μ q 0) / a.d 0 *
    a.bottomNumerator L μ q l / a.delta L μ q l

/-- The half-line entrance (P5). -/
def halfEntrance (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t : ℂ) : ℂ :=
  exp (L μ q t) * (a.βp - t) / a.d t

/-- The half-line bridge (C12). -/
def halfBridge (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ) : ℂ :=
  a.ψp * exp (-a.βp * l - 2 * L μ q a.βp)

/-- The normal bridge (C12). -/
def bridge (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q l : ℂ) : ℂ :=
  a.halfBridge L μ q l / a.delta L μ q l

/-- The half-line primitive numerator (P8). -/
def primitiveNumerator (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ q t l : ℂ) : ℂ :=
  exp (t * l) * (a.halfEntrance L μ q t) ^ 2 * a.halfBridge L μ q l

/-- Marked drawup amplitude (C19). -/
def amplitude (a : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t : ℂ) : ℂ :=
  (a.βp - t) * a.ψp / a.d t * exp (2 * L μ q t - 2 * L μ q a.βp)

end CepsNormalData

/-- The complete normal pair (C15), with `𝒟 = -∂q` taken before substitution. -/
def cepsNormalPair (A : ℂ → ℂ → CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ t w : ℂ) : ℂ :=
  let q := t * (1 + μ)
  let l := w * (1 + μ)
  exp (t * l) * ((A μ q).entrance L μ q t l) ^ 2 *
    (-deriv (fun q' => (A μ q').bridge L μ q' l) q - w * (A μ q).bridge L μ q l)

/-- The complete half-line pair (C15). -/
def cepsNormalHalfPair (A : ℂ → ℂ → CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ)
    (μ t w : ℂ) : ℂ :=
  let q := t * (1 + μ)
  let l := w * (1 + μ)
  exp (t * l) * ((A μ q).halfEntrance L μ q t) ^ 2 *
    (-deriv (fun q' => (A μ q').halfBridge L μ q' l) q -
      w * (A μ q).halfBridge L μ q l)

end PGM
