import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Laws on `ℤ`: finite convolutions and lattice concentration

Shared interface for the lattice concentration inequalities (Kolmogorov–Rogozin, Kesten).

* `convFin m μ` is the law of `X₀ + ⋯ + X_{m-1}` for independent `Xᵢ ∼ μ i`.
* `lconc μ c` is the largest `μ`-mass of `c` consecutive integers, i.e. the concentration
  function `Q(X; c - 1/2)` of an integer-valued `X`; `lconc μ 1` is the largest atom.
* `RogozinLattice C` is the lattice Kolmogorov–Rogozin inequality with constant `C`: for
  independent integer variables and window lengths `w, c ≥ 1`,
  `Q(S; w) · (∑ᵢ (1 - Q(Xᵢ; c)))^{1/2} ≤ C (w / c + 1)`.
-/

namespace PGM

noncomputable section

open MeasureTheory

/-- The law of the sum of `m` independent integer variables with laws `μ 0, …, μ (m-1)`. -/
def convFin : (m : ℕ) → (Fin m → Measure ℤ) → Measure ℤ
  | 0, _ => Measure.dirac 0
  | m + 1, μ => convFin m (fun i => μ i.castSucc) ∗ μ (Fin.last m)

/-- The largest mass of `c` consecutive integers. -/
def lconc (μ : Measure ℤ) (c : ℕ) : ℝ := ⨆ x : ℤ, (μ (Set.Ico x (x + c))).toReal

/-- The lattice Kolmogorov–Rogozin inequality with constant `C`. -/
def RogozinLattice (C : ℝ) : Prop :=
  ∀ (m : ℕ) (μ : Fin m → Measure ℤ), (∀ i, IsProbabilityMeasure (μ i)) →
    ∀ c w : ℕ, 1 ≤ c → 1 ≤ w →
      lconc (convFin m μ) w * Real.sqrt (∑ i, (1 - lconc (μ i) c)) ≤ C * ((w : ℝ) / c + 1)

end

end PGM
