import PLAStochastic.Index.GEP.RawDisc.Defs

/-!
# WP4 `SurvivalBound`: complex killed convolution chains on an interval

Objects of `research/2026-09-30-lean-gep-direct-term/rawdisc-design.md` §2.  For a step law `ρ`,
a slope `a` and a shift `β`, the *backward killed step* acts on functions,

`kStep J ρ β a u y = 1_J(y) ∫ u(y + β - a x) dρ(x)`,

so that iterating it follows the walk `y ↦ y + β - a x` and kills it outside `J`.  Along the
mixture `ν_z = (1 - z) ν + z σ` the step is the complex combination `kStepZ`; `kRow … n φ y₀` is the
complex path integral of `φ(y_n)` over walks from `y₀` whose points `y₀, …, y_n` stay in `J`
(word expansion: `kRow_eq_sum_words`, to be proved).

The residual walks of the minimal-slope certificate use `(β, a) = (1, a)` (step `1 - a X`) and
`(β, a) = (-1, -a)` (step `a X - 1`) on `J = [0, 2ε]`; the short free paths use `(β, a) = (0, -1)`
(step `+X`, key coordinates) on a long interval.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- One backward killed step for the step law `ρ`: `u ↦ 1_J(y) ∫ u(y + β - a x) dρ(x)`. -/
def kStep (J : Set ℝ) (ρ : Measure ℝ) (β a : ℝ) (u : ℝ → ℂ) (y : ℝ) : ℂ :=
  J.indicator (fun y => ∫ x, u (y + β - a * x) ∂ρ) y

/-- The killed step of the complex mixture `(1 - z) ν + z σ`. -/
def kStepZ (J : Set ℝ) (ν σ : Measure ℝ) (z : ℂ) (β a : ℝ) (u : ℝ → ℂ) (y : ℝ) : ℂ :=
  (1 - z) * kStep J ν β a u y + z * kStep J σ β a u y

/-- The complex killed row of length `n`: `n` steps `y ↦ y + β - a x` along `(1 - z) ν + z σ`,
all points `y₀, …, y_n` in `J`, evaluated on the test `φ(y_n)`. -/
def kRow (J : Set ℝ) (ν σ : Measure ℝ) (z : ℂ) (β a : ℝ) (n : ℕ) (φ : ℝ → ℂ) : ℝ → ℂ :=
  (kStepZ J ν σ z β a)^[n] (J.indicator φ)

/-- The walk of a gap sequence: `y_l = y₀ + l β - a (g 0 + ⋯ + g (l-1))`. -/
def kWalk (y₀ β a : ℝ) (g : ℕ → ℝ) (l : ℕ) : ℝ := y₀ + l * β - a * gapKeys g l

end

end PGM
