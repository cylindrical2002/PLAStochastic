import PLAStochastic.Index.CEPS.Canonical.LineSeparation

/-!
# CEPS WP3: definition of the canonical factor (blueprint (3.3))

For a step law `ρW`, real `γ` and a line abscissa `c`, the canonical factor is

  `L(ζ; μ, q) = (2π)⁻¹ ∫_ℝ log F(c + i y; μ, q) / (c + i y - ζ) dy - log (γ - ζ)`,

i.e. `(2πi)⁻¹ ∫_{c - i∞}^{c + i∞} log F(s)/(s - ζ) ds - log(γ - ζ)` (`ds = i dy`), with
`F = d (ζ² - γ²)/D₀` (`cepsF`), principal logarithms, `Re ζ < c`. Here `ℓ(μ, q) = L(0; μ, q)`.

The domain choice used downstream is `γ = 1`, `c = c₀` of a `CepsCanonDomain`
(`CepsCanonDomain.canonL`, `CepsCanonDomain.canonEll`); by C-3(a) the value does not depend on
`c ∈ [c₀, 2c₀]`.

Frozen statements proved in `Canonical.Factor` (C-3(a), (b)); throughout `dom : CepsCanonDomain D θ v`,
`IsStepLaw ρW fW D θ v`, real `μ` with `|μ| ≤ μ₀`, `γ ∈ [1/2, 1]`, `c ∈ [c₀, 2c₀]`:

* `integrable_cepsCanonL_integrand`: for `‖q‖ ≤ q₀` and `Re ζ < c` the integrand is integrable;
* `differentiableOn_cepsCanonL`: `(ζ, q) ↦ L` is jointly holomorphic on
  `{Re ζ < c} × B(0, q₀)`;
* `continuous_cepsCanonL_mu`: `μ ↦ L` is continuous on `[-μ₀, μ₀]`;
* `cepsCanonL_eq_of_abscissa`: `L` with abscissa `c` equals `L` with abscissa `c'` for `Re ζ < min c c'`;
* `norm_cepsCanonL_le`: `‖L(ζ)‖ ≤ C` for `‖ζ‖ ≤ c₀/2`;
* `norm_cepsCanonL_add_log_le`: `‖L(ζ) + log(γ - ζ)‖ ≤ C` for `Re ζ ≤ c₀/2`.
-/

noncomputable section

open MeasureTheory Complex

namespace PGM

/-- **The canonical factor** (blueprint (3.3)). -/
def cepsCanonL (D θ : ℝ) (ρW : Measure ℝ) (γ c : ℝ) (μ q ζ : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * (∫ y : ℝ, Complex.log (cepsF D θ ρW γ μ q (c + y * I)) / (c + y * I - ζ))
    - Complex.log (γ - ζ)

/-- `ℓ(μ, q) = L(0; μ, q)`. -/
def cepsCanonEll (D θ : ℝ) (ρW : Measure ℝ) (γ c : ℝ) (μ q : ℂ) : ℂ :=
  cepsCanonL D θ ρW γ c μ q 0

namespace CepsCanonDomain

variable {D θ v : ℝ}

/-- The canonical factor with the domain choice `γ = 1`, `c = c₀`. -/
def canonL (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ :=
  cepsCanonL D θ ρW 1 dom.c₀ μ q ζ

/-- `ℓ = L(0)` with the domain choice. -/
def canonEll (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (μ q : ℂ) : ℂ :=
  dom.canonL ρW μ q 0

end CepsCanonDomain

end PGM
