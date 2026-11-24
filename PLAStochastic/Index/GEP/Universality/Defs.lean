import PLAStochastic.Index.GEP.LayerLaw.WeightedDistance

/-!
# WP5 target: the one-layer universality rate (U)

The only strong-approximation input of the joint response (J).  It enters WP4 solely as the
real-axis smallness `δ_ε` in `positive-direction-response.md` (PD) §3, §6.2 (17), §7 and §9;
see `research/2026-09-28-lean-gep-additive/wp4-design.md` §4 and
`dependency-census.md` §1.3–1.4.

**Statement.** Let `rawLaw ε ν = Law_ν(v(ν) S_T / ε²)` (`S_T = stopSum ε`, `T` the first ALG-OPT
segment length of iid `ν` gaps, `v(ν) = lawVar ν`).  There is a universal rate exponent
`β > 1/2` such that for every variance bracket `[vlo, vhi]` and third-moment bound `κ₃` there
is a weight `γ > 0`, and then for every exponential-moment class `(B, θ)` and density-part
parameters `(D, c₀)` with `θ, c₀ > 0` there are `K, ε₀` with
`d_γ(rawLaw ε ν, rawLaw ε ν') ≤ K ε^{-β}` for all `ε ≥ ε₀` and all `ν, ν'` satisfying both
`UnivClass vlo vhi κ₃ B θ` and `SmoothPart D c₀`.  The distance is the weighted `W₁` of
`PLAStochastic/Index/GEP/LayerLaw/Defs.lean`, written as a lower integral so that the bound includes finiteness.

**Quantifiers.** `γ` must not depend on `(B, θ)`: PD §9 fixes the output weight first and
then lets the input exponential weight `α` (hence `θ = α/2`, `B = K_α`) shrink.  `β` must be
fixed before `α` (JR §4 needs `α b < β - 1/2`).  `SmoothPart` requires a bounded density
component of positive mass; the full law may have a singular remainder.  This permits the
positive paths of PD §1, §6.1, which leave the class of laws with a full bounded density.

**What the consumer extracts** (with `Wald E S_T = C`): `|v C/ε² - v' C'/ε²| ≤ K δ`,
`|v² E S_T²/ε⁴ - v'² E S_T'²/ε⁴| ≤ K δ` (hence `M₂/C²` is universal up to `K δ`), the weighted
`W₁` smallness of `Law(S_T/ε²)` along fixed-variance paths (PD (17)), and, with the reference
`P_ε = rawLaw ε ν*`, the Lipschitz dependence of `Law(P_ε/v)` on `v` (PD §7, B3).
The sources (ER `prop:onelayer`, `cor:regimes`(A), SO §2, PD (17)) give the rate
`K log ε / ε`, i.e. any `β < 1`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- `Law_ν(v(ν) S_T / ε²)`: the stopped sum in Brownian time units. -/
def rawLaw (eps : ℝ) (ν : ProbabilityMeasure ℝ) : ProbabilityMeasure ℝ :=
  ⟨(iidLaw ν).map (fun g => lawVar ν * stopSum eps g / eps ^ 2),
    Measure.isProbabilityMeasure_map
      ((measurable_const.mul (measurable_stopSum eps)).div_const _).aemeasurable⟩

/-- The class of (U): positive gaps, mean one, variance in `[vlo, vhi]`,
`E|X - 1|³ ≤ κ₃` and `E e^{θX} ≤ B`.  No density is required. -/
structure UnivClass (vlo vhi κ₃ B θ : ℝ) (ν : ProbabilityMeasure ℝ) : Prop where
  pos : (ν : Measure ℝ) (Iic 0) = 0
  mean : lawMean ν = 1
  var_ge : vlo ≤ lawVar ν
  var_le : lawVar ν ≤ vhi
  third : ∫⁻ x, ENNReal.ofReal (|x - 1| ^ 3) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal κ₃
  expMom : ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂(ν : Measure ℝ) ≤ ENNReal.ofReal B

/-- The weighted `W₁` distance as a lower integral: `∫_0^∞ e^{γx} |F_μ - F_ρ| dx ∈ [0, ∞]`. -/
def dEtaL (γ : ℝ) (μ ρ : ProbabilityMeasure ℝ) : ENNReal :=
  ∫⁻ x in Ioi (0 : ℝ),
    ENNReal.ofReal (Real.exp (γ * x) * |cdf (μ : Measure ℝ) x - cdf (ρ : Measure ℝ) x|)

/-- A density part of mass at least `c₀`, bounded by `D`: `f dx ≤ ν` with `0 ≤ f ≤ D`. -/
structure SmoothPart (D c₀ : ℝ) (ν : ProbabilityMeasure ℝ) : Prop where
  part : ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
    ENNReal.ofReal c₀ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∧
    volume.withDensity (fun x => ENNReal.ofReal (f x)) ≤ (ν : Measure ℝ)

/-- **(U)**, the one-layer universality rate consumed by WP4.

Amended 2026-09-29 (KMT blueprint `research/2026-09-28-lean-gep-additive/kmt-blueprint/`,
§1): the laws must also have a bounded density part (`SmoothPart`).  Without it the class
contains lattice laws, for which the uniform Cramér gap and the local limit theorem of the
dyadic coupling fail.  WP4 applies (U) only to regular laws and to the paths
`(1 - z) ν + z σ` with `ν` regular, which have `SmoothPart D (1 - z)`. -/
def GEPUniversality : Prop :=
  ∃ β : ℝ, 1 / 2 < β ∧
    ∀ vlo vhi κ₃ : ℝ, 0 < vlo → vlo ≤ vhi →
      ∃ γ : ℝ, 0 < γ ∧
        ∀ B θ D c₀ : ℝ, 0 < θ → 0 < c₀ →
          ∃ K e0 : ℝ, ∀ eps, e0 ≤ eps → ∀ ν ν' : ProbabilityMeasure ℝ,
            UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c₀ ν →
            UnivClass vlo vhi κ₃ B θ ν' → SmoothPart D c₀ ν' →
              dEtaL γ (rawLaw eps ν) (rawLaw eps ν') ≤ ENNReal.ofReal (K * eps ^ (-β))

end

end PGM
