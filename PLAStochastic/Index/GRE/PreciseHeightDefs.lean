import PLAStochastic.Index.GRE.LogLogTheta
import PLAStochastic.Index.KRE.LogLogTheta

/-!
# Definitions for the precise rank-equispaced height theorems

Shared vocabulary of the two precise ALG-RE theorems of the 2026-09-24 research drafts:

* `thm:GRE` (`research/2026-09-24-height-precision-ceiling/tex/main.tex`): under Model G, off a
  window of vanishing width, the height is the integer `⌈y⌉` with
  `y = log₂ (log n / log (c ε²) + 1)` (`greY`); the window half-width is
  `w = K (1 / log ε + log log n / log n)` (`greW`).
* `thm:uniform` (`research/2026-09-24-re-curvature-uniform/tex/main.tex`): under Model K, uniformly
  over the density classes `𝔉_δ` of `def:class` (`DensityClassParams.Mem`), the height is
  `log₂ (log N / log ε) + log₂⁺ (log N / log (ε / δ)) + O(1)` (`twoPhase`), on the Rényi keys
  `Q_f (Γ (t+1) / Γ (N+1))` of the canonical exponential sequence (`renyiKeys`).

`UniformLayerFacts` is the deterministic interface of the proof of `thm:uniform`: the per-layer
bounds of its Section 3 (noise bracket, band dichotomy, curvature upper and lower counts) for one
key sequence, with `effDelta n δ = max δ n⁻³` in the upper bounds.
-/

namespace PGM

noncomputable section

/-! ## `thm:GRE` -/

/-- The window-free value `y = log₂ (log n / log (c ε²) + 1)` of `thm:GRE`.  For
`c = κ_opt μ² / σ²` it is `log₂ (s_n + 1)` with `s_n = log n / log (κ_opt G₀)`. -/
def greY (c : ℝ) (n : ℕ) (eps : ℝ) : ℝ :=
  Real.logb 2 (Real.log n / Real.log (c * eps ^ 2) + 1)

/-- The window half-width `w = K (1 / log ε + log log n / log n)` of `thm:GRE`. -/
def greW (K : ℝ) (n : ℕ) (eps : ℝ) : ℝ :=
  K * (1 / Real.log eps + Real.log (Real.log n) / Real.log n)

/-! ## `thm:uniform` -/

/-- The class parameters of `def:class`: `0 < f₋ ≤ 1 ≤ f₊`, `L, V > 0`, `0 < a < b < 1`. -/
structure DensityClassParams where
  fmin : ℝ
  fmax : ℝ
  L : ℝ
  V : ℝ
  a : ℝ
  b : ℝ
  fmin_pos : 0 < fmin
  fmin_le_one : fmin ≤ 1
  one_le_fmax : 1 ≤ fmax
  L_pos : 0 < L
  V_pos : 0 < V
  a_pos : 0 < a
  a_lt_b : a < b
  b_lt_one : b < 1

/-- `f ∈ 𝔉_δ` (`def:class`): `0 ≤ δ ≤ 1` and `f` is a density on `[0, 1]` with
`f₋ ≤ f ≤ f₊`, `Lip f ≤ δ L` and `|f b - f a| ≥ δ V`.  For `δ = 0` the Lipschitz bound and
`∫₀¹ f = 1` force `f = 1` on `[0, 1]`, so `𝔉₀ = {1}`. -/
def DensityClassParams.Mem (c : DensityClassParams) (δ : ℝ) (f : ℝ → ℝ) : Prop :=
  0 ≤ δ ∧ δ ≤ 1 ∧ DensityK f 0 1 c.fmin c.fmax (δ * c.L) ∧ δ * c.V ≤ |f c.b - f c.a|

/-- The two-phase value `log₂ (log N / log ε) + log₂⁺ (log N / log (ε / δ))` of
`thm:uniform`, with `log₂⁺ x = max 0 (log₂ x)` and the second term `0` for `δ = 0`. -/
def twoPhase (N : ℕ) (eps δ : ℝ) : ℝ :=
  Real.logb 2 (Real.log N / Real.log eps) +
    if δ = 0 then 0 else max 0 (Real.logb 2 (Real.log N / Real.log (eps / δ)))

/-- The Rényi keys `Q_f (Γ (t+1) / Γ (N+1))` on the canonical exponential sequence, where
`Γ (t+1) = E 0 + ⋯ + E t` (`expPartial t`).  They have the law of the sorted Model K sample
(`integral_reHeight_kKeys`). -/
def renyiKeys (f : ℝ → ℝ) (N : ℕ) (ω : ℕ → ℝ) : ℕ → ℝ :=
  fun t => quantK f 0 1 (expPartial t ω / expPartial N ω)

/-- The effective curvature size `max δ n⁻³` of the upper bounds.  Replacing `δ` by it changes
neither `twoPhase` nor any upper bound that is monotone in `Lip f`. -/
def effDelta (n : ℕ) (δ : ℝ) : ℝ := max δ (1 / (n : ℝ) ^ 3)

/-- The per-layer bounds of Section 3 of `thm:uniform` for the ALG-RE run on keys `p`
(`n` keys, tolerance `eps`, class size `δ`), with the layer spacing `Δ = reDelta`, the layer
size `N_ℓ = reSize`, the segment count `M_{ℓ+1} = reSegs`, the step `d_ℓ = reStep` and
`s_ℓ = n / Δ_ℓ`.  With `D = effDelta n δ` and `Y = log n`, a layer with `N_ℓ ≥ 2` is

* noise-dominated if `D ε³ Δ³ ≤ n / Y⁴` and `ε² Δ² ≤ n / Y²`,
* curvature-dominated if `D ε³ Δ³ ≥ n Y⁴`,
* a band layer otherwise.

The fields are `lem:noise`, `lem:band`, `lem:curv`(b) and `lem:curv`(a). -/
structure UniformLayerFacts (p : ℕ → ℝ) (n : ℕ) (eps δ : ℝ)
    (cN CN Cu C0 c1 c2 c3 KL : ℝ) : Prop where
  noise : ∀ ℓ, 2 ≤ reSize eps p n ℓ →
    effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3 ≤ n / Real.log n ^ 4 →
    eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ n / Real.log n ^ 2 →
      cN * eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ reDelta eps p n (ℓ + 1) ∧
        (reDelta eps p n (ℓ + 1) : ℝ) ≤ CN * eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2 ∧
        2 ≤ reSize eps p n (ℓ + 1)
  band : ∀ ℓ, 2 ≤ reSize eps p n ℓ →
    ((n : ℝ) / Real.log n ^ 4 < effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3 ∨
      (n : ℝ) / Real.log n ^ 2 < eps ^ 2 * (reDelta eps p n ℓ : ℝ) ^ 2) →
    effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3 < n * Real.log n ^ 4 →
      reSegs eps p n ℓ = 1 ∨ (n : ℝ) ^ (1 / 4 : ℝ) ≤ reStep eps p n ℓ
  curvUp : ∀ ℓ, 2 ≤ reSize eps p n ℓ →
    (n : ℝ) * Real.log n ^ 4 ≤ effDelta n δ * eps ^ 3 * (reDelta eps p n ℓ : ℝ) ^ 3 →
      (reSegs eps p n ℓ : ℝ) ≤
        Cu * Real.sqrt (effDelta n δ * ((n : ℝ) / reDelta eps p n ℓ) / eps) + C0
  curvLow : 0 < δ → ∀ ℓ, 2 ≤ reSize eps p n ℓ →
    Real.log n ^ 2 ≤ (reDelta eps p n ℓ : ℝ) → KL ≤ (n : ℝ) / reDelta eps p n ℓ →
      min (min (c1 * Real.sqrt (δ * ((n : ℝ) / reDelta eps p n ℓ) / eps))
          (c2 * δ ^ (2 / 3 : ℝ) * ((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ)))
        (c3 * ((n : ℝ) / reDelta eps p n ℓ)) ≤ reSegs eps p n ℓ

end

end PGM
