import PLAStochastic.Index.CEPS.Canonical.Roots
import PLAStochastic.Index.CEPS.Canonical.LineBounds

/-!
# CEPS WP3: domain constants of the canonical factor

Blueprint §3.0. A `CepsCanonDomain D θ v` collects the class constants used by C-1 and C-3:

* `ρA` (radius of the root zone, where the removed quadratic is controlled by the Morse chart),
  `ρB` (outer radius of the quadratic zone), the Fourier gap `gF` beyond `|Im ζ| ≥ ρB/2`, the
  uniform lower bound `g` for `Re d` off the root zone;
* the line abscissa scale `c₀` (lines `Re ζ = c` with `c₀ ≤ |c| ≤ 2 c₀`), the drift and discount
  radii `μ₀`, `q₀`, the admissible imaginary drift `η` (`|Im μ| |Im ζ| ≤ η`), and the bound
  `rmax` for `r₊ = √(q - m(μ))`.

The fields are the inequalities used in the proofs; `cepsCanonDomain_exists` (in
`Canonical.LineSeparation`) shows that such constants exist for every class `(D, θ, v)` with
`D, θ, v > 0`.
-/

noncomputable section

open Set

namespace PGM

/-- Domain constants of the canonical factor for the step class `(D, θ, v)`. -/
structure CepsCanonDomain (D θ v : ℝ) where
  ρA : ℝ
  ρB : ℝ
  gF : ℝ
  g : ℝ
  c₀ : ℝ
  μ₀ : ℝ
  q₀ : ℝ
  η : ℝ
  rmax : ℝ
  ρA_pos : 0 < ρA
  ρA_R : 4 * ρA ≤ cepsChartRadius D θ
  ρA_C3 : 1920 * cepsCgfC3 D θ * ρA ≤ cepsVarLo D
  ρA_one : ρA ≤ 1
  ρA_v : 144 * v ^ 2 * ρA ≤ cepsVarLo D
  ρA_ρB : ρA ≤ ρB
  ρB_r0 : 4 * ρB ≤ cepsCgfRadius D θ
  ρB_C3 : 32 * cepsCgfC3 D θ * ρB ≤ cepsVarLo D
  gF_pos : 0 < gF
  gF_le : gF ≤ 1 / 2
  gF_gap : gF ≤ cepsGap D v (ρB / 2)
  g_pos : 0 < g
  g_gF : g ≤ gF / 2
  g_B : g ≤ 1 - Real.exp (-(cepsVarLo D * ρA ^ 2 / 16))
  c₀_pos : 0 < c₀
  c₀_g : 1000 * c₀ ≤ ρA * g
  c₀_W : 8 * c₀ * cepsShiftConst D θ ≤ gF
  η_pos : 0 < η
  η_le : 32 * η ≤ gF
  rmax_pos : 0 < rmax
  rmax_r1 : 2 * rmax ≤ cepsChartRho D θ
  rmax_c₀ : 8 * cepsChartK D * rmax ≤ c₀
  rmax_A1 : 192 * rmax ≤ ρA * cepsVarLo D
  rmax_A1' : rmax ≤ ρA
  rmax_A2 : 576 * v * cepsChartK D * rmax ≤ ρA * cepsVarLo D
  rmax_A3 : 64 * v * rmax ≤ cepsVarLo D
  rmax_one : rmax ≤ 1
  rmax_B : 16 * rmax ≤ cepsVarLo D * ρA
  rmax_C : 16 * rmax ≤ gF
  μ₀_pos : 0 < μ₀
  μ₀_r : 4 * (v + 1) * μ₀ ≤ cepsVarLo D * rmax
  μ₀_c₀ : 16 * μ₀ ≤ cepsVarLo D * c₀
  μ₀_B : 64 * ρB * μ₀ ≤ cepsVarLo D * ρA ^ 2
  μ₀_C : 64 * μ₀ ≤ gF
  μ₀_chart : 2 * μ₀ ≤ cepsChartMu D θ
  q₀_def : q₀ = rmax ^ 2 / 2

namespace CepsCanonDomain

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

theorem q₀_pos : 0 < dom.q₀ := by rw [dom.q₀_def]; have := dom.rmax_pos; positivity

theorem ρB_pos : 0 < dom.ρB := lt_of_lt_of_le dom.ρA_pos dom.ρA_ρB

theorem g_le_one : dom.g ≤ 1 := by
  have := dom.g_gF; have := dom.gF_le; linarith

theorem c₀_le : dom.c₀ ≤ dom.ρA / 1000 := by
  have h := dom.c₀_g
  have hg := dom.g_le_one
  have := dom.ρA_pos
  nlinarith

end CepsCanonDomain

end PGM
