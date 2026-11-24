import PLAStochastic.Index.CEPS.Canonical.MorseChart
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.AbsMax

/-!
# CEPS WP3: the two near-zero roots and the removed quadratic factor

Blueprint §3.1–§3.2 and the root part of lemma C-1. For `(μ, q)` let `m = m(μ)` be the Morse
minimum, `r₊ = √(q - m)` (principal branch, `cepsRootR`) and

  `β₊ = Θ(r₊, μ)`, `β₋ = Θ(-r₊, μ)`   (`cepsRootPlus`, `cepsRootMinus`).

With `Φ(ζ) = ψ_μ(ζ) - q` (`cepsRootEq`) and `D₀(ζ) = (ζ - β₊)(ζ - β₋)` (`cepsQuad`):

* `cepsRootEq_rootPlus`, `cepsRootEq_rootMinus`: `Φ(β±) = 0`;
* `norm_rootPlus_sub_center_le`: `‖β± - β*‖ ≤ K_Θ ‖r₊‖`, `K_Θ = 2/√(v₋/2)` (`cepsChartK`);
* `cepsRootEq_eq_quad_mul`: `Φ = D₀ · H` on `B(0, r₀)` with `H = cepsRootQuot` holomorphic
  (`differentiableOn_cepsRootQuot`), the two roots removed by iterated `dslope`;
* `norm_cepsRootQuot_sub_le`: on `closedBall 0 ρ_H`, `‖H - E W²/2‖ ≤ 5 C₃ ρ_H + 4‖r₊‖²/ρ_H²
  + 6 v K_Θ ‖r₊‖/ρ_H` (maximum modulus principle from the circle `‖ζ‖ = ρ_H`, where the chart
  identity `Φ(β* + u) = u² k(β*, u) - r₊²` is used).

Also the factor definitions `cepsD` (`d(ζ; μ, q) = 1 - e^{-q} e^{μζ} M₀(ζ)`) and `cepsF`
(`F = d (ζ² - γ²)/D₀`) of blueprint (1.3), (3.2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `r₊ = √(q - m(μ))`, principal branch. -/
def cepsRootR (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ :=
  Complex.sqrt (q - cepsMorseMin D θ ρW μ)

/-- `β₊ = Θ(r₊, μ)`. -/
def cepsRootPlus (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ :=
  cepsMorseRoot D θ ρW μ (cepsRootR D θ ρW μ q)

/-- `β₋ = Θ(-r₊, μ)`. -/
def cepsRootMinus (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ :=
  cepsMorseRoot D θ ρW μ (-cepsRootR D θ ρW μ q)

/-- The removed quadratic `D₀(ζ) = (ζ - β₊)(ζ - β₋)`. -/
def cepsQuad (D θ : ℝ) (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ :=
  (ζ - cepsRootPlus D θ ρW μ q) * (ζ - cepsRootMinus D θ ρW μ q)

/-- `d(ζ; μ, q) = 1 - e^{-q} e^{μ ζ} M₀(ζ)`. -/
def cepsD (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ := 1 - cexp (-q) * cexp (μ * ζ) * stepTransform ρW ζ

/-- `F(ζ; μ, q) = d(ζ) (ζ² - γ²)/D₀(ζ)` (blueprint (3.2): `F = Q (γ² - ζ²)`,
`Q = d/((β₊ - ζ)(ζ - β₋))`). -/
def cepsF (D θ : ℝ) (ρW : Measure ℝ) (γ μ q ζ : ℂ) : ℂ :=
  cepsD ρW μ q ζ * (ζ ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q ζ

/-- `Φ(ζ) = ψ_μ(ζ) - q`. -/
def cepsRootEq (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ := cepsCgfShift ρW μ ζ - q

/-- `H = Φ / D₀` with both roots removed. -/
def cepsRootQuot (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) : ℂ → ℂ :=
  dslope (dslope (cepsRootEq ρW μ q) (cepsRootPlus D θ ρW μ q)) (cepsRootMinus D θ ρW μ q)

/-- `K_Θ = 2/√(v₋/2)`: the class Lipschitz constant of the chart. -/
def cepsChartK (D : ℝ) : ℝ := 2 / Real.sqrt (cepsVarLo D / 2)

theorem cepsChartK_pos {D : ℝ} (hD : 0 < D) : 0 < cepsChartK D := by
  have := cepsVarLo_pos hD
  unfold cepsChartK; have : 0 < Real.sqrt (cepsVarLo D / 2) := Real.sqrt_pos.mpr (by positivity)
  positivity

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

theorem cepsRootR_sq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) :
    cepsRootR D θ ρW μ q ^ 2 = q - cepsMorseMin D θ ρW μ := by
  rw [cepsRootR, Complex.sqrt]; exact cpow_ofNat_inv_pow _ 2

theorem norm_cepsRootR_sq (D θ : ℝ) (ρW : Measure ℝ) (μ q : ℂ) :
    ‖cepsRootR D θ ρW μ q‖ ^ 2 = ‖q - cepsMorseMin D θ ρW μ‖ := by
  rw [← norm_pow, cepsRootR_sq]

section Roots

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `ψ_μ(β* + u) = m(μ) + u² k(β*, u)` for `‖β*‖ + ‖u‖ < r₀`. -/
theorem cepsCgfShift_center_add {μ u : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hu : ‖cepsMorseCenter D θ ρW μ‖ + ‖u‖ < cepsCgfRadius D θ) :
    cepsCgfShift ρW μ (cepsMorseCenter D θ ρW μ + u) =
      cepsMorseMin D θ ρW μ + u ^ 2 * cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u := by
  set b := cepsMorseCenter D θ ρW μ
  have hspec := hadamard2_spec (ψ := cepsCgf ρW) isOpen_ball (differentiableOn_cepsCgf hW hθ hD)
    (b := b) (u := u) (fun t ht => by
      rw [mem_ball, dist_zero_right]
      calc ‖b + t * u‖ ≤ ‖b‖ + ‖(t : ℂ)‖ * ‖u‖ := by rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ ‖b‖ + 1 * ‖u‖ := by
            gcongr
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
        _ < cepsCgfRadius D θ := by linarith)
  rw [cepsMorseMin, cepsCgfShift, cepsCgfShift, hspec, deriv_cepsCgf_cepsMorseCenter hW hθ hD hμ,
    cepsMorseK]
  ring

/-- `‖k(b, u)‖ ≤ v` on the chart region. -/
theorem norm_cepsMorseK_le {b u : ℂ} (hb : ‖b‖ < cepsChartRadius D θ)
    (hu : ‖u‖ < 2 * cepsChartRadius D θ) : ‖cepsMorseK ρW b u‖ ≤ v := by
  have h := cepsMorseK_near hW hθ hD hb hu
  have hvl := cepsVarLo_le hW hθ hD
  have hvv := cepsStepVar_le hW
  have hv0 := cepsStepVar_pos hW hθ hD
  have h2 : ‖(cepsStepVar ρW : ℂ) / 2‖ = cepsStepVar ρW / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hv0]; simp
  calc ‖cepsMorseK ρW b u‖ = ‖(cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2) +
        (cepsStepVar ρW : ℂ) / 2‖ := by ring_nf
    _ ≤ 3 * cepsVarLo D / 128 + cepsStepVar ρW / 2 := by
        rw [← h2]; exact (norm_add_le _ _).trans (add_le_add h le_rfl)
    _ ≤ v := by linarith

/-- `m(μ) = -β*² k(β*, -β*)`, hence `‖m(μ)‖ ≤ v ‖β*‖²`. -/
theorem norm_cepsMorseMin_le {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    ‖cepsMorseMin D θ ρW μ‖ ≤ v * ‖cepsMorseCenter D θ ρW μ‖ ^ 2 := by
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have h := cepsCgfShift_center_add hW hθ hD hμ (u := -cepsMorseCenter D θ ρW μ)
    (by rw [norm_neg]; linarith)
  rw [add_neg_cancel, cepsCgfShift, cepsCgf_zero hW, mul_zero, add_zero] at h
  have hm : cepsMorseMin D θ ρW μ = -(cepsMorseCenter D θ ρW μ ^ 2 *
      cepsMorseK ρW (cepsMorseCenter D θ ρW μ) (-cepsMorseCenter D θ ρW μ)) := by
    rw [neg_sq] at h; linear_combination -h
  have hk := norm_cepsMorseK_le hW hθ hD hb (u := -cepsMorseCenter D θ ρW μ)
    (by rw [norm_neg]; linarith [cepsChartRadius_pos hD hθ])
  rw [hm, norm_neg, norm_mul, norm_pow]
  calc ‖cepsMorseCenter D θ ρW μ‖ ^ 2 * ‖cepsMorseK ρW (cepsMorseCenter D θ ρW μ)
        (-cepsMorseCenter D θ ρW μ)‖ ≤ ‖cepsMorseCenter D θ ρW μ‖ ^ 2 * v := by gcongr
    _ = v * ‖cepsMorseCenter D θ ρW μ‖ ^ 2 := by ring

/-- `Φ(β₊) = 0`. -/
theorem cepsRootEq_rootPlus {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    cepsRootEq ρW μ q (cepsRootPlus D θ ρW μ q) = 0 := by
  rw [cepsRootEq, cepsRootPlus, cepsCgfShift_cepsMorseRoot hW hθ hD hμ hr, cepsRootR_sq]; ring

/-- `Φ(β₋) = 0`. -/
theorem cepsRootEq_rootMinus {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    cepsRootEq ρW μ q (cepsRootMinus D θ ρW μ q) = 0 := by
  rw [cepsRootEq, cepsRootMinus, cepsCgfShift_cepsMorseRoot hW hθ hD hμ (by rwa [norm_neg]),
    neg_sq, cepsRootR_sq]; ring

/-- The chart Lipschitz constant is at most `K_Θ`. -/
theorem two_div_norm_cepsChartSlope_le : 2 / ‖cepsChartSlope ρW‖ ≤ cepsChartK D := by
  have h := cepsChartSlope_ge hW hθ hD
  have hv := cepsVarLo_pos hD
  have h0 : 0 < Real.sqrt (cepsVarLo D / 2) := Real.sqrt_pos.mpr (by positivity)
  exact div_le_div_of_nonneg_left (by norm_num) h0 h

theorem norm_cepsMorseRoot_sub_center_le {μ r : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖r‖ < cepsChartRho D θ) :
    ‖cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ‖ ≤ cepsChartK D * ‖r‖ := by
  have h0 : ‖(0 : ℂ)‖ < cepsChartRho D θ := by simpa using cepsChartRho_pos hD hθ
  have := norm_cepsMorseRoot_sub_le hW hθ hD hμ hr h0
  rw [cepsMorseRoot_zero hW hθ hD hμ, sub_zero] at this
  exact this.trans (mul_le_mul_of_nonneg_right (two_div_norm_cepsChartSlope_le hW hθ hD)
    (norm_nonneg _))

theorem norm_rootPlus_sub_center_le {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    ‖cepsRootPlus D θ ρW μ q - cepsMorseCenter D θ ρW μ‖ ≤
      cepsChartK D * ‖cepsRootR D θ ρW μ q‖ :=
  norm_cepsMorseRoot_sub_center_le hW hθ hD hμ hr

theorem norm_rootMinus_sub_center_le {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    ‖cepsRootMinus D θ ρW μ q - cepsMorseCenter D θ ρW μ‖ ≤
      cepsChartK D * ‖cepsRootR D θ ρW μ q‖ := by
  have := norm_cepsMorseRoot_sub_center_le hW hθ hD hμ (r := -cepsRootR D θ ρW μ q)
    (by rwa [norm_neg])
  rwa [norm_neg] at this

/-- The two roots coincide only when `r₊ = 0`, in which case they equal `β*`. -/
theorem rootPlus_eq_rootMinus_iff {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    cepsRootPlus D θ ρW μ q = cepsRootMinus D θ ρW μ q ↔ cepsRootR D θ ρW μ q = 0 := by
  constructor
  · intro h
    have := cepsMorseRoot_injective hW hθ hD hμ hr (by rwa [norm_neg]) h
    have h2 : (2 : ℂ) * cepsRootR D θ ρW μ q = 0 := by linear_combination this
    simpa using h2
  · intro h
    rw [cepsRootPlus, cepsRootMinus, h, neg_zero]

theorem differentiableOn_cepsRootEq (μ q : ℂ) :
    DifferentiableOn ℂ (cepsRootEq ρW μ q) (ball 0 (cepsCgfRadius D θ)) := by
  intro ζ hζ
  have h1 := (differentiableOn_cepsCgf hW hθ hD ζ hζ).differentiableAt (isOpen_ball.mem_nhds hζ)
  exact ((h1.add (differentiableAt_id.const_mul μ)).sub_const q).differentiableWithinAt

theorem rootPlus_mem_ball {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    cepsRootPlus D θ ρW μ q ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
  obtain ⟨hu, -⟩ := cepsMorseRoot_sub_center hW hθ hD hμ hr
  rw [mem_ball, dist_zero_right] at hu ⊢
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  calc ‖cepsRootPlus D θ ρW μ q‖ = ‖cepsMorseCenter D θ ρW μ +
        (cepsMorseRoot D θ ρW μ (cepsRootR D θ ρW μ q) - cepsMorseCenter D θ ρW μ)‖ := by
        rw [cepsRootPlus]; ring_nf
    _ ≤ _ := norm_add_le _ _
    _ < cepsCgfRadius D θ := by linarith

theorem rootMinus_mem_ball {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    cepsRootMinus D θ ρW μ q ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
  obtain ⟨hu, -⟩ := cepsMorseRoot_sub_center hW hθ hD hμ (r := -cepsRootR D θ ρW μ q)
    (by rwa [norm_neg])
  rw [mem_ball, dist_zero_right] at hu ⊢
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  calc ‖cepsRootMinus D θ ρW μ q‖ = ‖cepsMorseCenter D θ ρW μ +
        (cepsMorseRoot D θ ρW μ (-cepsRootR D θ ρW μ q) - cepsMorseCenter D θ ρW μ)‖ := by
        rw [cepsRootMinus]; ring_nf
    _ ≤ _ := norm_add_le _ _
    _ < cepsCgfRadius D θ := by linarith

/-- `dslope Φ β₊` vanishes at `β₋` (also when the roots coincide). -/
theorem dslope_cepsRootEq_rootMinus {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    dslope (cepsRootEq ρW μ q) (cepsRootPlus D θ ρW μ q) (cepsRootMinus D θ ρW μ q) = 0 := by
  by_cases hne : cepsRootMinus D θ ρW μ q = cepsRootPlus D θ ρW μ q
  · -- double root: `r₊ = 0`, both roots are `β*`, and `ψ_μ'(β*) = 0`
    have hr0 : cepsRootR D θ ρW μ q = 0 :=
      (rootPlus_eq_rootMinus_iff hW hθ hD hμ hr).mp hne.symm
    rw [hne, dslope_same]
    have hc : cepsRootPlus D θ ρW μ q = cepsMorseCenter D θ ρW μ := by
      rw [cepsRootPlus, hr0, cepsMorseRoot_zero hW hθ hD hμ]
    rw [hc]
    have hmem : cepsMorseCenter D θ ρW μ ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
      rw [← hc]; exact rootPlus_mem_ball hW hθ hD hμ hr
    have hd := (differentiableOn_cepsCgf hW hθ hD _ hmem).differentiableAt
      (isOpen_ball.mem_nhds hmem)
    have h1 : HasDerivAt (cepsRootEq ρW μ q)
        (deriv (cepsCgf ρW) (cepsMorseCenter D θ ρW μ) + μ * 1) (cepsMorseCenter D θ ρW μ) :=
      ((hd.hasDerivAt.add ((hasDerivAt_id _).const_mul μ)).sub_const q)
    rw [h1.deriv, deriv_cepsCgf_cepsMorseCenter hW hθ hD hμ]; ring
  · rw [dslope_of_ne _ hne, slope_def_field, cepsRootEq_rootMinus hW hθ hD hμ hr,
      cepsRootEq_rootPlus hW hθ hD hμ hr, sub_self, zero_div]

/-- `Φ = D₀ · H` on `B(0, r₀)`. -/
theorem cepsRootEq_eq_quad_mul {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) (ζ : ℂ) :
    cepsRootEq ρW μ q ζ = cepsQuad D θ ρW μ q ζ * cepsRootQuot D θ ρW μ q ζ := by
  have h1 := sub_smul_dslope (cepsRootEq ρW μ q) (cepsRootPlus D θ ρW μ q) ζ
  have h2 := sub_smul_dslope (dslope (cepsRootEq ρW μ q) (cepsRootPlus D θ ρW μ q))
    (cepsRootMinus D θ ρW μ q) ζ
  rw [cepsRootEq_rootPlus hW hθ hD hμ hr, sub_zero, smul_eq_mul] at h1
  rw [dslope_cepsRootEq_rootMinus hW hθ hD hμ hr, sub_zero, smul_eq_mul] at h2
  rw [cepsQuad, cepsRootQuot, ← h1, ← h2]; ring

theorem differentiableOn_cepsRootQuot {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) :
    DifferentiableOn ℂ (cepsRootQuot D θ ρW μ q) (ball 0 (cepsCgfRadius D θ)) := by
  rw [cepsRootQuot, differentiableOn_dslope (isOpen_ball.mem_nhds
    (rootMinus_mem_ball hW hθ hD hμ hr)), differentiableOn_dslope (isOpen_ball.mem_nhds
    (rootPlus_mem_ball hW hθ hD hμ hr))]
  exact differentiableOn_cepsRootEq hW hθ hD μ q

/-- **Removed quadratic (C-1, zone A).** On `closedBall 0 ρ_H` the quotient `H = Φ/D₀` is close to
`E W²/2`, by the maximum modulus principle and the chart identity on the circle. -/
theorem norm_cepsRootQuot_sub_le {μ q : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ) {ρH : ℝ} (hρH : 0 < ρH)
    (hρR : 2 * ρH ≤ cepsChartRadius D θ)
    (hb : ‖cepsMorseCenter D θ ρW μ‖ ≤ ρH / 4)
    (hrK : cepsChartK D * ‖cepsRootR D θ ρW μ q‖ ≤ ρH / 4) {ζ : ℂ} (hζ : ‖ζ‖ ≤ ρH) :
    ‖cepsRootQuot D θ ρW μ q ζ - (cepsStepVar ρW : ℂ) / 2‖ ≤
      5 * cepsCgfC3 D θ * ρH + 4 * ‖cepsRootR D θ ρW μ q‖ ^ 2 / ρH ^ 2 +
        6 * v * cepsChartK D * ‖cepsRootR D θ ρW μ q‖ / ρH := by
  set r := cepsRootR D θ ρW μ q with hrdef
  set b := cepsMorseCenter D θ ρW μ with hbdef
  set E : ℝ := 5 * cepsCgfC3 D θ * ρH + 4 * ‖r‖ ^ 2 / ρH ^ 2 +
    6 * v * cepsChartK D * ‖r‖ / ρH with hE
  have hR := cepsChartRadius_pos hD hθ
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hC3 := cepsCgfC3_pos hD hθ
  have hK := cepsChartK_pos hD
  have hvW := cepsStepVar_pos hW hθ hD
  have hvv := cepsStepVar_le hW
  have hv : 0 < v := lt_of_lt_of_le hvW hvv
  -- holomorphy of `H - E W²/2` near the closed disc
  have hsub : closedBall (0 : ℂ) ρH ⊆ ball 0 (cepsCgfRadius D θ) :=
    closedBall_subset_ball (by linarith)
  have hHd : DifferentiableOn ℂ (fun z => cepsRootQuot D θ ρW μ q z - (cepsStepVar ρW : ℂ) / 2)
      (ball 0 (cepsCgfRadius D θ)) :=
    (differentiableOn_cepsRootQuot hW hθ hD hμ hr).sub_const _
  have hDC := hHd.diffContOnCl_ball hsub
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hDC ?_
    (by rw [closure_ball _ hρH.ne']; simpa [mem_closedBall, dist_zero_right] using hζ)
  intro z hz
  rw [frontier_ball _ hρH.ne', mem_sphere, dist_zero_right] at hz
  -- data on the circle
  set u := z - b with hudef
  set δp := cepsRootPlus D θ ρW μ q - b with hδp
  set δm := cepsRootMinus D θ ρW μ q - b with hδm
  have hδpn : ‖δp‖ ≤ cepsChartK D * ‖r‖ := norm_rootPlus_sub_center_le hW hθ hD hμ hr
  have hδmn : ‖δm‖ ≤ cepsChartK D * ‖r‖ := norm_rootMinus_sub_center_le hW hθ hD hμ hr
  have hu1 : ‖u‖ ≤ 5 * ρH / 4 := by
    calc ‖u‖ ≤ ‖z‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ 5 * ρH / 4 := by linarith
  have hu2 : 3 * ρH / 4 ≤ ‖u‖ := by
    have := norm_sub_norm_le z b
    linarith
  have hup : ρH / 2 ≤ ‖u - δp‖ := by
    have := norm_sub_norm_le u δp; linarith
  have hum : ρH / 2 ≤ ‖u - δm‖ := by
    have := norm_sub_norm_le u δm; linarith
  have hzβp : z - cepsRootPlus D θ ρW μ q = u - δp := by rw [hudef, hδp]; ring
  have hzβm : z - cepsRootMinus D θ ρW μ q = u - δm := by rw [hudef, hδm]; ring
  have hquad : cepsQuad D θ ρW μ q z = (u - δp) * (u - δm) := by rw [cepsQuad, hzβp, hzβm]
  have hquad0 : cepsQuad D θ ρW μ q z ≠ 0 := by
    rw [hquad]
    refine mul_ne_zero ?_ ?_
    · intro h; rw [h, norm_zero] at hup; linarith
    · intro h; rw [h, norm_zero] at hum; linarith
  -- `H(z) = Φ(z)/D₀(z)` and `Φ(z) = u² k(b, u) - r²`
  have hH : cepsRootQuot D θ ρW μ q z = cepsRootEq ρW μ q z / cepsQuad D θ ρW μ q z := by
    rw [cepsRootEq_eq_quad_mul hW hθ hD hμ hr z]; field_simp
  have hΦ : cepsRootEq ρW μ q z = u ^ 2 * cepsMorseK ρW b u - r ^ 2 := by
    have := cepsCgfShift_center_add hW hθ hD hμ (u := u) (by linarith)
    rw [show b + u = z by rw [hudef]; ring] at this
    rw [cepsRootEq, this, hrdef, cepsRootR_sq]; ring
  have hk : ‖cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2‖ ≤ 3 / 4 * cepsCgfC3 D θ * ρH := by
    have h := norm_cepsMorseK_sub_le hW hθ hD (b := b) (u := u) (by linarith)
    calc _ ≤ cepsCgfC3 D θ * (‖b‖ + ‖u‖) / 2 := h
      _ ≤ cepsCgfC3 D θ * (ρH / 4 + 5 * ρH / 4) / 2 := by gcongr
      _ = 3 / 4 * cepsCgfC3 D θ * ρH := by ring
  have hvW2 : ‖(cepsStepVar ρW : ℂ) / 2‖ ≤ v / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hvW]; simp; linarith
  -- the numerator
  have hnum : cepsRootEq ρW μ q z - (cepsStepVar ρW : ℂ) / 2 * cepsQuad D θ ρW μ q z =
      u ^ 2 * (cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2) - r ^ 2 +
        (cepsStepVar ρW : ℂ) / 2 * (u * (δp + δm) - δp * δm) := by
    rw [hΦ, hquad]; ring
  have hnumb : ‖cepsRootEq ρW μ q z - (cepsStepVar ρW : ℂ) / 2 * cepsQuad D θ ρW μ q z‖ ≤
      (5 * ρH / 4) ^ 2 * (3 / 4 * cepsCgfC3 D θ * ρH) + ‖r‖ ^ 2 +
        v / 2 * ((5 * ρH / 4) * (2 * (cepsChartK D * ‖r‖)) + (cepsChartK D * ‖r‖) ^ 2) := by
    rw [hnum]
    have e1 : ‖u ^ 2 * (cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2)‖ ≤
        (5 * ρH / 4) ^ 2 * (3 / 4 * cepsCgfC3 D θ * ρH) := by
      rw [norm_mul, norm_pow]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu1 2) hk (norm_nonneg _)
        (by positivity)
    have e2 : ‖(cepsStepVar ρW : ℂ) / 2 * (u * (δp + δm) - δp * δm)‖ ≤
        v / 2 * ((5 * ρH / 4) * (2 * (cepsChartK D * ‖r‖)) + (cepsChartK D * ‖r‖) ^ 2) := by
      rw [norm_mul]
      refine mul_le_mul hvW2 ?_ (norm_nonneg _) (by linarith)
      calc ‖u * (δp + δm) - δp * δm‖ ≤ ‖u‖ * (‖δp‖ + ‖δm‖) + ‖δp‖ * ‖δm‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
            gcongr
            exact norm_add_le _ _
        _ ≤ (5 * ρH / 4) * (2 * (cepsChartK D * ‖r‖)) + (cepsChartK D * ‖r‖) ^ 2 := by
            have := norm_nonneg δp; have := norm_nonneg δm
            nlinarith [mul_le_mul hδpn hδmn (norm_nonneg _) (by positivity)]
    calc _ ≤ ‖u ^ 2 * (cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2) - r ^ 2‖ +
          ‖(cepsStepVar ρW : ℂ) / 2 * (u * (δp + δm) - δp * δm)‖ := norm_add_le _ _
      _ ≤ (‖u ^ 2 * (cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2)‖ + ‖r ^ 2‖) +
          ‖(cepsStepVar ρW : ℂ) / 2 * (u * (δp + δm) - δp * δm)‖ := by
          gcongr; exact norm_sub_le _ _
      _ ≤ _ := by rw [norm_pow]; linarith
  have hden : ρH ^ 2 / 4 ≤ ‖cepsQuad D θ ρW μ q z‖ := by
    rw [hquad, norm_mul]
    calc ρH ^ 2 / 4 = (ρH / 2) * (ρH / 2) := by ring
      _ ≤ ‖u - δp‖ * ‖u - δm‖ := mul_le_mul hup hum (by positivity) (norm_nonneg _)
  have hden0 : 0 < ‖cepsQuad D θ ρW μ q z‖ := lt_of_lt_of_le (by positivity) hden
  have hdiff : cepsRootQuot D θ ρW μ q z - (cepsStepVar ρW : ℂ) / 2 =
      (cepsRootEq ρW μ q z - (cepsStepVar ρW : ℂ) / 2 * cepsQuad D θ ρW μ q z) /
        cepsQuad D θ ρW μ q z := by
    rw [hH]; field_simp
  rw [hdiff, norm_div, div_le_iff₀ hden0]
  refine hnumb.trans ?_
  -- arithmetic
  have hKr : cepsChartK D * ‖r‖ ≤ ρH / 4 := hrK
  have hrn := norm_nonneg r
  have hE1 : (5 * ρH / 4) ^ 2 * (3 / 4 * cepsCgfC3 D θ * ρH) ≤
      5 * cepsCgfC3 D θ * ρH * (ρH ^ 2 / 4) := by
    have h0 : 0 ≤ cepsCgfC3 D θ * ρH ^ 3 := by positivity
    have e1 : (5 * ρH / 4) ^ 2 * (3 / 4 * cepsCgfC3 D θ * ρH) =
        75 / 64 * (cepsCgfC3 D θ * ρH ^ 3) := by ring
    have e2 : 5 * cepsCgfC3 D θ * ρH * (ρH ^ 2 / 4) = 80 / 64 * (cepsCgfC3 D θ * ρH ^ 3) := by ring
    rw [e1, e2]; linarith
  have hE2 : ‖r‖ ^ 2 ≤ 4 * ‖r‖ ^ 2 / ρH ^ 2 * (ρH ^ 2 / 4) := by
    rw [show 4 * ‖r‖ ^ 2 / ρH ^ 2 * (ρH ^ 2 / 4) = ‖r‖ ^ 2 by field_simp]
  have hE3 : v / 2 * ((5 * ρH / 4) * (2 * (cepsChartK D * ‖r‖)) + (cepsChartK D * ‖r‖) ^ 2) ≤
      6 * v * cepsChartK D * ‖r‖ / ρH * (ρH ^ 2 / 4) := by
    have : (cepsChartK D * ‖r‖) ^ 2 ≤ (cepsChartK D * ‖r‖) * (ρH / 4) := by
      rw [sq]; exact mul_le_mul_of_nonneg_left hKr (by positivity)
    rw [show 6 * v * cepsChartK D * ‖r‖ / ρH * (ρH ^ 2 / 4) =
      v / 2 * (3 * ρH * (cepsChartK D * ‖r‖)) by field_simp; ring]
    gcongr
    nlinarith
  calc _ ≤ 5 * cepsCgfC3 D θ * ρH * (ρH ^ 2 / 4) + 4 * ‖r‖ ^ 2 / ρH ^ 2 * (ρH ^ 2 / 4) +
        6 * v * cepsChartK D * ‖r‖ / ρH * (ρH ^ 2 / 4) := by linarith
    _ = E * (ρH ^ 2 / 4) := by rw [hE]; ring
    _ ≤ E * ‖cepsQuad D θ ρW μ q z‖ := by
        have hE0 : 0 ≤ E := by rw [hE]; positivity
        exact mul_le_mul_of_nonneg_left hden hE0

end Roots

end PGM
