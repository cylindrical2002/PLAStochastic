import PLAStochastic.Index.CEPS.Canonical.Cumulant
import PLAStochastic.ForMathlib.Analysis.Complex.ParamInverse
import PLAStochastic.ForMathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.SqrtDeriv

/-!
# CEPS WP3, lemma C-2: the Morse root chart

Blueprint `research/2026-10-02-lean-ceps/blueprint-CS.md` §3.1. For a step law in the class
`IsStepLaw ρW fW D θ v` let `ψ₀ = cepsCgf ρW = log M₀` and `ψ_μ(ζ) = ψ₀(ζ) + μ ζ`
(`cepsCgfShift`). With class constants depending only on `(D, θ)`:

* the centre `β*(μ) = cepsMorseCenter D θ ρW μ` solves `ψ₀'(β*) = -μ` and is holomorphic in complex
  `μ` with `‖μ‖ < cepsChartMu D θ`;
* the minimum `m(μ) = ψ_μ(β*(μ))` (`cepsMorseMin`);
* the chart `Θ(r, μ) = cepsMorseRoot D θ ρW μ r` is jointly holomorphic in `(μ, r)` on
  `‖μ‖ < cepsChartMu D θ`, `‖r‖ < cepsChartRho D θ`, and satisfies
  `ψ_μ(Θ(r, μ)) = m(μ) + r²`, `Θ(0, μ) = β*(μ)`, `∂_r Θ(0, μ) = √(2/ψ₀''(β*))`
  (`cepsMorse_spec`, `differentiableOn_cepsMorseRoot`, `hasDerivAt_cepsMorseRoot_zero`).

Construction: `β*` is the quantitative inverse (`PGM.ParamInvHyp`) of `ψ₀'`, whose derivative stays
within `E W²/2` of `E W²` on a class disc; with the Hadamard quotient
`k(b, u) = ∫₀¹ (1-t) ψ₀''(b + t u) dt` one has `ψ_μ(β* + u) - m(μ) = u² k(β*, u)`, and
`Θ - β*` is the inverse in `u` of `g(μ, u) = u √(k(β*(μ), u))`, whose `u`-derivative stays within
`a/2` of `a = √(E W²/2)` (Cauchy estimate on a doubled disc).

No Weierstrass preparation or argument principle is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-! ### Class constants -/

/-- `ψ_μ(ζ) = ψ₀(ζ) + μ ζ`. -/
def cepsCgfShift (ρW : Measure ℝ) (μ ζ : ℂ) : ℂ := cepsCgf ρW ζ + μ * ζ

/-- The class lower bound `v₋ = 1/(256 D²)` on `E W²`. -/
def cepsVarLo (D : ℝ) : ℝ := 1 / (256 * D ^ 2)

/-- The class bound `C₃ = 288/r₀³` on `‖ψ₀'''‖` on `B(0, r₀/2)`. -/
def cepsCgfC3 (D θ : ℝ) : ℝ := 288 / cepsCgfRadius D θ ^ 3

/-- Radius of the centre inverse: `min (r₀/2) (v₋/(2 C₃))`. -/
def cepsCenterRadius (D θ : ℝ) : ℝ := min (cepsCgfRadius D θ / 2) (cepsVarLo D / (2 * cepsCgfC3 D θ))

/-- Radius of the chart in `u = ζ - β*`: `R_Θ = min (r₀/8) (v₋/(64 C₃))`. -/
def cepsChartRadius (D θ : ℝ) : ℝ :=
  min (cepsCgfRadius D θ / 8) (cepsVarLo D / (64 * cepsCgfC3 D θ))

/-- Drift radius of the chart: `μ_c = v₋ R_Θ / 2`. -/
def cepsChartMu (D θ : ℝ) : ℝ := cepsVarLo D * cepsChartRadius D θ / 2

/-- Radius of the chart variable: `r₁ = √(v₋/2) R_Θ / 2`. -/
def cepsChartRho (D θ : ℝ) : ℝ := Real.sqrt (cepsVarLo D / 2) * cepsChartRadius D θ / 2

section Constants

variable {D θ : ℝ}

theorem cepsVarLo_pos (hD : 0 < D) : 0 < cepsVarLo D := by unfold cepsVarLo; positivity

theorem cepsCgfC3_pos (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsCgfC3 D θ := by
  have := cepsCgfRadius_pos hD hθ; unfold cepsCgfC3; positivity

theorem cepsCenterRadius_pos (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsCenterRadius D θ := by
  have := cepsCgfRadius_pos hD hθ; have := cepsVarLo_pos hD; have := cepsCgfC3_pos hD hθ
  exact lt_min (by positivity) (by positivity)

theorem cepsChartRadius_pos (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsChartRadius D θ := by
  have := cepsCgfRadius_pos hD hθ; have := cepsVarLo_pos hD; have := cepsCgfC3_pos hD hθ
  exact lt_min (by positivity) (by positivity)

theorem cepsChartMu_pos (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsChartMu D θ := by
  have := cepsVarLo_pos hD; have := cepsChartRadius_pos hD hθ; unfold cepsChartMu; positivity

theorem cepsChartRho_pos (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsChartRho D θ := by
  have := cepsVarLo_pos hD; have := cepsChartRadius_pos hD hθ
  have : 0 < Real.sqrt (cepsVarLo D / 2) := Real.sqrt_pos.mpr (by positivity)
  unfold cepsChartRho; positivity

theorem cepsChartRadius_le_center (hD : 0 < D) (hθ : 0 < θ) :
    cepsChartRadius D θ ≤ cepsCenterRadius D θ := by
  have hr := cepsCgfRadius_pos hD hθ
  have hv := cepsVarLo_pos hD
  have hc := cepsCgfC3_pos hD hθ
  refine le_min ((min_le_left _ _).trans (by linarith)) ((min_le_right _ _).trans ?_)
  exact div_le_div_of_nonneg_left hv.le (by positivity) (by linarith)

theorem cepsChartRadius_le_r0 : cepsChartRadius D θ ≤ cepsCgfRadius D θ / 8 := min_le_left _ _

theorem cepsCgfC3_mul_chartRadius_le (hD : 0 < D) (hθ : 0 < θ) :
    cepsCgfC3 D θ * cepsChartRadius D θ ≤ cepsVarLo D / 64 := by
  have hc := cepsCgfC3_pos hD hθ
  have := min_le_right (cepsCgfRadius D θ / 8) (cepsVarLo D / (64 * cepsCgfC3 D θ))
  calc cepsCgfC3 D θ * cepsChartRadius D θ
      ≤ cepsCgfC3 D θ * (cepsVarLo D / (64 * cepsCgfC3 D θ)) :=
        mul_le_mul_of_nonneg_left this hc.le
    _ = cepsVarLo D / 64 := by field_simp

end Constants

/-! ### The centre `β*(μ)` -/

/-- `β*(μ)`: the solution of `ψ₀'(β) = -μ` in `B(0, cepsCenterRadius D θ)`. -/
@[irreducible] def cepsMorseCenter (D θ : ℝ) (ρW : Measure ℝ) (μ : ℂ) : ℂ :=
  paramInv (fun _ z => deriv (cepsCgf ρW) z) (cepsCenterRadius D θ) 0 (-μ)

/-- The minimum value `m(μ) = ψ_μ(β*(μ))`. -/
def cepsMorseMin (D θ : ℝ) (ρW : Measure ℝ) (μ : ℂ) : ℂ :=
  cepsCgfShift ρW μ (cepsMorseCenter D θ ρW μ)

/-- The Hadamard quotient `k(b, u) = ∫₀¹ (1-t) ψ₀''(b + t u) dt`. -/
@[irreducible] def cepsMorseK (ρW : Measure ℝ) (b u : ℂ) : ℂ := hadamard2 (cepsCgf ρW) b u

/-- `g(μ, u) = u √(k(β*(μ), u))`. -/
@[irreducible] def cepsMorseG (D θ : ℝ) (ρW : Measure ℝ) (μ u : ℂ) : ℂ :=
  u * Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u)

/-- The Morse root chart `Θ(r, μ) = β*(μ) + g(μ, ·)⁻¹(r)`. -/
@[irreducible] def cepsMorseRoot (D θ : ℝ) (ρW : Measure ℝ) (μ r : ℂ) : ℂ :=
  cepsMorseCenter D θ ρW μ + paramInv (cepsMorseG D θ ρW) (cepsChartRadius D θ) μ r

theorem cepsMorseCenter_eq (D θ : ℝ) (ρW : Measure ℝ) :
    cepsMorseCenter D θ ρW =
      fun μ => paramInv (fun _ z => deriv (cepsCgf ρW) z) (cepsCenterRadius D θ) 0 (-μ) := by
  funext μ; rw [cepsMorseCenter]

theorem cepsMorseK_eq (ρW : Measure ℝ) : cepsMorseK ρW = hadamard2 (cepsCgf ρW) := by
  funext b u; rw [cepsMorseK]

theorem cepsMorseRoot_eq (D θ : ℝ) (ρW : Measure ℝ) (μ : ℂ) :
    cepsMorseRoot D θ ρW μ =
      fun r => cepsMorseCenter D θ ρW μ + paramInv (cepsMorseG D θ ρW) (cepsChartRadius D θ) μ r := by
  funext r; rw [cepsMorseRoot]

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

section Center

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem cepsStepVar_pos : 0 < cepsStepVar ρW :=
  lt_of_lt_of_le (cepsVarLo_pos hD) (cepsStepVar_ge hW hθ hD)

theorem cepsVarLo_le : cepsVarLo D ≤ cepsStepVar ρW := cepsStepVar_ge hW hθ hD

/-- `ψ₀''` stays within `C₃ ‖ζ‖` of `E W²` on `B(0, r₀/2)`. -/
theorem norm_deriv2_cepsCgf_sub_le' {ζ : ℂ} (hζ : ‖ζ‖ < cepsCgfRadius D θ / 2) :
    ‖deriv (deriv (cepsCgf ρW)) ζ - cepsStepVar ρW‖ ≤ cepsCgfC3 D θ * ‖ζ‖ :=
  norm_deriv2_cepsCgf_sub_le hW hθ hD (by rwa [mem_ball, dist_zero_right])

theorem cepsCenter_hyp :
    ParamInvHyp univ (fun _ z => deriv (cepsCgf ρW) z) (cepsStepVar ρW : ℂ)
      (cepsCenterRadius D θ) := by
  have hr0 := cepsCgfRadius_pos hD hθ
  have hRβ := cepsCenterRadius_pos hD hθ
  have hRβle : cepsCenterRadius D θ ≤ cepsCgfRadius D θ / 2 := min_le_left _ _
  have hd1 : DifferentiableOn ℂ (deriv (cepsCgf ρW)) (ball 0 (cepsCgfRadius D θ)) :=
    (differentiableOn_cepsCgf hW hθ hD).deriv isOpen_ball
  refine ⟨isOpen_univ, hRβ, by exact_mod_cast (cepsStepVar_pos hW hθ hD).ne', ?_, fun _ _ =>
    deriv_cepsCgf_zero hW hθ hD, ?_⟩
  · intro x hx
    have hx2 : x.2 ∈ ball (0 : ℂ) (cepsCgfRadius D θ) :=
      ball_subset_ball (by linarith) hx.2
    have := (hd1 x.2 hx2).differentiableAt (isOpen_ball.mem_nhds hx2)
    exact (this.comp x differentiableAt_snd).differentiableWithinAt
  · intro _ _ z hz
    rw [mem_ball, dist_zero_right] at hz
    have h := norm_deriv2_cepsCgf_sub_le' hW hθ hD (ζ := z) (by linarith)
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (cepsStepVar_pos hW hθ hD)]
    calc ‖deriv (deriv (cepsCgf ρW)) z - cepsStepVar ρW‖ ≤ cepsCgfC3 D θ * ‖z‖ := h
      _ ≤ cepsCgfC3 D θ * cepsCenterRadius D θ :=
          mul_le_mul_of_nonneg_left hz.le (cepsCgfC3_pos hD hθ).le
      _ ≤ cepsCgfC3 D θ * (cepsVarLo D / (2 * cepsCgfC3 D θ)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (cepsCgfC3_pos hD hθ).le
      _ = cepsVarLo D / 2 := by have := cepsCgfC3_pos hD hθ; field_simp
      _ ≤ cepsStepVar ρW / 2 := by linarith [cepsVarLo_le hW hθ hD]

theorem norm_neg_lt_center {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    ‖-μ‖ < ‖(cepsStepVar ρW : ℂ)‖ * cepsCenterRadius D θ / 2 := by
  rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (cepsStepVar_pos hW hθ hD)]
  calc ‖μ‖ < cepsChartMu D θ := hμ
    _ = cepsVarLo D * cepsChartRadius D θ / 2 := rfl
    _ ≤ cepsStepVar ρW * cepsCenterRadius D θ / 2 := by
        have h1 := cepsChartRadius_pos hD hθ
        have h2 := cepsVarLo_pos hD
        have h3 := mul_le_mul (cepsVarLo_le hW hθ hD) (cepsChartRadius_le_center hD hθ) h1.le
          (cepsStepVar_pos hW hθ hD).le
        linarith

/-- `ψ₀'(β*(μ)) = -μ`. -/
theorem deriv_cepsCgf_cepsMorseCenter {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    deriv (cepsCgf ρW) (cepsMorseCenter D θ ρW μ) = -μ := by
  rw [cepsMorseCenter]
  exact (cepsCenter_hyp hW hθ hD).apply_paramInv (mem_univ _) (norm_neg_lt_center hW hθ hD hμ)

/-- `‖β*(μ)‖ ≤ 2 ‖μ‖ / E W²`. -/
theorem norm_cepsMorseCenter_le {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    ‖cepsMorseCenter D θ ρW μ‖ ≤ 2 * ‖μ‖ / cepsStepVar ρW := by
  have := (cepsCenter_hyp hW hθ hD).norm_paramInv_le (p := 0) (mem_univ _)
    (norm_neg_lt_center hW hθ hD hμ)
  rw [cepsMorseCenter]
  rwa [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos (cepsStepVar_pos hW hθ hD)] at this

/-- `‖β*(μ)‖ < R_Θ`. -/
theorem norm_cepsMorseCenter_lt {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    ‖cepsMorseCenter D θ ρW μ‖ < cepsChartRadius D θ := by
  have h := norm_cepsMorseCenter_le hW hθ hD hμ
  have hv := cepsStepVar_pos hW hθ hD
  have hvl := cepsVarLo_le hW hθ hD
  have hvl0 := cepsVarLo_pos hD
  calc ‖cepsMorseCenter D θ ρW μ‖ ≤ 2 * ‖μ‖ / cepsStepVar ρW := h
    _ ≤ 2 * ‖μ‖ / cepsVarLo D := div_le_div_of_nonneg_left (by positivity) hvl0 hvl
    _ < 2 * cepsChartMu D θ / cepsVarLo D := by gcongr
    _ = cepsChartRadius D θ := by unfold cepsChartMu; field_simp

/-- `β*` is holomorphic in `μ`. -/
theorem differentiableOn_cepsMorseCenter :
    DifferentiableOn ℂ (cepsMorseCenter D θ ρW) (ball 0 (cepsChartMu D θ)) := by
  intro μ hμ
  rw [mem_ball, dist_zero_right] at hμ
  have h := (cepsCenter_hyp hW hθ hD).differentiableAt_paramInv (mem_univ (0 : ℂ))
    (norm_neg_lt_center hW hθ hD hμ)
  have hl : DifferentiableAt ℂ (fun μ : ℂ => ((0 : ℂ), -μ)) μ :=
    (differentiableAt_const _).prodMk differentiableAt_id.neg
  rw [cepsMorseCenter_eq]
  exact (h.comp μ hl).differentiableWithinAt

end Center

/-! ### The Hadamard quotient and the chart map `g` -/

section Chart

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `‖k(b, u) - E W²/2‖ ≤ C₃ (‖b‖ + ‖u‖)/2` for `‖b‖ + ‖u‖ < r₀/2`. -/
theorem norm_cepsMorseK_sub_le {b u : ℂ} (hbu : ‖b‖ + ‖u‖ < cepsCgfRadius D θ / 2) :
    ‖cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2‖ ≤ cepsCgfC3 D θ * (‖b‖ + ‖u‖) / 2 := by
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖b + t * u‖ ≤ ‖b‖ + ‖u‖ := by
    intro t ht
    calc ‖b + t * u‖ ≤ ‖b‖ + ‖(t : ℂ)‖ * ‖u‖ := by rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖b‖ + 1 * ‖u‖ := by
          gcongr
          rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
      _ = ‖b‖ + ‖u‖ := by ring
  have h := norm_hadamard2_sub_le (ψ := cepsCgf ρW) (U := ball 0 (cepsCgfRadius D θ))
    isOpen_ball (differentiableOn_cepsCgf hW hθ hD) (b := b) (u := u)
    (c := (cepsStepVar ρW : ℂ)) (K := cepsCgfC3 D θ * (‖b‖ + ‖u‖))
    (fun t ht => by
      rw [mem_ball, dist_zero_right]
      linarith [hseg t ht, cepsCgfRadius_pos hD hθ])
    (fun t ht => by
      have h1 := norm_deriv2_cepsCgf_sub_le' hW hθ hD (ζ := b + t * u)
        (lt_of_le_of_lt (hseg t ht) hbu)
      exact h1.trans (mul_le_mul_of_nonneg_left (hseg t ht) (cepsCgfC3_pos hD hθ).le))
  rw [cepsMorseK]
  exact h

/-- The chart region: `‖b‖ < R_Θ`, `‖u‖ < 2 R_Θ`. -/
theorem cepsMorseK_near {b u : ℂ} (hb : ‖b‖ < cepsChartRadius D θ)
    (hu : ‖u‖ < 2 * cepsChartRadius D θ) :
    ‖cepsMorseK ρW b u - (cepsStepVar ρW : ℂ) / 2‖ ≤ 3 * cepsVarLo D / 128 := by
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hbu : ‖b‖ + ‖u‖ < cepsCgfRadius D θ / 2 := by linarith
  have h := norm_cepsMorseK_sub_le hW hθ hD hbu
  have hC := cepsCgfC3_mul_chartRadius_le hD hθ
  have hc := cepsCgfC3_pos hD hθ
  calc _ ≤ cepsCgfC3 D θ * (‖b‖ + ‖u‖) / 2 := h
    _ ≤ cepsCgfC3 D θ * (3 * cepsChartRadius D θ) / 2 := by gcongr; linarith
    _ = 3 * (cepsCgfC3 D θ * cepsChartRadius D θ) / 2 := by ring
    _ ≤ 3 * (cepsVarLo D / 64) / 2 := by gcongr
    _ = 3 * cepsVarLo D / 128 := by ring

theorem cepsMorseK_re_pos {b u : ℂ} (hb : ‖b‖ < cepsChartRadius D θ)
    (hu : ‖u‖ < 2 * cepsChartRadius D θ) : 0 < (cepsMorseK ρW b u).re := by
  have h := cepsMorseK_near hW hθ hD hb hu
  have hc : (cepsStepVar ρW : ℂ) / 2 = ((cepsStepVar ρW / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hc] at h
  have hre := (abs_re_le_norm _).trans h
  rw [sub_re, ofReal_re] at hre
  have hv := cepsVarLo_le hW hθ hD
  have hv0 := cepsVarLo_pos hD
  have := neg_abs_le ((cepsMorseK ρW b u).re - cepsStepVar ρW / 2)
  linarith

theorem cepsMorseK_mem_slitPlane {b u : ℂ} (hb : ‖b‖ < cepsChartRadius D θ)
    (hu : ‖u‖ < 2 * cepsChartRadius D θ) : cepsMorseK ρW b u ∈ slitPlane :=
  Or.inl (cepsMorseK_re_pos hW hθ hD hb hu)

omit hW hθ hD in
/-- `‖√z - √c‖ ≤ ‖z - c‖/√c` for real `c > 0`. -/
theorem norm_sqrt_sub_sqrt_le {z : ℂ} {c : ℝ} (hc : 0 < c) :
    ‖Complex.sqrt z - (Real.sqrt c : ℂ)‖ ≤ ‖z - c‖ / Real.sqrt c := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  set s := Complex.sqrt z with hsdef
  have hs2 : s ^ 2 = z := by
    rw [hsdef, Complex.sqrt]; exact cpow_ofNat_inv_pow z 2
  have hre : 0 ≤ s.re := by
    rw [hsdef, Complex.sqrt, cpow_inv_two_re]; exact Real.sqrt_nonneg _
  have hprod : (s - Real.sqrt c) * (s + Real.sqrt c) = z - c := by
    have : ((Real.sqrt c : ℝ) : ℂ) ^ 2 = (c : ℂ) := by
      rw [← ofReal_pow, Real.sq_sqrt hc.le]
    linear_combination hs2 - this
  have hlow : Real.sqrt c ≤ ‖s + Real.sqrt c‖ := by
    have := re_le_norm (s + Real.sqrt c)
    rw [add_re, ofReal_re] at this
    linarith
  rw [le_div_iff₀ hs]
  calc ‖s - Real.sqrt c‖ * Real.sqrt c ≤ ‖s - Real.sqrt c‖ * ‖s + Real.sqrt c‖ :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = ‖z - c‖ := by rw [← norm_mul, hprod]

/-- The chart slope `a = √(E W²/2)`. -/
def cepsChartSlope (ρW : Measure ℝ) : ℂ := (Real.sqrt (cepsStepVar ρW / 2) : ℂ)

omit hW hθ hD in
theorem norm_cepsChartSlope : ‖cepsChartSlope ρW‖ = Real.sqrt (cepsStepVar ρW / 2) := by
  rw [cepsChartSlope, norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

theorem cepsChartSlope_ge : Real.sqrt (cepsVarLo D / 2) ≤ ‖cepsChartSlope ρW‖ := by
  rw [norm_cepsChartSlope]
  exact Real.sqrt_le_sqrt (by linarith [cepsVarLo_le hW hθ hD])

theorem cepsChartSlope_sq : (Real.sqrt (cepsStepVar ρW / 2)) ^ 2 = cepsStepVar ρW / 2 :=
  Real.sq_sqrt (by linarith [cepsStepVar_pos hW hθ hD])

/-- Joint holomorphy of `g` on `B(0, μ_c) × B(0, 2 R_Θ)`. -/
theorem differentiableOn_cepsMorseG :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseG D θ ρW x.1 x.2)
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (2 * cepsChartRadius D θ)) := by
  rintro ⟨μ, u⟩ ⟨hμ, hu⟩
  rw [mem_ball, dist_zero_right] at hμ hu
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hk : DifferentiableAt ℂ (fun x : ℂ × ℂ => hadamard2 (cepsCgf ρW) x.1 x.2)
      (cepsMorseCenter D θ ρW μ, u) := by
    have hopen : IsOpen {x : ℂ × ℂ | ‖x.1‖ + ‖x.2‖ < cepsCgfRadius D θ} :=
      isOpen_lt (by fun_prop) continuous_const
    have hmem : (cepsMorseCenter D θ ρW μ, u) ∈ {x : ℂ × ℂ | ‖x.1‖ + ‖x.2‖ < cepsCgfRadius D θ} := by
      change ‖cepsMorseCenter D θ ρW μ‖ + ‖u‖ < cepsCgfRadius D θ
      linarith
    exact (differentiableOn_hadamard2 (differentiableOn_cepsCgf hW hθ hD) _ hmem).differentiableAt
      (hopen.mem_nhds hmem)
  have hc : DifferentiableAt ℂ (cepsMorseCenter D θ ρW) μ :=
    (differentiableOn_cepsMorseCenter hW hθ hD μ (by rwa [mem_ball, dist_zero_right]))
      |>.differentiableAt (isOpen_ball.mem_nhds (by rwa [mem_ball, dist_zero_right]))
  have hc1 : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsMorseCenter D θ ρW x.1) (μ, u) :=
    DifferentiableAt.fun_comp' (f := fun x : ℂ × ℂ => x.1) (g := cepsMorseCenter D θ ρW) (μ, u)
      hc differentiableAt_fst
  have hpair : DifferentiableAt ℂ (fun x : ℂ × ℂ => ((cepsMorseCenter D θ ρW x.1, x.2) : ℂ × ℂ))
      (μ, u) := hc1.prodMk differentiableAt_snd
  have hk' : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsMorseK ρW x.1 x.2)
      (cepsMorseCenter D θ ρW μ, u) := by
    have e : (fun x : ℂ × ℂ => cepsMorseK ρW x.1 x.2) =
        fun x : ℂ × ℂ => hadamard2 (cepsCgf ρW) x.1 x.2 := by
      funext x; rw [cepsMorseK]
    rw [e]; exact hk
  have hK : DifferentiableAt ℂ (fun x : ℂ × ℂ => cepsMorseK ρW (cepsMorseCenter D θ ρW x.1) x.2)
      (μ, u) := DifferentiableAt.fun_comp' (f := fun x : ℂ × ℂ =>
        ((cepsMorseCenter D θ ρW x.1, x.2) : ℂ × ℂ))
        (g := fun x : ℂ × ℂ => cepsMorseK ρW x.1 x.2) (μ, u) hk' hpair
  have hsq : DifferentiableAt ℂ
      (fun x : ℂ × ℂ => Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW x.1) x.2)) (μ, u) :=
    DifferentiableAt.fun_comp' (g := Complex.sqrt)
      (f := fun x : ℂ × ℂ => cepsMorseK ρW (cepsMorseCenter D θ ρW x.1) x.2) (μ, u)
      (differentiableAt_sqrt (cepsMorseK_mem_slitPlane hW hθ hD hb hu)) hK
  have e : (fun x : ℂ × ℂ => cepsMorseG D θ ρW x.1 x.2) =
      fun x : ℂ × ℂ => x.2 * Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW x.1) x.2) := by
    funext x; rw [cepsMorseG]
  rw [e]
  exact (differentiableAt_snd.mul hsq).differentiableWithinAt

/-- `‖g(μ, u) - a u‖ ≤ 3 C₃ R_Θ² / ‖a‖` on `B(0, 2 R_Θ)`. -/
theorem norm_cepsMorseG_sub_le {μ u : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hu : ‖u‖ < 2 * cepsChartRadius D θ) :
    ‖cepsMorseG D θ ρW μ u - cepsChartSlope ρW * u‖ ≤
      2 * cepsChartRadius D θ * (3 * cepsVarLo D / 128) / ‖cepsChartSlope ρW‖ := by
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hv := cepsStepVar_pos hW hθ hD
  have hk := cepsMorseK_near hW hθ hD hb hu
  have hsq := norm_sqrt_sub_sqrt_le (z := cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u)
    (c := cepsStepVar ρW / 2) (by linarith)
  have ha : ‖cepsChartSlope ρW‖ = Real.sqrt (cepsStepVar ρW / 2) := norm_cepsChartSlope
  have ha0 : 0 < Real.sqrt (cepsStepVar ρW / 2) := Real.sqrt_pos.mpr (by linarith)
  have e : cepsMorseG D θ ρW μ u - cepsChartSlope ρW * u =
      u * (Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u) -
        (Real.sqrt (cepsStepVar ρW / 2) : ℂ)) := by
    rw [cepsMorseG, cepsChartSlope]; ring
  rw [e, norm_mul, ha]
  have hc : ((cepsStepVar ρW / 2 : ℝ) : ℂ) = (cepsStepVar ρW : ℂ) / 2 := by push_cast; ring
  rw [hc] at hsq
  calc ‖u‖ * ‖Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u) -
        (Real.sqrt (cepsStepVar ρW / 2) : ℂ)‖
      ≤ (2 * cepsChartRadius D θ) * ((3 * cepsVarLo D / 128) / Real.sqrt (cepsStepVar ρW / 2)) :=
        mul_le_mul hu.le (hsq.trans (div_le_div_of_nonneg_right hk ha0.le)) (norm_nonneg _)
          (by have := cepsChartRadius_pos hD hθ; positivity)
    _ = _ := by ring

theorem cepsChart_hyp :
    ParamInvHyp (ball (0 : ℂ) (cepsChartMu D θ)) (cepsMorseG D θ ρW) (cepsChartSlope ρW)
      (cepsChartRadius D θ) := by
  have hR := cepsChartRadius_pos hD hθ
  have hv := cepsStepVar_pos hW hθ hD
  have ha0 : 0 < Real.sqrt (cepsStepVar ρW / 2) := Real.sqrt_pos.mpr (by linarith)
  have ha : ‖cepsChartSlope ρW‖ = Real.sqrt (cepsStepVar ρW / 2) := norm_cepsChartSlope
  have hdiff := differentiableOn_cepsMorseG hW hθ hD
  refine ⟨isOpen_ball, hR, ?_, ?_, fun μ _ => by simp [cepsMorseG], ?_⟩
  · rw [← norm_ne_zero_iff, ha]; exact ha0.ne'
  · exact hdiff.mono (prod_mono subset_rfl (ball_subset_ball (by linarith)))
  · intro μ hμ z hz
    rw [mem_ball, dist_zero_right] at hμ
    -- `h(u) = g(μ, u) - a u` is holomorphic and small on `B(0, 2 R_Θ)`
    set h : ℂ → ℂ := fun u => cepsMorseG D θ ρW μ u - cepsChartSlope ρW * u with hh
    have hgd : ∀ u ∈ ball (0 : ℂ) (2 * cepsChartRadius D θ),
        DifferentiableAt ℂ (cepsMorseG D θ ρW μ) u := by
      intro u hu
      have h1 := (hdiff (μ, u) ⟨by rwa [mem_ball, dist_zero_right], hu⟩).differentiableAt
        ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨by rwa [mem_ball, dist_zero_right], hu⟩)
      exact h1.comp u ((differentiableAt_const μ).prodMk differentiableAt_id)
    have hhd : DifferentiableOn ℂ h (ball 0 (2 * cepsChartRadius D θ)) := fun u hu =>
      ((hgd u hu).sub ((differentiableAt_id).const_mul _)).differentiableWithinAt
    have hhb : ∀ u ∈ ball (0 : ℂ) (2 * cepsChartRadius D θ),
        ‖h u‖ ≤ 2 * cepsChartRadius D θ * (3 * cepsVarLo D / 128) / ‖cepsChartSlope ρW‖ :=
      fun u hu => norm_cepsMorseG_sub_le hW hθ hD hμ (by rwa [mem_ball, dist_zero_right] at hu)
    have hz' : z ∈ ball (0 : ℂ) (2 * cepsChartRadius D θ / 2) := by
      rwa [show 2 * cepsChartRadius D θ / 2 = cepsChartRadius D θ by ring]
    have hcauchy := norm_deriv_le_of_ball_half (by positivity) hhd hhb hz'
    have hderiv : deriv h z = deriv (cepsMorseG D θ ρW μ) z - cepsChartSlope ρW := by
      have hz2 : z ∈ ball (0 : ℂ) (2 * cepsChartRadius D θ) :=
        ball_subset_ball (by linarith) hz
      have hd : HasDerivAt h (deriv (cepsMorseG D θ ρW μ) z - cepsChartSlope ρW * 1) z :=
        (hgd z hz2).hasDerivAt.sub ((hasDerivAt_id z).const_mul (cepsChartSlope ρW))
      rw [hd.deriv, mul_one]
    rw [← hderiv]
    refine hcauchy.trans ?_
    rw [ha]
    have hC := cepsCgfC3_mul_chartRadius_le hD hθ
    have hvl := cepsVarLo_le hW hθ hD
    have hvl0 := cepsVarLo_pos hD
    have hsq : Real.sqrt (cepsStepVar ρW / 2) ^ 2 = cepsStepVar ρW / 2 :=
      cepsChartSlope_sq hW hθ hD
    have hR2 : 0 < 2 * cepsChartRadius D θ := by positivity
    rw [show 4 * (2 * cepsChartRadius D θ * (3 * cepsVarLo D / 128) /
        Real.sqrt (cepsStepVar ρW / 2)) / (2 * cepsChartRadius D θ) =
        (3 * cepsVarLo D / 32) / Real.sqrt (cepsStepVar ρW / 2) by field_simp; ring,
      div_le_iff₀ ha0]
    nlinarith

end Chart

/-! ### The chart `Θ` -/

section Root

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem cepsChartRho_lt {r : ℂ} (hr : ‖r‖ < cepsChartRho D θ) :
    ‖r‖ < ‖cepsChartSlope ρW‖ * cepsChartRadius D θ / 2 := by
  have := cepsChartSlope_ge hW hθ hD
  have hR := cepsChartRadius_pos hD hθ
  calc ‖r‖ < cepsChartRho D θ := hr
    _ = Real.sqrt (cepsVarLo D / 2) * cepsChartRadius D θ / 2 := rfl
    _ ≤ ‖cepsChartSlope ρW‖ * cepsChartRadius D θ / 2 := by gcongr

/-- `u = Θ(r, μ) - β*(μ)` lies in `B(0, R_Θ)` and solves `g(μ, u) = r`. -/
theorem cepsMorseRoot_sub_center {μ r : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖r‖ < cepsChartRho D θ) :
    cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ ∈ ball (0 : ℂ) (cepsChartRadius D θ) ∧
      cepsMorseG D θ ρW μ (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ) = r := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  have := (cepsChart_hyp hW hθ hD).paramInv_spec hμ' (cepsChartRho_lt hW hθ hD hr)
  simpa [cepsMorseRoot] using this

/-- **C-2 (3.1).** `ψ_μ(Θ(r, μ)) = m(μ) + r²`. -/
theorem cepsCgfShift_cepsMorseRoot {μ r : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖r‖ < cepsChartRho D θ) :
    cepsCgfShift ρW μ (cepsMorseRoot D θ ρW μ r) = cepsMorseMin D θ ρW μ + r ^ 2 := by
  obtain ⟨hu, hg⟩ := cepsMorseRoot_sub_center hW hθ hD hμ hr
  set b := cepsMorseCenter D θ ρW μ with hbdef
  set u := cepsMorseRoot D θ ρW μ r - b with hudef
  rw [mem_ball, dist_zero_right] at hu
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hspec := hadamard2_spec (ψ := cepsCgf ρW) isOpen_ball (differentiableOn_cepsCgf hW hθ hD)
    (b := b) (u := u) (fun t ht => by
      rw [mem_ball, dist_zero_right]
      calc ‖b + t * u‖ ≤ ‖b‖ + ‖(t : ℂ)‖ * ‖u‖ := by rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ ‖b‖ + 1 * ‖u‖ := by
            gcongr
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
        _ < cepsCgfRadius D θ := by linarith)
  have hroot : cepsMorseRoot D θ ρW μ r = b + u := by rw [hudef]; ring
  have hk2 : (Complex.sqrt (cepsMorseK ρW b u)) ^ 2 = cepsMorseK ρW b u := by
    rw [Complex.sqrt]; exact cpow_ofNat_inv_pow _ 2
  have hgsq : r ^ 2 = u ^ 2 * cepsMorseK ρW b u := by
    rw [← hg, cepsMorseG, ← hbdef, mul_pow, hk2]
  rw [hroot, cepsMorseMin, cepsCgfShift, cepsCgfShift, hspec,
    deriv_cepsCgf_cepsMorseCenter hW hθ hD hμ, hgsq, cepsMorseK]
  ring

/-- **C-2.** `Θ(0, μ) = β*(μ)`. -/
theorem cepsMorseRoot_zero {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    cepsMorseRoot D θ ρW μ 0 = cepsMorseCenter D θ ρW μ := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  rw [cepsMorseRoot, (cepsChart_hyp hW hθ hD).paramInv_zero hμ', add_zero]

/-- **C-2.** Joint holomorphy of `(μ, r) ↦ Θ(r, μ)`. -/
theorem differentiableOn_cepsMorseRoot :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2)
      (ball (0 : ℂ) (cepsChartMu D θ) ×ˢ ball (0 : ℂ) (cepsChartRho D θ)) := by
  rintro ⟨μ, r⟩ ⟨hμ, hr⟩
  rw [mem_ball, dist_zero_right] at hr
  have hμ' := hμ
  rw [mem_ball, dist_zero_right] at hμ'
  have h1 := (cepsChart_hyp hW hθ hD).differentiableAt_paramInv hμ (cepsChartRho_lt hW hθ hD hr)
  have hc : DifferentiableAt ℂ (cepsMorseCenter D θ ρW) μ :=
    (differentiableOn_cepsMorseCenter hW hθ hD μ hμ).differentiableAt (isOpen_ball.mem_nhds hμ)
  have e : (fun x : ℂ × ℂ => cepsMorseRoot D θ ρW x.1 x.2) = fun x : ℂ × ℂ =>
      cepsMorseCenter D θ ρW x.1 + paramInv (cepsMorseG D θ ρW) (cepsChartRadius D θ) x.1 x.2 := by
    funext x; rw [cepsMorseRoot]
  rw [e]
  exact ((DifferentiableAt.fun_comp' (f := fun x : ℂ × ℂ => x.1) (g := cepsMorseCenter D θ ρW)
    (μ, r) hc differentiableAt_fst).add h1).differentiableWithinAt

/-- `∂_u g(μ, 0) = √(ψ₀''(β*)/2)`. -/
theorem hasDerivAt_cepsMorseG_zero {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    HasDerivAt (cepsMorseG D θ ρW μ)
      (Complex.sqrt (deriv (deriv (cepsCgf ρW)) (cepsMorseCenter D θ ρW μ) / 2)) 0 := by
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_pos hD hθ
  have hu0 : ‖(0 : ℂ)‖ < 2 * cepsChartRadius D θ := by simp; positivity
  have hdiff := differentiableOn_cepsMorseG hW hθ hD
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  have hu0' : (0 : ℂ) ∈ ball (0 : ℂ) (2 * cepsChartRadius D θ) := mem_ball_self (by positivity)
  -- the square-root factor is continuous at `0`
  have hK : ContinuousAt (fun u => Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u)) 0 := by
    have hopen : IsOpen {x : ℂ × ℂ | ‖x.1‖ + ‖x.2‖ < cepsCgfRadius D θ} :=
      isOpen_lt (by fun_prop) continuous_const
    have hr0 := cepsCgfRadius_pos hD hθ
    have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
    have hmem : (cepsMorseCenter D θ ρW μ, (0 : ℂ)) ∈
        {x : ℂ × ℂ | ‖x.1‖ + ‖x.2‖ < cepsCgfRadius D θ} := by
      change ‖cepsMorseCenter D θ ρW μ‖ + ‖(0 : ℂ)‖ < cepsCgfRadius D θ
      simp; linarith
    have hk := (differentiableOn_hadamard2 (differentiableOn_cepsCgf hW hθ hD) _
      hmem).differentiableAt (hopen.mem_nhds hmem)
    have hk1 : ContinuousAt (fun u => cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u) 0 := by
      rw [cepsMorseK_eq]
      exact (DifferentiableAt.fun_comp' (f := fun u : ℂ => ((cepsMorseCenter D θ ρW μ, u) : ℂ × ℂ))
        (g := fun x : ℂ × ℂ => hadamard2 (cepsCgf ρW) x.1 x.2) (0 : ℂ) hk
        ((differentiableAt_const _).prodMk differentiableAt_id)).continuousAt
    exact (continuousAt_sqrt (Or.inl (cepsMorseK_re_pos hW hθ hD hb hu0).le)).comp hk1
  -- `g(μ, u) = u · s(u)` with `s` continuous at `0`, so `g'(0) = s(0)`
  have hs0 : Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW μ) 0) =
      Complex.sqrt (deriv (deriv (cepsCgf ρW)) (cepsMorseCenter D θ ρW μ) / 2) := by
    rw [cepsMorseK, hadamard2_zero]
  rw [← hs0]
  rw [hasDerivAt_iff_tendsto_slope]
  have : ∀ u ∈ ({0}ᶜ : Set ℂ), slope (cepsMorseG D θ ρW μ) 0 u =
      Complex.sqrt (cepsMorseK ρW (cepsMorseCenter D θ ρW μ) u) := by
    intro u hu
    rw [slope_def_field, cepsMorseG, cepsMorseG, zero_mul, sub_zero, sub_zero]
    field_simp [show u ≠ 0 from hu]
  refine (tendsto_congr' ?_).mpr (hK.tendsto.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact this u hu

/-- **C-2 (3.1).** `∂_r Θ(0, μ) = √(2/ψ₀''(β*(μ)))`. -/
theorem hasDerivAt_cepsMorseRoot_zero {μ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ) :
    HasDerivAt (cepsMorseRoot D θ ρW μ)
      (Complex.sqrt (2 / deriv (deriv (cepsCgf ρW)) (cepsMorseCenter D θ ρW μ))) 0 := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  have hyp := cepsChart_hyp hW hθ hD
  have h0 : ‖(0 : ℂ)‖ < ‖cepsChartSlope ρW‖ * cepsChartRadius D θ / 2 :=
    cepsChartRho_lt hW hθ hD (by simpa using cepsChartRho_pos hD hθ)
  have hinv := hyp.hasDerivAt_paramInv hμ' h0
  rw [hyp.paramInv_zero hμ', (hasDerivAt_cepsMorseG_zero hW hθ hD hμ).deriv] at hinv
  have hsum := hinv.const_add (cepsMorseCenter D θ ρW μ)
  -- `(√(x/2))⁻¹ = √(2/x)` for `Re x > 0`
  set x := deriv (deriv (cepsCgf ρW)) (cepsMorseCenter D θ ρW μ) with hx
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_pos hD hθ
  have hk := cepsMorseK_re_pos hW hθ hD (u := 0) hb (by simp; positivity)
  rw [cepsMorseK, hadamard2_zero, ← hx] at hk
  have harg : (x / 2).arg ≠ Real.pi := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    linarith [this.1]
  have e : (Complex.sqrt (x / 2))⁻¹ = Complex.sqrt (2 / x) := by
    rw [Complex.sqrt, Complex.sqrt, ← Complex.inv_cpow _ _ harg, inv_div]
  rw [e] at hsum
  rw [cepsMorseRoot_eq]
  exact hsum

/-- **C-2.** The chart is injective: `Θ(r₁, μ) = Θ(r₂, μ)` forces `r₁ = r₂`. -/
theorem cepsMorseRoot_injective {μ r₁ r₂ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (h₁ : ‖r₁‖ < cepsChartRho D θ) (h₂ : ‖r₂‖ < cepsChartRho D θ)
    (he : cepsMorseRoot D θ ρW μ r₁ = cepsMorseRoot D θ ρW μ r₂) : r₁ = r₂ := by
  have e1 := (cepsMorseRoot_sub_center hW hθ hD hμ h₁).2
  have e2 := (cepsMorseRoot_sub_center hW hθ hD hμ h₂).2
  rw [he] at e1
  exact e1.symm.trans e2

/-- **C-2.** Two-sided Lipschitz bounds of the chart. -/
theorem norm_cepsMorseRoot_sub_le {μ r₁ r₂ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (h₁ : ‖r₁‖ < cepsChartRho D θ) (h₂ : ‖r₂‖ < cepsChartRho D θ) :
    ‖cepsMorseRoot D θ ρW μ r₁ - cepsMorseRoot D θ ρW μ r₂‖ ≤
      2 / ‖cepsChartSlope ρW‖ * ‖r₁ - r₂‖ := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  obtain ⟨hu₁, e1⟩ := cepsMorseRoot_sub_center hW hθ hD hμ h₁
  obtain ⟨hu₂, e2⟩ := cepsMorseRoot_sub_center hW hθ hD hμ h₂
  have := (cepsChart_hyp hW hθ hD).norm_sub_le hμ' hu₁ hu₂
  rw [e1, e2] at this
  calc ‖cepsMorseRoot D θ ρW μ r₁ - cepsMorseRoot D θ ρW μ r₂‖
      = ‖(cepsMorseRoot D θ ρW μ r₁ - cepsMorseCenter D θ ρW μ) -
          (cepsMorseRoot D θ ρW μ r₂ - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
    _ ≤ _ := this

theorem norm_sub_le_cepsMorseRoot_sub {μ r₁ r₂ : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (h₁ : ‖r₁‖ < cepsChartRho D θ) (h₂ : ‖r₂‖ < cepsChartRho D θ) :
    ‖r₁ - r₂‖ ≤ 3 * ‖cepsChartSlope ρW‖ / 2 *
      ‖cepsMorseRoot D θ ρW μ r₁ - cepsMorseRoot D θ ρW μ r₂‖ := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  obtain ⟨hu₁, e1⟩ := cepsMorseRoot_sub_center hW hθ hD hμ h₁
  obtain ⟨hu₂, e2⟩ := cepsMorseRoot_sub_center hW hθ hD hμ h₂
  have := (cepsChart_hyp hW hθ hD).norm_apply_sub_le hμ' hu₁ hu₂
  rw [e1, e2] at this
  calc ‖r₁ - r₂‖ ≤ _ := this
    _ = 3 * ‖cepsChartSlope ρW‖ / 2 *
      ‖cepsMorseRoot D θ ρW μ r₁ - cepsMorseRoot D θ ρW μ r₂‖ := by ring_nf

/-- **C-2.** Every solution of `ψ_μ(ζ) = q` near `β*` is `Θ(±r)` for any `r` with
`r² = q - m(μ)`: precisely, if `‖ζ - β*(μ)‖ < R_Θ/3`, `‖r‖ < r₁` and `r² = ψ_μ(ζ) - m(μ)`, then
`ζ = Θ(r, μ)` or `ζ = Θ(-r, μ)`. -/
theorem eq_cepsMorseRoot_or {μ ζ r : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hζ : ‖ζ - cepsMorseCenter D θ ρW μ‖ < cepsChartRadius D θ / 3)
    (hr : ‖r‖ < cepsChartRho D θ)
    (hq : r ^ 2 = cepsCgfShift ρW μ ζ - cepsMorseMin D θ ρW μ) :
    ζ = cepsMorseRoot D θ ρW μ r ∨ ζ = cepsMorseRoot D θ ρW μ (-r) := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  have hyp := cepsChart_hyp hW hθ hD
  set b := cepsMorseCenter D θ ρW μ with hbdef
  set u := ζ - b with hudef
  have hR := cepsChartRadius_pos hD hθ
  have hu : u ∈ ball (0 : ℂ) (cepsChartRadius D θ) := by
    rw [mem_ball, dist_zero_right]; linarith
  -- `g(μ, u)² = ψ_μ(ζ) - m(μ) = r²`
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hspec := hadamard2_spec (ψ := cepsCgf ρW) isOpen_ball (differentiableOn_cepsCgf hW hθ hD)
    (b := b) (u := u) (fun t ht => by
      rw [mem_ball, dist_zero_right]
      rw [mem_ball, dist_zero_right] at hu
      calc ‖b + t * u‖ ≤ ‖b‖ + ‖(t : ℂ)‖ * ‖u‖ := by rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ ‖b‖ + 1 * ‖u‖ := by
            gcongr
            rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; exact ht.2
        _ < cepsCgfRadius D θ := by linarith)
  have hk2 : (Complex.sqrt (cepsMorseK ρW b u)) ^ 2 = cepsMorseK ρW b u := by
    rw [Complex.sqrt]; exact cpow_ofNat_inv_pow _ 2
  have hgsq : (cepsMorseG D θ ρW μ u) ^ 2 = r ^ 2 := by
    rw [hq, cepsMorseG, ← hbdef, mul_pow, hk2, cepsMorseMin, cepsCgfShift, cepsCgfShift,
      show ζ = b + u by rw [hudef]; ring, hspec, deriv_cepsCgf_cepsMorseCenter hW hθ hD hμ,
      cepsMorseK]
    ring
  have hg := sq_eq_sq_iff_eq_or_eq_neg.mp hgsq
  have hroot : ∀ s : ℂ, ‖s‖ < cepsChartRho D θ → cepsMorseG D θ ρW μ u = s →
      ζ = cepsMorseRoot D θ ρW μ s := by
    intro s hs hgs
    have := hyp.paramInv_eq hμ' hu hgs
    rw [cepsMorseRoot, this, hudef]; ring
  rcases hg with h | h
  · exact Or.inl (hroot r hr h)
  · exact Or.inr (hroot (-r) (by rwa [norm_neg]) h)

/-- **C-2 corollary.** `ψ_μ'(Θ(ρ)) ∂_ρ Θ(ρ) = 2 ρ`. -/
theorem deriv_cepsCgfShift_mul_deriv_cepsMorseRoot {μ r : ℂ} (hμ : ‖μ‖ < cepsChartMu D θ)
    (hr : ‖r‖ < cepsChartRho D θ) :
    deriv (cepsCgfShift ρW μ) (cepsMorseRoot D θ ρW μ r) *
      deriv (cepsMorseRoot D θ ρW μ) r = 2 * r := by
  have hμ' : μ ∈ ball (0 : ℂ) (cepsChartMu D θ) := by rwa [mem_ball, dist_zero_right]
  have hr' : r ∈ ball (0 : ℂ) (cepsChartRho D θ) := by rwa [mem_ball, dist_zero_right]
  -- differentiability of `Θ(·, μ)` at `r`
  have hΘ : DifferentiableAt ℂ (cepsMorseRoot D θ ρW μ) r := by
    have h := (differentiableOn_cepsMorseRoot hW hθ hD (μ, r) ⟨hμ', hr'⟩).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμ', hr'⟩)
    exact h.comp r ((differentiableAt_const μ).prodMk differentiableAt_id)
  -- differentiability of `ψ_μ` at `Θ(r)`
  obtain ⟨hu, -⟩ := cepsMorseRoot_sub_center hW hθ hD hμ hr
  rw [mem_ball, dist_zero_right] at hu
  have hb := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hmem : cepsMorseRoot D θ ρW μ r ∈ ball (0 : ℂ) (cepsCgfRadius D θ) := by
    rw [mem_ball, dist_zero_right]
    calc ‖cepsMorseRoot D θ ρW μ r‖ = ‖cepsMorseCenter D θ ρW μ +
          (cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
      _ < cepsCgfRadius D θ := by linarith
  have hψ : DifferentiableAt ℂ (cepsCgfShift ρW μ) (cepsMorseRoot D θ ρW μ r) := by
    have := (differentiableOn_cepsCgf hW hθ hD _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
    exact this.add (differentiableAt_id.const_mul μ)
  -- differentiate `ψ_μ(Θ(s)) = m + s²` on a neighbourhood of `r`
  have heq : (fun s => cepsCgfShift ρW μ (cepsMorseRoot D θ ρW μ s)) =ᶠ[𝓝 r]
      fun s => cepsMorseMin D θ ρW μ + s ^ 2 := by
    filter_upwards [isOpen_ball.mem_nhds hr'] with s hs
    rw [mem_ball, dist_zero_right] at hs
    exact cepsCgfShift_cepsMorseRoot hW hθ hD hμ hs
  have h1 := hψ.hasDerivAt.comp r hΘ.hasDerivAt
  have h2 : HasDerivAt (fun s => cepsMorseMin D θ ρW μ + s ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add (cepsMorseMin D θ ρW μ))
  have h1' : HasDerivAt (fun s => cepsMorseMin D θ ρW μ + s ^ 2)
      (deriv (cepsCgfShift ρW μ) (cepsMorseRoot D θ ρW μ r) *
        deriv (cepsMorseRoot D θ ρW μ) r) r := h1.congr_of_eventuallyEq heq.symm
  exact h1'.unique h2

end Root

end PGM
