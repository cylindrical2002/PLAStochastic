import PLAStochastic.Index.CEPS.Canonical.Domain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# CEPS WP3, lemma C-1: the three zones of a vertical line

Fix a domain `dom : CepsCanonDomain D θ v` and parameters `‖μ‖ ≤ μ₀` (complex), `‖q‖ ≤ q₀`.
Write `A(ζ) = e^{-q} e^{μ ζ} M₀(ζ)` (`cepsA`), so `d = 1 - A`.

* Roots (`CepsCanonDomain.norm_cepsRootR_le`, `…norm_rootPlus_le`, `…norm_rootMinus_le`):
  `‖r₊‖ ≤ rmax` and `‖β±‖ ≤ c₀/4`.
* Zone A, `‖ζ‖ ≤ ρA`: `d = -D₀ · Q_A` with `Q_A = H φ₁(Φ)` (`cepsQuotA`, `φ₁(x) = (eˣ - 1)/x`),
  and `‖Q_A - E W²/2‖ ≤ v₋/16` (`CepsCanonDomain.cepsD_eq_zoneA`, `…norm_cepsQuotA_sub_le`).
* Zone B, `ρA ≤ ‖ζ‖`, `|Im ζ| ≤ ρB`, `|Re ζ| ≤ 2 c₀`: `Re Φ ≤ -v₋ ρA²/16`, hence `‖A‖ ≤ 1 - g`.
* Zone C, `|Im ζ| ≥ ρB/2`, `|Re ζ| ≤ 2c₀`, `|Im μ| |Im ζ| ≤ η`: `‖A‖ ≤ 1 - gF/2 ≤ 1 - g`
  (class Fourier gap plus the horizontal shift bound).
* The rational factor `R = (ζ² - γ²)/D₀` for `‖ζ‖ ≥ ρA`, `|Re ζ| ≤ 2 c₀`, real `γ ∈ [1/2, 1]`:
  `Re R ≥ 1/2`, `|Im R| ≤ (34 c₀/ρA) Re R`, `‖R‖ ≤ 4/ρA²`, `‖R - 1‖ ≤ 3/(ρA ‖ζ‖)`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `A(ζ) = e^{-q} e^{μ ζ} M₀(ζ)`; `d = 1 - A`. -/
def cepsA (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ := cexp (-q) * cexp (μ * ζ) * stepTransform ρW ζ

theorem cepsD_eq_one_sub_cepsA (ρW : Measure ℝ) (μ q ζ : ℂ) :
    cepsD ρW μ q ζ = 1 - cepsA ρW μ q ζ := rfl

/-- `Q_A = H · φ₁(Φ)` with `φ₁ = dslope exp 0`. -/
def cepsQuotA (D θ : ℝ) (ρW : Measure ℝ) (μ q ζ : ℂ) : ℂ :=
  cepsRootQuot D θ ρW μ q ζ * dslope cexp 0 (cepsRootEq ρW μ q ζ)

/-- `R = (ζ² - γ²)/D₀`. -/
def cepsRatR (D θ : ℝ) (ρW : Measure ℝ) (γ μ q ζ : ℂ) : ℂ :=
  (ζ ^ 2 - γ ^ 2) / cepsQuad D θ ρW μ q ζ

theorem cepsF_eq_mul_ratR (D θ : ℝ) (ρW : Measure ℝ) (γ μ q ζ : ℂ) :
    cepsF D θ ρW γ μ q ζ = cepsD ρW μ q ζ * cepsRatR D θ ρW γ μ q ζ := by
  rw [cepsF, cepsRatR, mul_div_assoc]

theorem exp_sub_one_eq_mul_dslope (x : ℂ) : cexp x - 1 = x * dslope cexp 0 x := by
  have := sub_smul_dslope cexp 0 x
  rw [sub_zero, smul_eq_mul, Complex.exp_zero] at this
  exact this.symm

theorem norm_dslope_exp_sub_one_le {x : ℂ} (hx : ‖x‖ ≤ 1) : ‖dslope cexp 0 x - 1‖ ≤ ‖x‖ := by
  by_cases h0 : x = 0
  · subst h0; rw [dslope_same, Complex.deriv_exp, Complex.exp_zero]; simp
  · rw [dslope_of_ne _ h0, slope_def_field, sub_zero, Complex.exp_zero]
    have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr h0
    have h := Complex.norm_exp_sub_one_sub_id_le hx
    rw [show (cexp x - 1) / x - 1 = (cexp x - 1 - x) / x by field_simp, norm_div,
      div_le_iff₀ hx0]
    nlinarith

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

theorem μ_lt_chart {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) : ‖μ‖ < cepsChartMu D θ := by
  have := dom.μ₀_chart; have := dom.μ₀_pos; linarith

section Basic

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem v_pos : 0 < v := lt_of_lt_of_le (cepsStepVar_pos hW hθ hD) (cepsStepVar_le hW)

theorem varLo_le_v : cepsVarLo D ≤ v := (cepsVarLo_le hW hθ hD).trans (cepsStepVar_le hW)


include dom in
theorem norm_center_le {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) :
    ‖cepsMorseCenter D θ ρW μ‖ ≤ dom.c₀ / 8 := by
  have h := norm_cepsMorseCenter_le hW hθ hD (dom.μ_lt_chart hμ)
  have hvW := cepsVarLo_le hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hc := dom.μ₀_c₀
  calc ‖cepsMorseCenter D θ ρW μ‖ ≤ 2 * ‖μ‖ / cepsStepVar ρW := h
    _ ≤ 2 * dom.μ₀ / cepsVarLo D := by
        apply div_le_div₀ (by linarith [dom.μ₀_pos]) (by linarith) hvl hvW
    _ ≤ dom.c₀ / 8 := by rw [div_le_div_iff₀ hvl (by norm_num)]; linarith

include dom in
theorem norm_cepsRootR_le {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootR D θ ρW μ q‖ ≤ dom.rmax := by
  have hμc := dom.μ_lt_chart hμ
  have hm := norm_cepsMorseMin_le hW hθ hD hμc
  have hb := norm_cepsMorseCenter_le hW hθ hD hμc
  have hvW := cepsVarLo_le hW hθ hD
  have hvl := cepsVarLo_pos hD
  have hv := v_pos hW hθ hD
  have hr := dom.rmax_pos
  have hsq := norm_cepsRootR_sq D θ ρW μ q
  -- `‖β*‖ ≤ rmax/(2(v+1))`
  have hb' : ‖cepsMorseCenter D θ ρW μ‖ ≤ dom.rmax / (2 * (v + 1)) := by
    calc ‖cepsMorseCenter D θ ρW μ‖ ≤ 2 * ‖μ‖ / cepsStepVar ρW := hb
      _ ≤ 2 * dom.μ₀ / cepsVarLo D := div_le_div₀ (by linarith [dom.μ₀_pos]) (by linarith) hvl hvW
      _ ≤ dom.rmax / (2 * (v + 1)) := by
          rw [div_le_div_iff₀ hvl (by positivity)]; nlinarith [dom.μ₀_r]
  have hbn := norm_nonneg (cepsMorseCenter D θ ρW μ)
  have h1 : ‖q - cepsMorseMin D θ ρW μ‖ ≤ dom.rmax ^ 2 := by
    calc ‖q - cepsMorseMin D θ ρW μ‖ ≤ ‖q‖ + ‖cepsMorseMin D θ ρW μ‖ := norm_sub_le _ _
      _ ≤ dom.rmax ^ 2 / 2 + v * (dom.rmax / (2 * (v + 1))) ^ 2 := by
          rw [← dom.q₀_def]
          exact add_le_add hq (hm.trans (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ hbn hb' 2) hv.le))
      _ ≤ dom.rmax ^ 2 := by
          have : v * (dom.rmax / (2 * (v + 1))) ^ 2 ≤ dom.rmax ^ 2 / 4 := by
            rw [div_pow, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [sq_nonneg dom.rmax, sq_nonneg v]
          nlinarith [sq_nonneg dom.rmax]
  rw [← hsq] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hr.le (by norm_num)).mp h1

include dom in
theorem norm_cepsRootR_lt {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ := by
  have := dom.norm_cepsRootR_le hW hθ hD hμ hq
  have := dom.rmax_r1; have := dom.rmax_pos; linarith

include dom in
theorem norm_rootPlus_le {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootPlus D θ ρW μ q‖ ≤ dom.c₀ / 4 := by
  have h1 := norm_rootPlus_sub_center_le hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq)
  have h2 := dom.norm_center_le hW hθ hD hμ
  have h3 := dom.norm_cepsRootR_le hW hθ hD hμ hq
  have hK := cepsChartK_pos hD
  have h4 := dom.rmax_c₀
  have : cepsChartK D * ‖cepsRootR D θ ρW μ q‖ ≤ dom.c₀ / 8 := by nlinarith
  calc ‖cepsRootPlus D θ ρW μ q‖ = ‖cepsMorseCenter D θ ρW μ +
        (cepsRootPlus D θ ρW μ q - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ dom.c₀ / 4 := by linarith

include dom in
theorem norm_rootMinus_le {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    ‖cepsRootMinus D θ ρW μ q‖ ≤ dom.c₀ / 4 := by
  have h1 := norm_rootMinus_sub_center_le hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq)
  have h2 := dom.norm_center_le hW hθ hD hμ
  have h3 := dom.norm_cepsRootR_le hW hθ hD hμ hq
  have hK := cepsChartK_pos hD
  have h4 := dom.rmax_c₀
  have : cepsChartK D * ‖cepsRootR D θ ρW μ q‖ ≤ dom.c₀ / 8 := by nlinarith
  calc ‖cepsRootMinus D θ ρW μ q‖ = ‖cepsMorseCenter D θ ρW μ +
        (cepsRootMinus D θ ρW μ q - cepsMorseCenter D θ ρW μ)‖ := by ring_nf
    _ ≤ _ := norm_add_le _ _
    _ ≤ dom.c₀ / 4 := by linarith

end Basic

/-! ### Zone A -/

section ZoneA

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `‖H - E W²/2‖ ≤ v₋/64` on `closedBall 0 (2 ρA)`. -/
theorem norm_quot_sub_le {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ 2 * dom.ρA) :
    ‖cepsRootQuot D θ ρW μ q ζ - (cepsStepVar ρW : ℂ) / 2‖ ≤ cepsVarLo D / 64 := by
  have hρA := dom.ρA_pos
  have hr := dom.norm_cepsRootR_le hW hθ hD hμ hq
  have hb := dom.norm_center_le hW hθ hD hμ
  have hc := dom.c₀_le
  have hK := cepsChartK_pos hD
  have hv := v_pos hW hθ hD
  have hC3 := cepsCgfC3_pos hD hθ
  have hrn := norm_nonneg (cepsRootR D θ ρW μ q)
  have hKr : cepsChartK D * ‖cepsRootR D θ ρW μ q‖ ≤ 2 * dom.ρA / 4 := by
    have := dom.rmax_c₀; have := dom.c₀_pos; nlinarith
  have h := norm_cepsRootQuot_sub_le hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq) (ρH := 2 * dom.ρA) (by positivity)
    (by linarith [dom.ρA_R]) (by linarith [dom.c₀_pos]) hKr hζ
  refine h.trans ?_
  set r := ‖cepsRootR D θ ρW μ q‖
  have t1 : 5 * cepsCgfC3 D θ * (2 * dom.ρA) ≤ cepsVarLo D / 192 := by
    have := dom.ρA_C3; linarith
  have t2 : 4 * r ^ 2 / (2 * dom.ρA) ^ 2 ≤ cepsVarLo D / 192 := by
    have hrr : r ≤ dom.ρA := hr.trans dom.rmax_A1'
    have h192 := dom.rmax_A1
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : r ^ 2 ≤ dom.rmax * dom.ρA := by nlinarith
    nlinarith
  have t3 : 6 * v * cepsChartK D * r / (2 * dom.ρA) ≤ cepsVarLo D / 192 := by
    have h576 := dom.rmax_A2
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : v * cepsChartK D * r ≤ v * cepsChartK D * dom.rmax :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    nlinarith
  linarith

/-- `‖Φ‖ ≤ 4 v ρA² + rmax²` on `closedBall 0 ρA`. -/
theorem norm_rootEq_le {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.ρA) :
    ‖cepsRootEq ρW μ q ζ‖ ≤ 4 * v * dom.ρA ^ 2 + dom.rmax ^ 2 := by
  have hμc := dom.μ_lt_chart hμ
  have hb := dom.norm_center_le hW hθ hD hμ
  have hc := dom.c₀_le
  have hρA := dom.ρA_pos
  have hR := dom.ρA_R
  have hRl := cepsChartRadius_le_r0 (D := D) (θ := θ)
  set b := cepsMorseCenter D θ ρW μ
  set u := ζ - b with hu
  have hun : ‖u‖ ≤ 2 * dom.ρA := by
    calc ‖u‖ ≤ ‖ζ‖ + ‖b‖ := norm_sub_le _ _
      _ ≤ 2 * dom.ρA := by linarith [dom.c₀_pos]
  have hspec := cepsCgfShift_center_add hW hθ hD hμc (u := u) (by linarith)
  rw [show b + u = ζ by rw [hu]; ring] at hspec
  have hk := norm_cepsMorseK_le hW hθ hD (b := b) (u := u)
    (by linarith [dom.c₀_pos]) (by linarith)
  have hr := dom.norm_cepsRootR_le hW hθ hD hμ hq
  have e : cepsRootEq ρW μ q ζ = u ^ 2 * cepsMorseK ρW b u - cepsRootR D θ ρW μ q ^ 2 := by
    rw [cepsRootEq, hspec, cepsRootR_sq]; ring
  rw [e]
  have hv := v_pos hW hθ hD
  calc ‖u ^ 2 * cepsMorseK ρW b u - cepsRootR D θ ρW μ q ^ 2‖
      ≤ ‖u‖ ^ 2 * ‖cepsMorseK ρW b u‖ + ‖cepsRootR D θ ρW μ q‖ ^ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_pow, norm_pow]
    _ ≤ (2 * dom.ρA) ^ 2 * v + dom.rmax ^ 2 := by
        gcongr
    _ = 4 * v * dom.ρA ^ 2 + dom.rmax ^ 2 := by ring

theorem norm_rootEq_le_half {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ dom.ρA) : ‖cepsRootEq ρW μ q ζ‖ ≤ 1 / 2 := by
  have h := dom.norm_rootEq_le hW hθ hD hμ hq hζ
  have hv := v_pos hW hθ hD
  have hvl := varLo_le_v hW hθ hD
  have h144 := dom.ρA_v
  have h64 := dom.rmax_A3
  have hρ := dom.ρA_pos
  have hρ1 := dom.ρA_one
  have hr := dom.rmax_pos
  have hr1 := dom.rmax_one
  -- `144 v ρA ≤ 1` and `64 rmax ≤ 1`
  have a1 : 144 * v * dom.ρA ≤ 1 := by
    have : 144 * v ^ 2 * dom.ρA ≤ v := h144.trans hvl
    nlinarith
  have a2 : 64 * dom.rmax ≤ 1 := by nlinarith
  nlinarith

/-- `d = 1 - e^{Φ}` where `ψ₀` is defined. -/
theorem cepsD_eq_one_sub_exp {μ q ζ : ℂ} (hζ : ‖ζ‖ < cepsCgfRadius D θ) :
    cepsD ρW μ q ζ = 1 - cexp (cepsRootEq ρW μ q ζ) := by
  have hM := stepTransform_mem_slitPlane hW hθ hD hζ.le
  have hM0 : stepTransform ρW ζ ≠ 0 := slitPlane_ne_zero hM
  rw [cepsD, cepsRootEq, cepsCgfShift, cepsCgf,
    show Complex.log (stepTransform ρW ζ) + μ * ζ - q =
      -q + μ * ζ + Complex.log (stepTransform ρW ζ) by ring,
    Complex.exp_add, Complex.exp_add, Complex.exp_log hM0]

/-- **Zone A factorization.** `d = -D₀ · Q_A` on `closedBall 0 ρA`. -/
theorem cepsD_eq_zoneA {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ dom.ρA) :
    cepsD ρW μ q ζ = -(cepsQuad D θ ρW μ q ζ * cepsQuotA D θ ρW μ q ζ) := by
  have hρ := dom.ρA_pos
  have hr0 : ‖ζ‖ < cepsCgfRadius D θ := by
    have := dom.ρA_R; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
    have := cepsCgfRadius_pos hD hθ; linarith
  rw [cepsD_eq_one_sub_exp hW hθ hD hr0]
  have h1 := exp_sub_one_eq_mul_dslope (cepsRootEq ρW μ q ζ)
  have h2 := cepsRootEq_eq_quad_mul hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq) ζ
  rw [cepsQuotA]
  linear_combination -h1 - h2 * dslope cexp 0 (cepsRootEq ρW μ q ζ)

/-- `‖Q_A - E W²/2‖ ≤ v₋/16` on `closedBall 0 ρA`. -/
theorem norm_cepsQuotA_sub_le {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ dom.ρA) :
    ‖cepsQuotA D θ ρW μ q ζ - (cepsStepVar ρW : ℂ) / 2‖ ≤ cepsVarLo D / 16 := by
  have hρ := dom.ρA_pos
  have hH := dom.norm_quot_sub_le hW hθ hD hμ hq (ζ := ζ) (by linarith)
  have hΦ := dom.norm_rootEq_le hW hθ hD hμ hq hζ
  have hΦ2 := dom.norm_rootEq_le_half hW hθ hD hμ hq hζ
  have hφ := norm_dslope_exp_sub_one_le (x := cepsRootEq ρW μ q ζ) (by linarith)
  have hv := v_pos hW hθ hD
  have hvl := varLo_le_v hW hθ hD
  have hvl0 := cepsVarLo_pos hD
  have hvW := cepsStepVar_pos hW hθ hD
  have hvW2 : ‖(cepsStepVar ρW : ℂ) / 2‖ ≤ v / 2 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hvW]; simp
    linarith [cepsStepVar_le hW]
  set H := cepsRootQuot D θ ρW μ q ζ
  set φ := dslope cexp 0 (cepsRootEq ρW μ q ζ)
  set c := (cepsStepVar ρW : ℂ) / 2
  have e : cepsQuotA D θ ρW μ q ζ - c = (H - c) * φ + c * (φ - 1) := by
    rw [cepsQuotA]; ring
  have hφn : ‖φ‖ ≤ 3 / 2 := by
    calc ‖φ‖ = ‖(φ - 1) + 1‖ := by ring_nf
      _ ≤ ‖φ - 1‖ + 1 := by simpa using norm_add_le (φ - 1) 1
      _ ≤ 3 / 2 := by linarith
  -- `(v/2) ‖Φ‖ ≤ v₋/72 + v₋/128`
  have hvΦ : v / 2 * ‖cepsRootEq ρW μ q ζ‖ ≤ cepsVarLo D / 72 + cepsVarLo D / 128 := by
    have h144 := dom.ρA_v
    have h64 := dom.rmax_A3
    have hρ1 := dom.ρA_one
    have hr1 := dom.rmax_one
    have hr := dom.rmax_pos
    have b1 : v / 2 * (4 * v * dom.ρA ^ 2) ≤ cepsVarLo D / 72 := by
      have : dom.ρA ^ 2 ≤ dom.ρA := by nlinarith
      nlinarith
    have b2 : v / 2 * dom.rmax ^ 2 ≤ cepsVarLo D / 128 := by
      have : dom.rmax ^ 2 ≤ dom.rmax := by nlinarith
      nlinarith
    calc v / 2 * ‖cepsRootEq ρW μ q ζ‖ ≤ v / 2 * (4 * v * dom.ρA ^ 2 + dom.rmax ^ 2) := by gcongr
      _ ≤ _ := by linarith
  rw [e]
  calc ‖(H - c) * φ + c * (φ - 1)‖ ≤ ‖H - c‖ * ‖φ‖ + ‖c‖ * ‖φ - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
    _ ≤ cepsVarLo D / 64 * (3 / 2) + v / 2 * ‖cepsRootEq ρW μ q ζ‖ := by
        gcongr
    _ ≤ cepsVarLo D / 16 := by linarith

/-- **Zone A form of `F`.** Off the roots, `F = Q_A (γ² - ζ²)`. -/
theorem cepsF_eq_zoneA {γ μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ dom.ρA) (hne : cepsQuad D θ ρW μ q ζ ≠ 0) :
    cepsF D θ ρW γ μ q ζ = cepsQuotA D θ ρW μ q ζ * (γ ^ 2 - ζ ^ 2) := by
  rw [cepsF, dom.cepsD_eq_zoneA hW hθ hD hμ hq hζ]
  field_simp
  ring

end ZoneA

/-! ### Zones B and C -/

section ZoneBC

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- **Zone B.** `‖A(ζ)‖ ≤ 1 - g` for `ρA ≤ ‖ζ‖`, `|Im ζ| ≤ ρB`, `|Re ζ| ≤ 2 c₀`. -/
theorem norm_cepsA_zoneB {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (h1 : dom.ρA ≤ ‖ζ‖) (h2 : |ζ.im| ≤ dom.ρB) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖cepsA ρW μ q ζ‖ ≤ 1 - dom.g := by
  have hρA := dom.ρA_pos
  have hc := dom.c₀_le
  have hc0 := dom.c₀_pos
  have hAB := dom.ρA_ρB
  have hr0 := cepsCgfRadius_pos hD hθ
  have hB0 := dom.ρB_r0
  have hBC := dom.ρB_C3
  have hC3 := cepsCgfC3_pos hD hθ
  have hvW := cepsVarLo_le hW hθ hD
  have hvl := cepsVarLo_pos hD
  -- `‖ζ‖ ≤ 2 ρB`
  have hζB' : ‖ζ‖ < 2 * dom.ρB := by
    calc ‖ζ‖ ≤ |ζ.re| + |ζ.im| := norm_le_abs_re_add_abs_im ζ
      _ < 2 * dom.ρB := by linarith
  have hζB : ‖ζ‖ ≤ 2 * dom.ρB := hζB'.le
  have hζr : ‖ζ‖ < cepsCgfRadius D θ / 2 := by linarith
  -- `ψ₀(ζ) = ζ² k(0, ζ)`
  have hψ := hadamard2_spec (ψ := cepsCgf ρW) isOpen_ball (differentiableOn_cepsCgf hW hθ hD)
    (b := 0) (u := ζ) (fun t ht => by
      rw [mem_ball, dist_zero_right, zero_add]
      calc ‖(t : ℂ) * ζ‖ = |t| * ‖ζ‖ := by rw [norm_mul, norm_real, Real.norm_eq_abs]
        _ ≤ 1 * ‖ζ‖ := by gcongr; rw [abs_of_nonneg ht.1]; exact ht.2
        _ < cepsCgfRadius D θ := by linarith)
  rw [zero_add, cepsCgf_zero hW, deriv_cepsCgf_zero hW hθ hD, zero_mul, add_zero, zero_add] at hψ
  set k := hadamard2 (cepsCgf ρW) 0 ζ with hkdef
  have hk : ‖k - (cepsStepVar ρW : ℂ) / 2‖ ≤ cepsVarLo D / 32 := by
    have h := norm_cepsMorseK_sub_le hW hθ hD (b := 0) (u := ζ) (by simpa using hζr)
    rw [cepsMorseK] at h
    calc _ ≤ cepsCgfC3 D θ * (‖(0 : ℂ)‖ + ‖ζ‖) / 2 := h
      _ ≤ cepsCgfC3 D θ * (2 * dom.ρB) / 2 := by simp only [norm_zero, zero_add]; gcongr
      _ ≤ cepsVarLo D / 32 := by nlinarith
  have hkre : cepsStepVar ρW / 2 - cepsVarLo D / 32 ≤ k.re := by
    have := (abs_re_le_norm _).trans hk
    rw [sub_re, show ((cepsStepVar ρW : ℂ) / 2).re = cepsStepVar ρW / 2 by simp] at this
    linarith [neg_abs_le (k.re - cepsStepVar ρW / 2)]
  have hkim : |k.im| ≤ cepsVarLo D / 32 := by
    have := (abs_im_le_norm _).trans hk
    rwa [sub_im, show ((cepsStepVar ρW : ℂ) / 2).im = 0 by simp, sub_zero] at this
  -- `Re(ζ² k) ≤ -E W² ‖ζ‖²/8`
  have hs2 : ‖ζ‖ ^ 2 = ζ.re ^ 2 + ζ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hre2 : ζ.re ^ 2 ≤ ‖ζ‖ ^ 2 / 4 := by
    have : |ζ.re| ≤ ‖ζ‖ / 2 := by linarith
    have h0 : 0 ≤ |ζ.re| := abs_nonneg _
    nlinarith [sq_abs ζ.re]
  have hsq_re : (ζ ^ 2).re = ζ.re ^ 2 - ζ.im ^ 2 := by rw [sq, mul_re]; ring
  have hsq_im : |(ζ ^ 2).im| ≤ ‖ζ‖ ^ 2 := by
    rw [sq, mul_im, hs2, abs_le]
    constructor <;> nlinarith [sq_nonneg (ζ.re + ζ.im), sq_nonneg (ζ.re - ζ.im)]
  set n := ‖ζ‖ ^ 2 with hn
  have hn0 : 0 ≤ n := sq_nonneg _
  have hmain : (ζ ^ 2 * k).re ≤ -(cepsStepVar ρW * n / 8) := by
    rw [mul_re, hsq_re]
    have hneg : ζ.re ^ 2 - ζ.im ^ 2 ≤ -(n / 2) := by linarith
    have hkpos : 0 ≤ k.re := by linarith
    have e1 : (ζ.re ^ 2 - ζ.im ^ 2) * k.re ≤ -(n / 2) * k.re :=
      mul_le_mul_of_nonneg_right hneg hkpos
    have e3 : -(n / 2) * k.re ≤ -(n / 2) * (cepsStepVar ρW / 2 - cepsVarLo D / 32) :=
      mul_le_mul_of_nonpos_left hkre (by linarith)
    have e2 : -((ζ ^ 2).im * k.im) ≤ n * (cepsVarLo D / 32) := by
      have : |(ζ ^ 2).im * k.im| ≤ n * (cepsVarLo D / 32) := by
        rw [abs_mul]; exact mul_le_mul hsq_im hkim (abs_nonneg _) hn0
      linarith [neg_abs_le ((ζ ^ 2).im * k.im)]
    have e4 : n * cepsVarLo D ≤ n * cepsStepVar ρW := mul_le_mul_of_nonneg_left hvW hn0
    have e5 : 0 ≤ n * cepsStepVar ρW := mul_nonneg hn0 (by linarith)
    linarith
  -- `Re Φ ≤ -v₋ ρA²/16`
  have hΦ : (cepsRootEq ρW μ q ζ).re ≤ -(cepsVarLo D * dom.ρA ^ 2 / 16) := by
    rw [cepsRootEq, cepsCgfShift, hψ]
    simp only [sub_re, add_re]
    have hμs : (μ * ζ).re ≤ dom.μ₀ * (2 * dom.ρB) := by
      calc (μ * ζ).re ≤ ‖μ * ζ‖ := re_le_norm _
        _ = ‖μ‖ * ‖ζ‖ := norm_mul _ _
        _ ≤ dom.μ₀ * (2 * dom.ρB) := mul_le_mul hμ hζB (norm_nonneg _) dom.μ₀_pos.le
    have hqre : -q.re ≤ dom.q₀ := by
      have := neg_abs_le q.re; have := abs_re_le_norm q; linarith
    have hq₀ : dom.q₀ ≤ cepsVarLo D * dom.ρA ^ 2 / 32 := by
      rw [dom.q₀_def]
      have hrB := dom.rmax_B
      have hrA := dom.rmax_A1'
      have hr := dom.rmax_pos
      have : dom.rmax * dom.rmax ≤ (cepsVarLo D * dom.ρA / 16) * dom.ρA :=
        mul_le_mul (by linarith) hrA hr.le (by positivity)
      nlinarith
    have hμ₀ : dom.μ₀ * (2 * dom.ρB) ≤ cepsVarLo D * dom.ρA ^ 2 / 32 := by
      have := dom.μ₀_B; linarith
    have hρ2 : dom.ρA ^ 2 ≤ n := pow_le_pow_left₀ hρA.le h1 2
    have : cepsVarLo D * dom.ρA ^ 2 ≤ cepsStepVar ρW * n :=
      mul_le_mul hvW hρ2 (sq_nonneg _) (by linarith)
    linarith
  -- conclude
  have hr0' : ‖ζ‖ < cepsCgfRadius D θ := by linarith
  have hA : cepsA ρW μ q ζ = cexp (cepsRootEq ρW μ q ζ) := by
    have := cepsD_eq_one_sub_exp hW hθ hD (μ := μ) (q := q) hr0'
    rw [cepsD_eq_one_sub_cepsA] at this
    linear_combination -this
  rw [hA, Complex.norm_exp]
  calc Real.exp (cepsRootEq ρW μ q ζ).re ≤ Real.exp (-(cepsVarLo D * dom.ρA ^ 2 / 16)) :=
        Real.exp_le_exp.mpr hΦ
    _ ≤ 1 - dom.g := by linarith [dom.g_B]

omit hW hθ hD in
/-- `e^{x} ≤ 1 + 2 x` for `0 ≤ x ≤ 1`. -/
theorem exp_le_one_add_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have := Real.abs_exp_sub_one_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  rw [abs_of_nonneg h0] at this
  linarith [le_abs_self (Real.exp x - 1)]

omit hW hθ hD in
/-- `‖e^{-q} e^{μ ζ}‖ ≤ e^{q₀ + 2 μ₀ c₀ + η}` under admissibility. -/
theorem norm_exp_factor_le {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖cexp (-q) * cexp (μ * ζ)‖ ≤ Real.exp (dom.q₀ + 2 * dom.μ₀ * dom.c₀ + dom.η) := by
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [neg_re, mul_re]
  have hq' : -q.re ≤ dom.q₀ := by
    have := neg_abs_le q.re; have := abs_re_le_norm q; linarith
  have hr : μ.re * ζ.re ≤ dom.μ₀ * (2 * dom.c₀) := by
    calc μ.re * ζ.re ≤ |μ.re * ζ.re| := le_abs_self _
      _ = |μ.re| * |ζ.re| := abs_mul _ _
      _ ≤ dom.μ₀ * (2 * dom.c₀) :=
          mul_le_mul ((abs_re_le_norm μ).trans hμ) h3 (abs_nonneg _) dom.μ₀_pos.le
  have hi : -(μ.im * ζ.im) ≤ dom.η := by
    have := neg_abs_le (μ.im * ζ.im); rw [abs_mul] at this; linarith
  linarith

/-- **Zone C.** `‖A(ζ)‖ ≤ 1 - g` for `|Im ζ| ≥ ρB/2`, `|Re ζ| ≤ 2 c₀`, admissible `μ`. -/
theorem norm_cepsA_zoneC {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀) (h2 : dom.ρB / 2 ≤ |ζ.im|) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖cepsA ρW μ q ζ‖ ≤ 1 - dom.g := by
  have hgap := norm_stepTransform_I_le hW hθ hD (Y := dom.ρB / 2) (y := ζ.im)
    (by linarith [dom.ρB_pos]) h2
  have hc := dom.c₀_le
  have hc0 := dom.c₀_pos
  have hρA := dom.ρA_pos
  have hcθ : |ζ.re| ≤ θ / 2 := by
    have := dom.ρA_R; have := cepsChartRadius_le_r0 (D := D) (θ := θ)
    have := cepsCgfRadius_le (D := D) (θ := θ); linarith
  have hshift := norm_stepTransform_shift_le hW hθ hD.le hcθ ζ.im
  have hζ : (ζ.re : ℂ) + ζ.im * I = ζ := re_add_im ζ
  rw [hζ] at hshift
  have hW' := cepsShiftConst_pos hD hθ
  have hM : ‖stepTransform ρW ζ‖ ≤ 1 - 3 * dom.gF / 4 := by
    have h1 : ‖stepTransform ρW ζ‖ ≤ ‖stepTransform ρW (ζ.im * I)‖ + |ζ.re| * cepsShiftConst D θ := by
      calc ‖stepTransform ρW ζ‖ = ‖(stepTransform ρW ζ - stepTransform ρW (ζ.im * I)) +
            stepTransform ρW (ζ.im * I)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
        _ ≤ _ := by linarith
    have h2 : |ζ.re| * cepsShiftConst D θ ≤ dom.gF / 4 := by
      have := dom.c₀_W
      calc |ζ.re| * cepsShiftConst D θ ≤ 2 * dom.c₀ * cepsShiftConst D θ := by gcongr
        _ ≤ dom.gF / 4 := by linarith
    have := dom.gF_gap
    linarith
  have hE := dom.norm_exp_factor_le hμ hμη hq h3
  set x := dom.q₀ + 2 * dom.μ₀ * dom.c₀ + dom.η with hx
  have hx0 : 0 ≤ x := by
    have := dom.q₀_pos; have := dom.μ₀_pos; have := dom.η_pos; positivity
  have hx1 : x ≤ dom.gF / 8 := by
    have hq0 : dom.q₀ ≤ dom.gF / 32 := by
      rw [dom.q₀_def]
      have := dom.rmax_C; have := dom.rmax_one; have := dom.rmax_pos; nlinarith
    have hm0 : 2 * dom.μ₀ * dom.c₀ ≤ dom.gF / 32 := by
      have := dom.μ₀_C; have := dom.μ₀_pos
      have hc1 : dom.c₀ ≤ 1 := by linarith [dom.ρA_one]
      nlinarith
    have := dom.η_le
    linarith
  have hgF := dom.gF_le
  have hgF0 := dom.gF_pos
  have hexp : Real.exp x ≤ 1 + 2 * x := exp_le_one_add_two_mul hx0 (by linarith)
  rw [cepsA, mul_assoc] at *
  calc ‖cexp (-q) * (cexp (μ * ζ) * stepTransform ρW ζ)‖
      = ‖cexp (-q) * cexp (μ * ζ)‖ * ‖stepTransform ρW ζ‖ := by rw [← mul_assoc, norm_mul]
    _ ≤ Real.exp x * (1 - 3 * dom.gF / 4) := by
        gcongr
    _ ≤ (1 + 2 * x) * (1 - 3 * dom.gF / 4) := by
        gcongr; linarith
    _ ≤ 1 - dom.gF / 2 := by nlinarith
    _ ≤ 1 - dom.g := by linarith [dom.g_gF]

/-- Off zone A on a near-imaginary strip, `‖A‖ ≤ 1 - g`. -/
theorem norm_cepsA_offA {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀) (h1 : dom.ρA ≤ ‖ζ‖) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖cepsA ρW μ q ζ‖ ≤ 1 - dom.g := by
  rcases le_total |ζ.im| dom.ρB with h | h
  · exact dom.norm_cepsA_zoneB hW hθ hD hμ hq h1 h h3
  · exact dom.norm_cepsA_zoneC hW hθ hD hμ hμη hq (by linarith [dom.ρB_pos]) h3

omit hW hθ hD in
/-- `‖A(ζ)‖ ≤ 3 ‖M₀(ζ)‖` off zone A. -/
theorem norm_cepsA_le_three_mul {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖cepsA ρW μ q ζ‖ ≤ 3 * ‖stepTransform ρW ζ‖ := by
  have hE := dom.norm_exp_factor_le hμ hμη hq h3
  have hx1 : dom.q₀ + 2 * dom.μ₀ * dom.c₀ + dom.η ≤ 1 := by
    have hq0 : dom.q₀ ≤ 1 / 2 := by
      rw [dom.q₀_def]; have := dom.rmax_one; have := dom.rmax_pos; nlinarith
    have := dom.μ₀_C; have := dom.η_le; have := dom.gF_le; have := dom.μ₀_pos
    have hc1 : dom.c₀ ≤ 1 / 1000 := by linarith [dom.c₀_le, dom.ρA_one]
    nlinarith
  have he : Real.exp (dom.q₀ + 2 * dom.μ₀ * dom.c₀ + dom.η) ≤ 3 := by
    calc Real.exp (dom.q₀ + 2 * dom.μ₀ * dom.c₀ + dom.η) ≤ Real.exp 1 := Real.exp_le_exp.mpr hx1
      _ ≤ 3 := Real.exp_one_lt_three.le
  rw [cepsA, norm_mul]
  exact mul_le_mul_of_nonneg_right (hE.trans he) (norm_nonneg _)

end ZoneBC

/-! ### The rational factor `R` -/

section Rational

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

omit hW hθ hD in
/-- `D₀(ζ) = ζ² (1 - β₊/ζ)(1 - β₋/ζ)`. -/
theorem cepsQuad_eq {μ q ζ : ℂ} (hζ : ζ ≠ 0) :
    cepsQuad D θ ρW μ q ζ =
      ζ ^ 2 * ((1 - cepsRootPlus D θ ρW μ q / ζ) * (1 - cepsRootMinus D θ ρW μ q / ζ)) := by
  rw [cepsQuad]; field_simp

/-- Estimates for `w = 1/((1 - β₊/ζ)(1 - β₋/ζ))`: `‖w - 1‖ ≤ c₀/‖ζ‖` and `‖w‖ ≤ 2`. -/
theorem norm_w_sub_one_le {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (h1 : dom.ρA ≤ ‖ζ‖) :
    ‖((1 - cepsRootPlus D θ ρW μ q / ζ) * (1 - cepsRootMinus D θ ρW μ q / ζ))⁻¹ - 1‖ ≤
      dom.c₀ / ‖ζ‖ ∧
      ‖((1 - cepsRootPlus D θ ρW μ q / ζ) * (1 - cepsRootMinus D θ ρW μ q / ζ))⁻¹‖ ≤ 2 := by
  have hρA := dom.ρA_pos
  have hc := dom.c₀_le
  have hc0 := dom.c₀_pos
  have hζ0 : 0 < ‖ζ‖ := lt_of_lt_of_le hρA h1
  have hp := dom.norm_rootPlus_le hW hθ hD hμ hq
  have hm := dom.norm_rootMinus_le hW hθ hD hμ hq
  set ε := dom.c₀ / (4 * ‖ζ‖) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hεs : ε ≤ 1 / 4000 := by
    rw [hε, div_le_iff₀ (by positivity)]
    have : dom.c₀ ≤ dom.ρA / 1000 := hc
    nlinarith
  have ha : ‖cepsRootPlus D θ ρW μ q / ζ‖ ≤ ε := by
    rw [norm_div, hε, div_le_div_iff₀ hζ0 (by positivity)]; nlinarith
  have hb : ‖cepsRootMinus D θ ρW μ q / ζ‖ ≤ ε := by
    rw [norm_div, hε, div_le_div_iff₀ hζ0 (by positivity)]; nlinarith
  set a := cepsRootPlus D θ ρW μ q / ζ
  set b := cepsRootMinus D θ ρW μ q / ζ
  set z := (1 - a) * (1 - b) with hz
  have hz1 : ‖z - 1‖ ≤ 3 * ε := by
    have e : z - 1 = -a - b + a * b := by rw [hz]; ring
    rw [e]
    calc ‖-a - b + a * b‖ ≤ ‖a‖ + ‖b‖ + ‖a‖ * ‖b‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
          gcongr
          refine (norm_sub_le _ _).trans ?_
          rw [norm_neg]
      _ ≤ ε + ε + ε * ε := by gcongr
      _ ≤ 3 * ε := by nlinarith
  have hzn : 1 / 2 ≤ ‖z‖ := by
    have := norm_sub_norm_le 1 (1 - z)
    rw [show (1 : ℂ) - (1 - z) = z by ring, norm_one] at this
    have h' : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    linarith
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hzn; linarith
  have hzn' : 1 - 3 * ε ≤ ‖z‖ := by
    have := norm_sub_norm_le 1 (1 - z)
    rw [show (1 : ℂ) - (1 - z) = z by ring, norm_one] at this
    have h' : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    linarith
  constructor
  · have e : z⁻¹ - 1 = (1 - z) / z := by field_simp
    rw [e, norm_div, norm_sub_rev]
    rw [div_le_iff₀ (by linarith)]
    calc ‖z - 1‖ ≤ 3 * ε := hz1
      _ ≤ dom.c₀ / ‖ζ‖ * (1 - 3 * ε) := by
          rw [hε]
          have hk : dom.c₀ / ‖ζ‖ = 4 * (dom.c₀ / (4 * ‖ζ‖)) := by field_simp
          rw [hk]
          nlinarith
      _ ≤ dom.c₀ / ‖ζ‖ * ‖z‖ := by gcongr
  · rw [norm_inv]
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith

/-- **The rational factor.** For `ρA ≤ ‖ζ‖`, `|Re ζ| ≤ 2 c₀`, real `γ ∈ [1/2, 1]`:
`Re R ≥ 1/2`, `|Im R| ≤ (34 c₀/ρA) Re R`, `‖R‖ ≤ 4/ρA²`, `‖R - 1‖ ≤ 3/(ρA ‖ζ‖)`. -/
theorem cepsRatR_bounds {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) (h1 : dom.ρA ≤ ‖ζ‖) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    1 / 2 ≤ (cepsRatR D θ ρW γ μ q ζ).re ∧
      |(cepsRatR D θ ρW γ μ q ζ).im| ≤ 34 * dom.c₀ / dom.ρA * (cepsRatR D θ ρW γ μ q ζ).re ∧
      ‖cepsRatR D θ ρW γ μ q ζ‖ ≤ 4 / dom.ρA ^ 2 ∧
      ‖cepsRatR D θ ρW γ μ q ζ - 1‖ ≤ 3 / (dom.ρA * ‖ζ‖) := by
  have hρA := dom.ρA_pos
  have hc := dom.c₀_le
  have hc0 := dom.c₀_pos
  have hρ1 := dom.ρA_one
  have hζ0 : 0 < ‖ζ‖ := lt_of_lt_of_le hρA h1
  have hζne : ζ ≠ 0 := norm_pos_iff.mp hζ0
  obtain ⟨hw1, hw2⟩ := dom.norm_w_sub_one_le hW hθ hD hμ hq h1
  set w := ((1 - cepsRootPlus D θ ρW μ q / ζ) * (1 - cepsRootMinus D θ ρW μ q / ζ))⁻¹ with hwdef
  set t : ℂ := -((γ : ℂ) ^ 2) / ζ ^ 2 with htdef
  set N : ℂ := 1 + t with hN
  have hR : cepsRatR D θ ρW γ μ q ζ = N * w := by
    rw [cepsRatR, cepsQuad_eq hζne, hwdef, hN, htdef]
    have hf : (1 - cepsRootPlus D θ ρW μ q / ζ) * (1 - cepsRootMinus D θ ρW μ q / ζ) ≠ 0 := by
      intro h0
      have hw0 : w = 0 := by rw [hwdef, h0, inv_zero]
      rw [hw0, zero_sub, norm_neg, norm_one] at hw1
      have : dom.c₀ / ‖ζ‖ < 1 := by
        rw [div_lt_one hζ0]; linarith
      linarith
    field_simp
    ring
  -- components of `t`
  set c := ζ.re; set y := ζ.im
  have hs2 : ‖ζ‖ ^ 2 = c ^ 2 + y ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hnsq : Complex.normSq (ζ ^ 2) = ‖ζ‖ ^ 4 := by
    rw [Complex.normSq_eq_norm_sq, norm_pow]; ring
  have hns0 : 0 < Complex.normSq (ζ ^ 2) := by rw [hnsq]; positivity
  have hsre : (ζ ^ 2).re = c ^ 2 - y ^ 2 := by rw [sq, mul_re]; ring
  have hsim : (ζ ^ 2).im = 2 * c * y := by rw [sq, mul_im]; ring
  have hγ2re : ((γ : ℂ) ^ 2).re = γ ^ 2 := by rw [← ofReal_pow, ofReal_re]
  have hγ2im : ((γ : ℂ) ^ 2).im = 0 := by rw [← ofReal_pow, ofReal_im]
  have htre : t.re = γ ^ 2 * (y ^ 2 - c ^ 2) / ‖ζ‖ ^ 4 := by
    rw [htdef, div_re, neg_re, neg_im, hγ2re, hγ2im, hsre, hsim, hnsq]; ring
  have htim : t.im = 2 * γ ^ 2 * c * y / ‖ζ‖ ^ 4 := by
    rw [htdef, div_im, neg_re, neg_im, hγ2re, hγ2im, hsre, hsim, hnsq]; ring
  have hc2 : c ^ 2 ≤ ‖ζ‖ ^ 2 / 4 := by
    have : |c| ≤ ‖ζ‖ / 2 := by linarith
    nlinarith [sq_abs c, abs_nonneg c]
  have hyc : ‖ζ‖ ^ 2 / 2 ≤ y ^ 2 - c ^ 2 := by linarith
  have hγ0 : 0 < γ := by linarith
  have hζ4 : 0 < ‖ζ‖ ^ 4 := by positivity
  have htre0 : 0 ≤ t.re := by rw [htre]; apply div_nonneg _ hζ4.le; nlinarith
  set κ := 8 * dom.c₀ / dom.ρA with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκs : κ ≤ 8 / 1000 := by
    rw [hκ, div_le_iff₀ hρA]; linarith
  have htim_le : |t.im| ≤ κ * t.re := by
    rw [htim, htre, abs_div, abs_of_pos hζ4, mul_div_assoc', div_le_div_iff_of_pos_right hζ4]
    -- `2 γ² |c| |y| ≤ κ γ² (y² - c²)`
    have hy : |y| ≤ ‖ζ‖ := abs_im_le_norm ζ
    have hcabs : |c| ≤ 2 * dom.c₀ := h3
    have h4 : 2 * |c| * |y| ≤ 4 * dom.c₀ * ‖ζ‖ := by
      have := mul_le_mul hcabs hy (abs_nonneg _) (by linarith)
      linarith
    have h5 : 4 * dom.c₀ * ‖ζ‖ ≤ κ * (‖ζ‖ ^ 2 / 2) := by
      rw [hκ]
      have : dom.c₀ * ‖ζ‖ * dom.ρA ≤ dom.c₀ * ‖ζ‖ * ‖ζ‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      rw [div_mul_eq_mul_div, le_div_iff₀ hρA]; nlinarith
    have habs : |2 * γ ^ 2 * c * y| = 2 * γ ^ 2 * (|c| * |y|) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (by positivity : 0 < γ ^ 2)]; ring
    rw [habs]
    have hγsq : 0 < γ ^ 2 := by positivity
    have key : 2 * (|c| * |y|) ≤ κ * (y ^ 2 - c ^ 2) := by
      have : κ * (‖ζ‖ ^ 2 / 2) ≤ κ * (y ^ 2 - c ^ 2) := mul_le_mul_of_nonneg_left hyc hκ0
      linarith
    have key2 := mul_le_mul_of_nonneg_left key hγsq.le
    linarith
  -- `Re N ≥ 1`, `|Im N| ≤ κ Re N`
  have hNre : N.re = 1 + t.re := by rw [hN, add_re, one_re]
  have hNim : N.im = t.im := by rw [hN, add_im, one_im, zero_add]
  have hNre1 : 1 ≤ N.re := by rw [hNre]; linarith
  have hNim_le : |N.im| ≤ κ * N.re := by
    rw [hNim, hNre]
    exact htim_le.trans (mul_le_mul_of_nonneg_left (by linarith) hκ0)
  -- `‖t‖ = γ²/‖ζ‖²`
  have htn : ‖t‖ ≤ 1 / ‖ζ‖ ^ 2 := by
    rw [htdef, norm_div, norm_neg, norm_pow, norm_pow, norm_real, Real.norm_eq_abs,
      abs_of_pos hγ0]
    gcongr
    calc γ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hγ0.le hγ2 2
      _ = 1 := one_pow 2
  have hNn : ‖N‖ ≤ 2 / dom.ρA ^ 2 := by
    have : 1 / ‖ζ‖ ^ 2 ≤ 1 / dom.ρA ^ 2 := by gcongr
    have h1' : 1 ≤ 1 / dom.ρA ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      calc dom.ρA ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ hρA.le hρ1 2
        _ = 1 := one_pow 2
    calc ‖N‖ ≤ ‖(1 : ℂ)‖ + ‖t‖ := by rw [hN]; exact norm_add_le _ _
      _ = 1 + ‖t‖ := by rw [norm_one]
      _ ≤ 2 / dom.ρA ^ 2 := by
          have : 2 / dom.ρA ^ 2 = 1 / dom.ρA ^ 2 + 1 / dom.ρA ^ 2 := by ring
          linarith
  -- `δ = ‖w - 1‖ ≤ c₀/ρA`
  set δ := ‖w - 1‖ with hδ
  have hδ1 : δ ≤ dom.c₀ / dom.ρA :=
    hw1.trans (div_le_div_of_nonneg_left hc0.le hρA h1)
  have hδs : δ ≤ 1 / 1000 := by
    refine hδ1.trans ?_; rw [div_le_iff₀ hρA]; linarith
  have hwre : |w.re - 1| ≤ δ := by
    have := abs_re_le_norm (w - 1); rwa [sub_re, one_re] at this
  have hwim : |w.im| ≤ δ := by
    have := abs_im_le_norm (w - 1); rwa [sub_im, one_im, sub_zero] at this
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hRre : (N * w).re = N.re * w.re - N.im * w.im := mul_re _ _
  have hRim : (N * w).im = N.re * w.im + N.im * w.re := mul_im _ _
  have hRre_ge : N.re / 2 ≤ (N * w).re := by
    rw [hRre]
    have e1 : N.re * (1 - δ) ≤ N.re * w.re := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith [neg_abs_le (w.re - 1)]
    have e2 : N.im * w.im ≤ κ * N.re * δ := by
      calc N.im * w.im ≤ |N.im * w.im| := le_abs_self _
        _ = |N.im| * |w.im| := abs_mul _ _
        _ ≤ (κ * N.re) * δ := mul_le_mul hNim_le hwim (abs_nonneg _) (by positivity)
    have hN0 : 0 ≤ N.re := by linarith
    have e3 : N.re * δ ≤ N.re * (1 / 1000) := mul_le_mul_of_nonneg_left hδs hN0
    have e4 : κ * N.re * δ ≤ (8 / 1000 * N.re) * (1 / 1000) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hκs hN0) hδs hδ0 (by positivity)
    linarith
  have hRim_le : |(N * w).im| ≤ (δ + 2 * κ) * N.re := by
    rw [hRim]
    calc |N.re * w.im + N.im * w.re| ≤ |N.re * w.im| + |N.im * w.re| := abs_add_le _ _
      _ = N.re * |w.im| + |N.im| * |w.re| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : 0 < N.re)]
      _ ≤ N.re * δ + (κ * N.re) * 2 := by
          have hwre2 : |w.re| ≤ 2 := by
            have := abs_sub_abs_le_abs_sub w.re 1
            rw [abs_one] at this; linarith
          exact add_le_add (mul_le_mul_of_nonneg_left hwim (by linarith))
            (mul_le_mul hNim_le hwre2 (abs_nonneg _) (by positivity))
      _ = (δ + 2 * κ) * N.re := by ring
  rw [hR]
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · calc |(N * w).im| ≤ (δ + 2 * κ) * N.re := hRim_le
      _ ≤ (δ + 2 * κ) * (2 * (N * w).re) := by gcongr; linarith
      _ = 2 * (δ + 2 * κ) * (N * w).re := by ring
      _ ≤ 34 * dom.c₀ / dom.ρA * (N * w).re := by
          refine mul_le_mul_of_nonneg_right ?_ (by linarith)
          have e8 : 8 * dom.c₀ / dom.ρA = 8 * (dom.c₀ / dom.ρA) := by ring
          have e34 : 34 * dom.c₀ / dom.ρA = 34 * (dom.c₀ / dom.ρA) := by ring
          rw [hκ, e8, e34]
          linarith
  · rw [norm_mul]
    calc ‖N‖ * ‖w‖ ≤ (2 / dom.ρA ^ 2) * 2 := mul_le_mul hNn hw2 (norm_nonneg _) (by positivity)
      _ = 4 / dom.ρA ^ 2 := by ring
  · have e : N * w - 1 = t * w + (w - 1) := by rw [hN]; ring
    rw [e]
    calc ‖t * w + (w - 1)‖ ≤ ‖t‖ * ‖w‖ + ‖w - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ 1 / ‖ζ‖ ^ 2 * 2 + dom.c₀ / ‖ζ‖ := by gcongr
      _ ≤ 3 / (dom.ρA * ‖ζ‖) := by
          have a1 : 1 / ‖ζ‖ ^ 2 * 2 ≤ 2 / (dom.ρA * ‖ζ‖) := by
            rw [div_mul_eq_mul_div, one_mul, sq]
            exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_right h1 hζ0.le)
          have a2 : dom.c₀ / ‖ζ‖ ≤ 1 / (dom.ρA * ‖ζ‖) := by
            have hc1 : dom.c₀ * dom.ρA ≤ 1 := by
              have : dom.c₀ ≤ 1 := by linarith
              calc dom.c₀ * dom.ρA ≤ 1 * 1 := mul_le_mul this hρ1 hρA.le zero_le_one
                _ = 1 := one_mul 1
            rw [show dom.c₀ / ‖ζ‖ = (dom.c₀ * dom.ρA) / (dom.ρA * ‖ζ‖) by field_simp]
            exact div_le_div_of_nonneg_right hc1 (by positivity)
          have : 3 / (dom.ρA * ‖ζ‖) = 2 / (dom.ρA * ‖ζ‖) + 1 / (dom.ρA * ‖ζ‖) := by ring
          linarith

end Rational

end CepsCanonDomain

end PGM
