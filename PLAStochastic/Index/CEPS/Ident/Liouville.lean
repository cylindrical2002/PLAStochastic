import PLAStochastic.Index.CEPS.Ident.LineFactor
import Mathlib.Analysis.Complex.Liouville

/-!
# CEPS WP4, lemma C-5 for `Re q > 0`: identification by Liouville's theorem

Fix real `|μ| ≤ μ₀` and `Re q > 0`, `‖q‖ ≤ q₀`. With `A±` the ladder transforms of `Y = W + μ`,
`L₂ = L^{(2c₀)}` (abscissa `2c₀`), `Ψ = (2π)⁻¹ lineCauchy φ_{c₀} c₀` (the Cauchy integral on the line
`c₀` evaluated to its right) and `P = (1 - A₊) e^{-L₂}`:

* left piece `E_L = -dslope P β₊ = P/(β₊ - ζ)` on `Re ζ < 2c₀` (`P(β₊) = 0` because `Re β₊ > 0`
  forces `1 - A₋(β₊) ≠ 0`);
* right piece `E_R = (ζ - β₋) e^{-Ψ}/((1 - A₋)(1 + ζ))` on `Re ζ > c₀`;
* on the overlap `c₀ < Re ζ < 2c₀` the two agree by Plemelj (`L₂ - Ψ = log F - log(1 - ζ)`)
  and W-3;
* the glued function is entire and bounded, and tends to `1` along the negative real axis.

Hence `E ≡ 1`, i.e. `1 - A₊(ζ) = (β₊ - ζ) e^{L(ζ)}` (`one_sub_asc_eq_of_re_pos`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology Bornology
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

/-- `P(ζ) = (1 - A₊(ζ)) e^{-L₂(ζ)}`. -/
def identP (ρW : Measure ℝ) (μ : ℝ) (q ζ : ℂ) : ℂ :=
  (1 - ascTransform (driftStep ρW μ) (cexp (-q)) ζ) *
    cexp (-cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ)

/-- The right Cauchy integral `Ψ(ζ) = (2π)⁻¹ ∫ log F(c₀ + i y)/(c₀ + i y - ζ) dy`. -/
def identΨ (ρW : Measure ℝ) (μ : ℝ) (q ζ : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * lineCauchy (cepsLogFLine D θ ρW dom.c₀ μ q) dom.c₀ ζ

/-- The left Cauchy integral `Φ₂(ζ)` on the line `2c₀`. -/
def identΦ (ρW : Measure ℝ) (μ : ℝ) (q ζ : ℂ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * lineCauchy (cepsLogFLine D θ ρW (2 * dom.c₀) μ q) (2 * dom.c₀) ζ

def identEL (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) : ℂ → ℂ :=
  fun ζ => -dslope (dom.identP ρW μ q) (cepsRootPlus D θ ρW μ q) ζ

def identER (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) : ℂ → ℂ :=
  fun ζ => (ζ - cepsRootMinus D θ ρW μ q) * cexp (-dom.identΨ ρW μ q ζ) /
    ((1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ) * (1 + ζ))

def identE (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) : ℂ → ℂ :=
  fun ζ => if ζ.re < 2 * dom.c₀ then dom.identEL ρW μ q ζ else dom.identER ρW μ q ζ

theorem c₀_le_small : dom.c₀ ≤ 1 / 1000 := by
  have := dom.c₀_le; have := dom.ρA_one; linarith

theorem canonL₂_eq (ρW : Measure ℝ) (μ : ℝ) (q ζ : ℂ) :
    cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ =
      dom.identΦ ρW μ q ζ - Complex.log (((1 : ℝ) : ℂ) - ζ) := rfl

theorem one_sub_mem_slitPlane {ζ : ℂ} (hζ : ζ.re < 2 * dom.c₀) :
    ((1 : ℝ) : ℂ) - ζ ∈ slitPlane := by
  left; simp; linarith [dom.c₀_le_small]

theorem cexp_neg_canonL₂ (ρW : Measure ℝ) (μ : ℝ) (q : ℂ) {ζ : ℂ} (hζ : ζ.re < 2 * dom.c₀) :
    cexp (-cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ) =
      cexp (-dom.identΦ ρW μ q ζ) * (((1 : ℝ) : ℂ) - ζ) := by
  rw [dom.canonL₂_eq, neg_sub, sub_eq_add_neg, Complex.exp_add,
    Complex.exp_log (slitPlane_ne_zero (dom.one_sub_mem_slitPlane hζ)), mul_comm]

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

variable {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 < q.re) (hq : ‖q‖ ≤ dom.q₀)
include hμ hq0 hq

omit hq0 in
theorem norm_rootPlus_le' : ‖cepsRootPlus D θ ρW μ q‖ ≤ dom.c₀ / 4 :=
  dom.norm_rootPlus_le hW hθ hD (dom.norm_ofReal_le_μ₀ hμ) hq

omit hq0 in
theorem norm_rootMinus_le' : ‖cepsRootMinus D θ ρW μ q‖ ≤ dom.c₀ / 4 :=
  dom.norm_rootMinus_le hW hθ hD (dom.norm_ofReal_le_μ₀ hμ) hq

/-- `1 - A₊(β₊) = 0`. -/
theorem one_sub_asc_rootPlus :
    1 - ascTransform (driftStep ρW μ) (cexp (-q)) (cepsRootPlus D θ ρW μ q) = 0 := by
  have := hW.isProbabilityMeasure
  have hb := dom.norm_rootPlus_le' hW hθ hD hμ hq
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hre := (dom.re_roots hW hθ hD hμ hq0 hq).1
  have hwh := dom.wienerHopf_cepsD hW hθ hD hμ hq0.le (ζ := cepsRootPlus D θ ρW μ q)
    (by have := abs_re_le_norm (cepsRootPlus D θ ρW μ q); linarith)
  rw [dom.cepsD_rootPlus hW hθ hD hμ hq] at hwh
  have hlt := norm_descTransform_exp_lt_one (ρ := driftStep ρW μ) hq0 hre.le
  have hne : 1 - descTransform (driftStep ρW μ) (cexp (-q)) (cepsRootPlus D θ ρW μ q) ≠ 0 := by
    intro h0
    rw [← sub_eq_zero.mp h0, norm_one] at hlt
    exact lt_irrefl 1 hlt
  exact (mul_eq_zero.mp hwh).resolve_right hne

theorem identP_rootPlus : dom.identP ρW μ q (cepsRootPlus D θ ρW μ q) = 0 := by
  rw [identP, dom.one_sub_asc_rootPlus hW hθ hD hμ hq0 hq, zero_mul]

omit hq0 in
theorem differentiableAt_identΦ {ζ : ℂ} (hζ : ζ.re ≠ 2 * dom.c₀) :
    DifferentiableAt ℂ (dom.identΦ ρW μ q) ζ := by
  have hc0 := dom.c₀_pos
  exact (dom.differentiableAt_lineCauchy_logF hW hθ hD (by linarith) le_rfl hμ hq hζ).const_mul _

omit hq0 in
theorem differentiableAt_identΨ {ζ : ℂ} (hζ : ζ.re ≠ dom.c₀) :
    DifferentiableAt ℂ (dom.identΨ ρW μ q) ζ := by
  have hc0 := dom.c₀_pos
  exact (dom.differentiableAt_lineCauchy_logF hW hθ hD le_rfl (by linarith) hμ hq hζ).const_mul _

theorem differentiableAt_identP {ζ : ℂ} (hζ : ζ.re < 2 * dom.c₀) :
    DifferentiableAt ℂ (dom.identP ρW μ q) ζ := by
  have hθc := dom.two_c₀_lt
  have hA := (dom.differentiableOn_asc hW hθ hD hμ (s := cexp (-q))
    (norm_cexp_neg_le_one hq0.le) ζ (by show ζ.re < θ / 2; linarith)).differentiableAt
    ((isOpen_lt continuous_re continuous_const).mem_nhds (by show ζ.re < θ / 2; linarith))
  have hL : DifferentiableAt ℂ (fun ζ => cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ) ζ := by
    have h1 := dom.differentiableAt_identΦ hW hθ hD hμ hq (ζ := ζ) hζ.ne
    have h2 : DifferentiableAt ℂ (fun ζ : ℂ => Complex.log (((1 : ℝ) : ℂ) - ζ)) ζ :=
      ((differentiableAt_const _).sub differentiableAt_id).clog (dom.one_sub_mem_slitPlane hζ)
    exact h1.sub h2
  exact ((differentiableAt_const _).sub hA).mul hL.neg.cexp

theorem differentiableAt_identEL {ζ : ℂ} (hζ : ζ.re < 2 * dom.c₀) :
    DifferentiableAt ℂ (dom.identEL ρW μ q) ζ := by
  have hb := dom.norm_rootPlus_le' hW hθ hD hμ hq
  have hc0 := dom.c₀_pos
  set U : Set ℂ := {w : ℂ | w.re < 2 * dom.c₀}
  have hU : IsOpen U := isOpen_lt continuous_re continuous_const
  have hbU : cepsRootPlus D θ ρW μ q ∈ U := by
    show (cepsRootPlus D θ ρW μ q).re < 2 * dom.c₀
    have := re_le_norm (cepsRootPlus D θ ρW μ q); linarith
  have hPU : DifferentiableOn ℂ (dom.identP ρW μ q) U := fun w hw =>
    (dom.differentiableAt_identP hW hθ hD hμ hq0 hq hw).differentiableWithinAt
  have hd := (differentiableOn_dslope (hU.mem_nhds hbU)).mpr hPU
  exact (hd.differentiableAt (hU.mem_nhds hζ)).neg

theorem identEL_eq {ζ : ℂ} (hζ : ζ ≠ cepsRootPlus D θ ρW μ q) :
    dom.identEL ρW μ q ζ = dom.identP ρW μ q ζ / (cepsRootPlus D θ ρW μ q - ζ) := by
  have hne : ζ - cepsRootPlus D θ ρW μ q ≠ 0 := sub_ne_zero.mpr hζ
  rw [identEL, dslope_of_ne _ hζ, slope_def_field, dom.identP_rootPlus hW hθ hD hμ hq0 hq,
    sub_zero, ← neg_sub ζ, div_neg]

omit hθ hD hμ hq in
theorem one_sub_desc_ne_zero {ζ : ℂ} (hζ : 0 ≤ ζ.re) :
    1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ ≠ 0 := by
  have := hW.isProbabilityMeasure
  have hlt := norm_descTransform_exp_lt_one (ρ := driftStep ρW μ) hq0 hζ
  intro h0
  rw [← sub_eq_zero.mp h0, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem differentiableAt_identER {ζ : ℂ} (hζ : dom.c₀ < ζ.re) :
    DifferentiableAt ℂ (dom.identER ρW μ q) ζ := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hA := (dom.differentiableOn_desc hW hθ hD hμ (s := cexp (-q))
    (norm_cexp_neg_le_one hq0.le) ζ (by show -(θ / 2) < ζ.re; linarith)).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by show -(θ / 2) < ζ.re; linarith))
  have hΨ := dom.differentiableAt_identΨ hW hθ hD hμ hq (ζ := ζ) hζ.ne'
  have hden : (1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ) * (1 + ζ) ≠ 0 := by
    refine mul_ne_zero (one_sub_desc_ne_zero hW hq0 (by linarith)) ?_
    intro h0; have := congrArg re h0; simp at this; linarith
  exact ((differentiableAt_id.sub_const _).mul hΨ.neg.cexp).div
    (((differentiableAt_const _).sub hA).mul ((differentiableAt_const _).add differentiableAt_id))
    hden

/-- **Agreement on the overlap** `c₀ < Re ζ < 2c₀` (Plemelj and W-3). -/
theorem identEL_eq_identER {ζ : ℂ} (hζ1 : dom.c₀ < ζ.re) (hζ2 : ζ.re < 2 * dom.c₀) :
    dom.identEL ρW μ q ζ = dom.identER ρW μ q ζ := by
  have := hW.isProbabilityMeasure
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hbp := dom.norm_rootPlus_le' hW hθ hD hμ hq
  have hbm := dom.norm_rootMinus_le' hW hθ hD hμ hq
  have hζn : dom.c₀ < ‖ζ‖ := lt_of_lt_of_le hζ1 (re_le_norm ζ)
  have hne_p : ζ ≠ cepsRootPlus D θ ρW μ q := by intro h; rw [h] at hζn; linarith
  have hne_m : ζ ≠ cepsRootMinus D θ ρW μ q := by intro h; rw [h] at hζn; linarith
  have hAmne : 1 - descTransform (driftStep ρW μ) (cexp (-q)) ζ ≠ 0 :=
    one_sub_desc_ne_zero hW hq0 (by linarith)
  have h1ζ : (1 : ℂ) + ζ ≠ 0 := by intro h0; have := congrArg re h0; simp at this; linarith
  have hβζ : cepsRootPlus D θ ρW μ q - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne_p)
  have hYne : cexp (dom.identΦ ρW μ q ζ) ≠ 0 := Complex.exp_ne_zero _
  rw [dom.identEL_eq hW hθ hD hμ hq0 hq hne_p, identER, identP, div_eq_div_iff hβζ
    (mul_ne_zero hAmne h1ζ)]
  apply mul_right_cancel₀ hYne
  set βp := cepsRootPlus D θ ρW μ q
  set βm := cepsRootMinus D θ ρW μ q
  set Ap := ascTransform (driftStep ρW μ) (cexp (-q)) ζ
  set Am := descTransform (driftStep ρW μ) (cexp (-q)) ζ
  set F := cepsF D θ ρW ((1 : ℝ) : ℂ) μ q ζ with hF
  set d := cepsD ρW μ q ζ
  set X := cexp (-dom.identΨ ρW μ q ζ)
  set Y := cexp (dom.identΦ ρW μ q ζ)
  set E2 := cexp (-cepsCanonL D θ ρW 1 (2 * dom.c₀) μ q ζ) with hE2
  have hWH : (1 - Ap) * (1 - Am) = d := dom.wienerHopf_cepsD hW hθ hD hμ hq0.le
    (by rw [abs_of_pos (by linarith)]; linarith)
  have hD₀ : cepsQuad D θ ρW μ q ζ = (ζ - βp) * (ζ - βm) := rfl
  have hD₀ne : cepsQuad D θ ρW μ q ζ ≠ 0 := by
    rw [hD₀]; exact mul_ne_zero (sub_ne_zero.mpr hne_p) (sub_ne_zero.mpr hne_m)
  have hFdef : F * ((ζ - βp) * (ζ - βm)) = d * (ζ ^ 2 - 1) := by
    rw [← hD₀, hF, cepsF, div_mul_cancel₀ _ hD₀ne, ofReal_one, one_pow]
  obtain ⟨hFre, -⟩ := dom.re_cepsF_ge hW hθ hD (γ := 1) (by norm_num) le_rfl (ζ := ζ) hμ'
    (by simp; exact dom.η_pos.le) hq (by rw [abs_of_pos (by linarith)]; exact hζ1.le)
    (by rw [abs_of_pos (by linarith)]; exact hζ2.le)
  have hFre' : dom.d₀ ≤ F.re := hFre
  have hFne : F ≠ 0 := by
    intro h0; have := dom.d₀_pos hD; rw [h0, zero_re] at hFre'; linarith
  have hpl := dom.plemelj hW hθ hD hμ hq hζ1 hζ2
  have hXY : Y * X = F := by
    show cexp (dom.identΦ ρW μ q ζ) * cexp (-dom.identΨ ρW μ q ζ) = F
    rw [← Complex.exp_add, ← sub_eq_add_neg]
    simp only [identΨ, identΦ]
    rw [hpl, Complex.exp_log hFne]
  have hL : E2 * Y = 1 - ζ := by
    rw [hE2, dom.cexp_neg_canonL₂ ρW μ q hζ2, mul_assoc, mul_comm _ Y, ← mul_assoc,
      ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul, ofReal_one]
  linear_combination (1 - Ap) * (1 - Am) * (1 + ζ) * hL + (1 + ζ) * (1 - ζ) * hWH -
    (ζ - βm) * (βp - ζ) * hXY + hFdef

end

end CepsCanonDomain

end PGM
