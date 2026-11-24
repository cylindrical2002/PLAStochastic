import PLAStochastic.Index.CEPS.Ident.Ladder
import PLAStochastic.ForMathlib.Analysis.Complex.LineCauchy

/-!
# CEPS WP4: the canonical factor as a line Cauchy transform; the Plemelj relation

With `γ = 1` and `φ_c(y) = log F(c + i y; μ, q)` (`cepsLogFLine`), the canonical factor is
`L^{(c)}(ζ) = (2π)⁻¹ lineCauchy φ_c c ζ - log(1 - ζ)` (`cepsCanonL_eq_lineCauchy`). For real
`|μ| ≤ μ₀`, `‖q‖ ≤ q₀` (closed ball) and `c ∈ [c₀, 2c₀]`:

* `integrable_logFLine`: `φ_c(y)/(c + i y - ζ)` is integrable for every `Re ζ ≠ c`;
* `differentiableAt_lineCauchy_logF`: the Cauchy transform is holomorphic off the line;
* `norm_lineCauchy_logF_le`: `‖(2π)⁻¹ lineCauchy φ_c c ζ‖ ≤ CL (2D²/θ + 1/(2|c - Re ζ|) + 1/(2c))`;
* `plemelj`: for `c₀ < Re ζ < 2c₀`,
  `(2π)⁻¹ lineCauchy φ_{2c₀} (2c₀) ζ - (2π)⁻¹ lineCauchy φ_{c₀} c₀ ζ = log F(ζ)`;
* `continuousOn_canonL_q`: `q ↦ L(ζ; μ, q)` is continuous on the closed ball `‖q‖ ≤ q₀`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

/-- `log F(c + i y; μ, q)` with `γ = 1`. -/
def cepsLogFLine (D θ : ℝ) (ρW : Measure ℝ) (c : ℝ) (μ q : ℂ) (y : ℝ) : ℂ :=
  Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q (c + y * I))

theorem cepsCanonL_eq_lineCauchy (D θ : ℝ) (ρW : Measure ℝ) (c : ℝ) (μ q ζ : ℂ) :
    cepsCanonL D θ ρW 1 c μ q ζ =
      (2 * Real.pi : ℂ)⁻¹ * lineCauchy (cepsLogFLine D θ ρW c μ q) c ζ -
        Complex.log (((1 : ℝ) : ℂ) - ζ) := rfl

/-- The dominating function is unchanged by reflecting `ζ` across the line. -/
theorem cepsLineBound_reflect (ρW : Measure ℝ) (c : ℝ) (ζ : ℂ) :
    cepsLineBound ρW c ζ = cepsLineBound ρW c (((2 * c - ζ.re : ℝ) : ℂ) + ζ.im * I) := by
  funext y
  simp only [cepsLineBound, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, mul_zero,
    sub_zero, add_im, mul_im, mul_one, add_zero, zero_add]
  ring_nf

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

theorem integrable_cepsLineBound_of_ne (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
    {c : ℝ} (hc : 0 < c) (hcθ : c < θ / 2) {ζ : ℂ} (hζ : ζ.re ≠ c) :
    Integrable (cepsLineBound ρW c ζ) ∧
      ∫ y, cepsLineBound ρW c ζ y ≤ 4 * Real.pi * D ^ 2 / θ + Real.pi / |c - ζ.re| +
        Real.pi / c := by
  rcases lt_or_gt_of_ne hζ with h | h
  · have := integrable_cepsLineBound hW hθ hD hc hcθ h
    rwa [abs_of_pos (by linarith)]
  · set ζ' : ℂ := ((2 * c - ζ.re : ℝ) : ℂ) + ζ.im * I
    have hζ' : ζ'.re = 2 * c - ζ.re := by simp [ζ']
    have := integrable_cepsLineBound hW hθ hD hc hcθ (ζ := ζ') (by rw [hζ']; linarith)
    rw [cepsLineBound_reflect ρW c ζ, abs_of_neg (by linarith)]
    rw [hζ'] at this
    rwa [show c - (2 * c - ζ.re) = -(c - ζ.re) by ring] at this

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

omit hW hθ hD in
theorem CL_nonneg : 0 ≤ dom.CL := by unfold CL Linf; have := dom.ρA_pos; positivity

/-- Pointwise domination, any side of the line. -/
theorem norm_logFLine_div_le {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re ≠ c) (y : ℝ) :
    ‖cepsLogFLine D θ ρW c μ q y / ((c : ℂ) + y * I - ζ)‖ ≤
      dom.CL * cepsLineBound ρW c ζ y := by
  have hc0 := dom.c₀_pos
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  set s : ℂ := c + y * I with hs
  have hsre : s.re = c := by simp [hs]
  have hlog := dom.norm_log_cepsF_le hW hθ hD (γ := 1) (by norm_num) le_rfl (ζ := s) hμ'
    (by simp; exact dom.η_pos.le) hq (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
    (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
  have hsζ : 0 < ‖s - ζ‖ := norm_pos_iff.mpr (vline_sub_ne_zero hζ y)
  have hs0 : 0 < ‖s‖ := by
    have := re_le_norm s; rw [hsre] at this; linarith
  have hb2 : (1 / ‖s - ζ‖) ^ 2 = ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ := by
    rw [div_pow, one_pow, one_div, hs, norm_vline_sub_sq]
  have he2 : (1 / ‖s‖) ^ 2 = ((y - 0) ^ 2 + c ^ 2)⁻¹ := by
    have := norm_vline_sub_sq c y 0
    simp only [sub_zero, zero_re, zero_im] at this
    rw [div_pow, one_pow, one_div, hs, this, sub_zero]
  have hCL := dom.CL_nonneg
  unfold cepsLogFLine
  rw [← hs, norm_div]
  set a := ‖stepTransform ρW s‖
  set b := 1 / ‖s - ζ‖
  set e := 1 / ‖s‖
  calc ‖Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q s)‖ / ‖s - ζ‖
      = ‖Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q s)‖ * b := by rw [div_eq_mul_one_div]
    _ ≤ dom.CL * (a + e) * b := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simpa [e] using hlog
    _ ≤ dom.CL * (a ^ 2 + b ^ 2 + e ^ 2) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hCL
        nlinarith [sq_nonneg (a - b), sq_nonneg (e - b), sq_nonneg a, sq_nonneg e]
    _ = dom.CL * cepsLineBound ρW c ζ y := by
        rw [cepsLineBound, ← hs, ← hb2, ← he2]

theorem continuous_logFLine {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) :
    Continuous (cepsLogFLine D θ ρW c μ q) :=
  dom.continuous_logF_line hW hθ hD (γ := 1) (by norm_num) le_rfl hc1 hc2
    (dom.norm_ofReal_le_μ₀ hμ) (by simp) hq

/-- Integrability of the line integrand at every point off the line. -/
theorem integrable_logFLine {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re ≠ c) :
    Integrable fun y : ℝ => cepsLogFLine D θ ρW c μ q y / ((c : ℂ) + y * I - ζ) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  obtain ⟨hB, -⟩ := integrable_cepsLineBound_of_ne hW hθ hD (c := c) (by linarith)
    (by linarith) hζ
  refine (hB.const_mul dom.CL).mono' ?_ (Eventually.of_forall fun y =>
    dom.norm_logFLine_div_le hW hθ hD hc1 hc2 hμ hq hζ y)
  exact ((dom.continuous_logFLine hW hθ hD hc1 hc2 hμ hq).div (by fun_prop)
    (vline_sub_ne_zero hζ)).aestronglyMeasurable

theorem differentiableAt_lineCauchy_logF {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀)
    {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re ≠ c) :
    DifferentiableAt ℂ (lineCauchy (cepsLogFLine D θ ρW c μ q) c) ζ := by
  have hc0 := dom.c₀_pos
  have h0 : (0 : ℂ).re ≠ c := by simp; linarith
  exact differentiableAt_lineCauchy h0 (dom.integrable_logFLine hW hθ hD hc1 hc2 hμ hq h0) hζ

/-- `‖(2π)⁻¹ lineCauchy φ_c c ζ‖ ≤ CL (2D²/θ + 1/(2|c - Re ζ|) + 1/(2c))`. -/
theorem norm_lineCauchy_logF_le {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re ≠ c) :
    ‖(2 * Real.pi : ℂ)⁻¹ * lineCauchy (cepsLogFLine D θ ρW c μ q) c ζ‖ ≤
      dom.CL * (2 * D ^ 2 / θ + 1 / (2 * |c - ζ.re|) + 1 / (2 * c)) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  obtain ⟨hB, hBle⟩ := integrable_cepsLineBound_of_ne hW hθ hD (c := c) (by linarith)
    (by linarith) hζ
  have hCL := dom.CL_nonneg
  have hpi := Real.pi_pos
  have hd : 0 < |c - ζ.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hζ))
  have hint : ‖lineCauchy (cepsLogFLine D θ ρW c μ q) c ζ‖ ≤
      dom.CL * (4 * Real.pi * D ^ 2 / θ + Real.pi / |c - ζ.re| + Real.pi / c) := by
    calc ‖lineCauchy (cepsLogFLine D θ ρW c μ q) c ζ‖
        ≤ ∫ y, dom.CL * cepsLineBound ρW c ζ y :=
          norm_integral_le_of_norm_le (hB.const_mul _) (Eventually.of_forall fun y =>
            dom.norm_logFLine_div_le hW hθ hD hc1 hc2 hμ hq hζ y)
      _ = dom.CL * ∫ y, cepsLineBound ρW c ζ y := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hBle hCL
  rw [norm_mul, norm_inv, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]]
  calc (2 * Real.pi)⁻¹ * ‖lineCauchy (cepsLogFLine D θ ρW c μ q) c ζ‖
      ≤ (2 * Real.pi)⁻¹ * (dom.CL * (4 * Real.pi * D ^ 2 / θ + Real.pi / |c - ζ.re| +
          Real.pi / c)) := by gcongr
    _ = dom.CL * (2 * D ^ 2 / θ + 1 / (2 * |c - ζ.re|) + 1 / (2 * c)) := by
        field_simp
        ring

/-- The line logarithm is holomorphic on the closed strip `c₀ ≤ Re ≤ 2c₀`. -/
theorem differentiableAt_logF_strip {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q z : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    (hz : z.re ∈ Icc dom.c₀ (2 * dom.c₀)) :
    DifferentiableAt ℂ (fun z => Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q z)) z := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hzn : dom.c₀ / 2 ≤ ‖z‖ := by have := re_le_norm z; linarith [hz.1]
  have hF := dom.differentiableAt_cepsF_z hW hθ hD (γ := ((1 : ℝ) : ℂ)) hμ' hq hzn
    (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2])
  obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD (γ := 1) (by norm_num) le_rfl (ζ := z) hμ'
    (by simp; exact dom.η_pos.le) hq
    (by rw [abs_of_pos (by linarith [hz.1])]; exact hz.1)
    (by rw [abs_of_pos (by linarith [hz.1])]; exact hz.2)
  exact hF.clog (Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre))

/-- **Plemelj on the strip `[c₀, 2c₀]`.** -/
theorem plemelj {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    (hζ1 : dom.c₀ < ζ.re) (hζ2 : ζ.re < 2 * dom.c₀) :
    (2 * Real.pi : ℂ)⁻¹ * lineCauchy (cepsLogFLine D θ ρW (2 * dom.c₀) μ q) (2 * dom.c₀) ζ -
      (2 * Real.pi : ℂ)⁻¹ * lineCauchy (cepsLogFLine D θ ρW dom.c₀ μ q) dom.c₀ ζ =
        Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q ζ) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hCL := dom.CL_nonneg
  set h : ℂ → ℂ := fun z => Complex.log (cepsF D θ ρW ((1 : ℝ) : ℂ) μ q z) with hh
  have hM : ∀ z : ℂ, z.re ∈ Icc dom.c₀ (2 * dom.c₀) →
      ‖h z‖ ≤ dom.CL * ((2 + 128 * D / θ) + 1 / dom.c₀) := by
    intro z hz
    have hlog := dom.norm_log_cepsF_le hW hθ hD (γ := 1) (by norm_num) le_rfl (ζ := z) hμ'
      (by simp; exact dom.η_pos.le) hq (by rw [abs_of_pos (by linarith [hz.1])]; exact hz.1)
      (by rw [abs_of_pos (by linarith [hz.1])]; exact hz.2)
    have hMz := norm_stepTransform_le_strip hW hθ hD.le (z := z)
      (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2])
    have hz1 : 1 / ‖z‖ ≤ 1 / dom.c₀ :=
      one_div_le_one_div_of_le hc0 ((re_le_norm z).trans' hz.1)
    exact hlog.trans (mul_le_mul_of_nonneg_left (add_le_add hMz hz1) hCL)
  have hstrip := vline_cauchy_strip (h := h) (a := dom.c₀) (b := 2 * dom.c₀) (by linarith)
    (fun z hz => dom.differentiableAt_logF_strip hW hθ hD hμ hq hz) hM hζ1 hζ2
    (dom.integrable_logFLine hW hθ hD le_rfl (by linarith) hμ hq (ne_of_gt hζ1))
    (dom.integrable_logFLine hW hθ hD (by linarith) le_rfl hμ hq (ne_of_lt hζ2))
  have e1 : lineCauchy (cepsLogFLine D θ ρW (2 * dom.c₀) μ q) (2 * dom.c₀) ζ =
      ∫ y : ℝ, h (((2 * dom.c₀ : ℝ) : ℂ) + y * I) / (((2 * dom.c₀ : ℝ) : ℂ) + y * I - ζ) := rfl
  have e2 : lineCauchy (cepsLogFLine D θ ρW dom.c₀ μ q) dom.c₀ ζ =
      ∫ y : ℝ, h ((dom.c₀ : ℂ) + y * I) / ((dom.c₀ : ℂ) + y * I - ζ) := rfl
  rw [← mul_sub, e1, e2, hstrip]
  field_simp
  rfl

/-- `q ↦ L(ζ; μ, q)` is continuous on the closed ball `‖q‖ ≤ q₀` (`Re ζ < c`). -/
theorem continuousOn_canonL_q {c : ℝ} (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℝ}
    (hμ : |μ| ≤ dom.μ₀) {ζ : ℂ} (hζ : ζ.re < c) :
    ContinuousOn (fun q => cepsCanonL D θ ρW 1 c μ q ζ) (closedBall 0 dom.q₀) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  obtain ⟨hB, -⟩ := integrable_cepsLineBound_of_ne hW hθ hD (c := c) (by linarith)
    (by linarith) hζ.ne
  have hint : ContinuousOn (fun q => lineCauchy (cepsLogFLine D θ ρW c μ q) c ζ)
      (closedBall 0 dom.q₀) := by
    refine continuousOn_of_dominated (bound := fun y => dom.CL * cepsLineBound ρW c ζ y)
      (fun q hq => (dom.integrable_logFLine hW hθ hD hc1 hc2 hμ (mem_closedBall_zero_iff.mp hq)
        hζ.ne).aestronglyMeasurable)
      (fun q hq => Eventually.of_forall fun y => dom.norm_logFLine_div_le hW hθ hD hc1 hc2 hμ
        (mem_closedBall_zero_iff.mp hq) hζ.ne y)
      (hB.const_mul _) (Eventually.of_forall fun y => ?_)
    intro q hq
    have hq' := mem_closedBall_zero_iff.mp hq
    set s : ℂ := c + y * I with hs
    have hsre : s.re = c := by simp [hs]
    have hd := dom.differentiableAt_logF_q hW hθ hD (γ := 1) (by norm_num) le_rfl (s := s) hμ'
      (by simp; exact dom.η_pos.le) hq' (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
      (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
    exact (hd.continuousAt.div_const _).continuousWithinAt
  unfold cepsCanonL
  exact (hint.const_smul ((2 * Real.pi : ℂ)⁻¹)).sub continuousOn_const

end

end CepsCanonDomain

end PGM
