import PLAStochastic.Index.CEPS.Canonical.FactorPointwise
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineShift
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineInversion
import PLAStochastic.ForMathlib.Analysis.Complex.Osgood

/-!
# CEPS WP3, lemma C-3(a)(b): the canonical factor is well defined, holomorphic and bounded

Fix `dom : CepsCanonDomain D θ v`, a class step law, real `γ ∈ [1/2, 1]`, an abscissa
`c ∈ [c₀, 2 c₀]` and a real drift `|μ| ≤ μ₀`. With the frozen definition
`cepsCanonL D θ ρW γ c μ q ζ` (`Canonical.FactorDefs`):

* `integrable_cepsCanonL_integrand`: the line integrand is integrable for `‖q‖ ≤ q₀`,
  `Re ζ < c`, dominated by `CL · lineBound` (`norm_lineIntegrand_le`), where
  `lineBound = ‖M₀‖² + ‖s - ζ‖⁻² + ‖s‖⁻²` has integral at most
  `4πD²/θ + π/(c - Re ζ) + π/c` (`integral_lineBound_le`);
* `differentiableOn_cepsCanonL`: `(ζ, q) ↦ L` is jointly holomorphic on `{Re ζ < c} × B(0, q₀)`;
* `continuousOn_cepsCanonL_mu`: `μ ↦ L` is continuous on `[-μ₀, μ₀]`;
* `cepsCanonL_eq_of_abscissa`: `L` does not depend on `c ∈ [c₀, 2 c₀]` (line shift, horizontal
  edges vanish because `‖M₀‖` is bounded on the strip);
* `norm_cepsCanonL_le` (`‖ζ‖ ≤ c₀/2`) and `norm_cepsCanonL_add_log_le` (`Re ζ ≤ c₀/2`): uniform
  bounds by class constants.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- `‖M₀(z)‖ ≤ 2 + 128 D/θ` on `|Re z| ≤ θ/2`. -/
theorem norm_stepTransform_le_strip (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D)
    {z : ℂ} (hz : |z.re| ≤ θ / 2) : ‖stepTransform ρW z‖ ≤ 2 + 128 * D / θ := by
  have := hW.isProbabilityMeasure
  have h1 := hW.integral_exp_le hθ hD (t := θ / 2) (by rw [abs_of_pos (by positivity)])
  have h2 := hW.integral_exp_le hθ hD (t := -(θ / 2))
    (by rw [abs_neg, abs_of_pos (by positivity)])
  have hint := h1.1.add h2.1
  have hpt : ∀ w : ℝ, ‖cexp (z * w)‖ ≤ Real.exp (θ / 2 * w) + Real.exp (-(θ / 2) * w) := by
    intro w
    rw [Complex.norm_exp]
    simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    rcases le_total 0 w with hw | hw
    · have : z.re * w ≤ θ / 2 * w := mul_le_mul_of_nonneg_right (le_of_abs_le hz) hw
      have := Real.exp_le_exp.mpr this; linarith [Real.exp_pos (-(θ / 2) * w)]
    · have : z.re * w ≤ -(θ / 2) * w := by
        have := neg_abs_le z.re; nlinarith [abs_nonneg z.re]
      have := Real.exp_le_exp.mpr this; linarith [Real.exp_pos (θ / 2 * w)]
  calc ‖stepTransform ρW z‖ ≤ ∫ w, (Real.exp (θ / 2 * w) + Real.exp (-(θ / 2) * w)) ∂ρW :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall hpt)
    _ = ∫ w, Real.exp (θ / 2 * w) ∂ρW + ∫ w, Real.exp (-(θ / 2) * w) ∂ρW :=
        integral_add h1.1 h2.1
    _ ≤ (1 + (θ / 2) ^ 2 * (256 * D / θ ^ 3)) + (1 + (-(θ / 2)) ^ 2 * (256 * D / θ ^ 3)) :=
        add_le_add h1.2 h2.2
    _ = 2 + 128 * D / θ := by field_simp; ring

/-- The line integrand `log F(c + i y)/(c + i y - ζ)`. -/
def cepsLineIntegrand (D θ : ℝ) (ρW : Measure ℝ) (γ c : ℝ) (μ q ζ : ℂ) (y : ℝ) : ℂ :=
  Complex.log (cepsF D θ ρW γ μ q (c + y * I)) / (c + y * I - ζ)

/-- The dominating function `‖M₀‖² + ‖s - ζ‖⁻² + ‖s‖⁻²` on the line `Re s = c`. -/
def cepsLineBound (ρW : Measure ℝ) (c : ℝ) (ζ : ℂ) (y : ℝ) : ℝ :=
  ‖stepTransform ρW (c + y * I)‖ ^ 2 + ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ +
    ((y - 0) ^ 2 + c ^ 2)⁻¹

theorem cepsCanonL_eq (D θ : ℝ) (ρW : Measure ℝ) (γ c : ℝ) (μ q ζ : ℂ) :
    cepsCanonL D θ ρW γ c μ q ζ =
      (2 * Real.pi : ℂ)⁻¹ * (∫ y : ℝ, cepsLineIntegrand D θ ρW γ c μ q ζ y) -
        Complex.log (γ - ζ) := rfl

theorem norm_line_sub_sq (c y : ℝ) (ζ : ℂ) :
    ‖(c : ℂ) + y * I - ζ‖ ^ 2 = (y - ζ.im) ^ 2 + (c - ζ.re) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, add_im, mul_im]
  ring

theorem norm_line_sq (c y : ℝ) : ‖(c : ℂ) + y * I‖ ^ 2 = (y - 0) ^ 2 + c ^ 2 := by
  have := norm_line_sub_sq c y 0
  simpa using this

theorem continuous_stepTransform_line (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
    {c : ℝ} (hcθ : |c| < θ / 2) : Continuous fun y : ℝ => stepTransform ρW (c + y * I) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  have h := (differentiableAt_stepTransform_strip hW hθ hD (ζ := c + y * I)
    (by simpa using hcθ)).continuousAt
  exact ContinuousAt.comp (g := stepTransform ρW) h (by fun_prop)

/-- Integrability and integral of the dominating function. -/
theorem integrable_cepsLineBound (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
    {c : ℝ} (hc : 0 < c) (hcθ : c < θ / 2) {ζ : ℂ} (hζ : ζ.re < c) :
    Integrable (cepsLineBound ρW c ζ) ∧
      ∫ y, cepsLineBound ρW c ζ y ≤ 4 * Real.pi * D ^ 2 / θ + Real.pi / (c - ζ.re) +
        Real.pi / c := by
  have hM := lintegral_norm_sq_stepTransform_le hW hθ (c := c) (by rw [abs_of_pos hc]; linarith)
  have hMc := continuous_stepTransform_line hW hθ hD (c := c) (by rw [abs_of_pos hc]; exact hcθ)
  have hsq_int : Integrable fun y : ℝ => ‖stepTransform ρW (c + y * I)‖ ^ 2 := by
    refine ⟨(hMc.norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by positivity)]
    exact lt_of_le_of_lt hM (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hsq_le : ∫ y : ℝ, ‖stepTransform ρW (c + y * I)‖ ^ 2 ≤ 2 * Real.pi * (2 * D ^ 2 / θ) := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (f := fun y : ℝ => ‖stepTransform ρW (c + y * I)‖ ^ 2)
      (Eventually.of_forall fun y => sq_nonneg _)
      (by exact (hMc.norm.pow 2).aestronglyMeasurable)]
    calc _ ≤ (ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (2 * D ^ 2 / θ)).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hM
      _ = 2 * Real.pi * (2 * D ^ 2 / θ) := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
            ENNReal.toReal_ofReal (by positivity)]
  obtain ⟨hi1, he1⟩ := integral_inv_sq_add_sq (d := c - ζ.re) (by linarith) ζ.im
  obtain ⟨hi2, he2⟩ := integral_inv_sq_add_sq (d := c) hc 0
  have hint : Integrable (cepsLineBound ρW c ζ) := (hsq_int.add hi1).add hi2
  refine ⟨hint, ?_⟩
  have e : ∫ y, cepsLineBound ρW c ζ y = (∫ y : ℝ, ‖stepTransform ρW (c + y * I)‖ ^ 2) +
      (∫ y : ℝ, ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹) + ∫ y : ℝ, ((y - 0) ^ 2 + c ^ 2)⁻¹ := by
    unfold cepsLineBound
    rw [integral_add (f := fun y : ℝ => ‖stepTransform ρW (c + y * I)‖ ^ 2 +
        ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹) (g := fun y : ℝ => ((y - 0) ^ 2 + c ^ 2)⁻¹)
        (hsq_int.add hi1) hi2,
      integral_add (f := fun y : ℝ => ‖stepTransform ρW (c + y * I)‖ ^ 2)
        (g := fun y : ℝ => ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹) hsq_int hi1]
  have he1' : ∫ y : ℝ, ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ = Real.pi / (c - ζ.re) := he1
  have he2' : ∫ y : ℝ, ((y - 0) ^ 2 + c ^ 2)⁻¹ = Real.pi / c := he2
  rw [e, he1', he2']
  have : 2 * Real.pi * (2 * D ^ 2 / θ) = 4 * Real.pi * D ^ 2 / θ := by ring
  linarith

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- Pointwise domination of the line integrand (any admissible complex `μ`). -/
theorem norm_lineIntegrand_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q ζ : ℂ} {y : ℝ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : |μ.im| * |y| ≤ dom.η) (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < c) :
    ‖cepsLineIntegrand D θ ρW γ c μ q ζ y‖ ≤ dom.CL * cepsLineBound ρW c ζ y := by
  have hc0 := dom.c₀_pos
  set s : ℂ := c + y * I with hs
  have hsre : s.re = c := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hlog := dom.norm_log_cepsF_le hW hθ hD hγ1 hγ2 (ζ := s) hμ (by rwa [hsim])
    hq (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
    (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
  have hsζ : 0 < ‖s - ζ‖ := by
    have := re_le_norm (s - ζ); rw [sub_re, hsre] at this; linarith
  have hs0 : 0 < ‖s‖ := by
    have := re_le_norm s; rw [hsre] at this; linarith
  have hb2 : (1 / ‖s - ζ‖) ^ 2 = ((y - ζ.im) ^ 2 + (c - ζ.re) ^ 2)⁻¹ := by
    rw [div_pow, one_pow, one_div, hs, norm_line_sub_sq]
  have he2 : (1 / ‖s‖) ^ 2 = ((y - 0) ^ 2 + c ^ 2)⁻¹ := by
    rw [div_pow, one_pow, one_div, hs, norm_line_sq]
  have hCL : 0 ≤ dom.CL := by
    unfold CL Linf; have := dom.ρA_pos; positivity
  unfold cepsLineIntegrand
  rw [← hs, norm_div]
  set a := ‖stepTransform ρW s‖
  set b := 1 / ‖s - ζ‖
  set e := 1 / ‖s‖
  calc ‖Complex.log (cepsF D θ ρW γ μ q s)‖ / ‖s - ζ‖
      = ‖Complex.log (cepsF D θ ρW γ μ q s)‖ * b := by rw [div_eq_mul_one_div]
    _ ≤ dom.CL * (a + e) * b := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        simpa [e] using hlog
    _ ≤ dom.CL * (a ^ 2 + b ^ 2 + e ^ 2) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hCL
        nlinarith [sq_nonneg (a - b), sq_nonneg (e - b), sq_nonneg a, sq_nonneg e]
    _ = dom.CL * cepsLineBound ρW c ζ y := by
        rw [cepsLineBound, ← hs, ← hb2, ← he2]

/-- Continuity of the line integrand in `y`. -/
theorem continuous_lineIntegrand {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < c) :
    Continuous (cepsLineIntegrand D θ ρW γ c μ q ζ) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  refine continuous_iff_continuousAt.mpr fun y => ?_
  set s : ℂ := c + y * I with hs
  have hsre : s.re = c := by simp [hs]
  have hsim : s.im = y := by simp [hs]
  have hsn : dom.c₀ / 2 ≤ ‖s‖ := by
    have := re_le_norm s; rw [hsre] at this; linarith
  have hF := (dom.differentiableAt_cepsF_z hW hθ hD (γ := γ) hμ hq hsn
    (by rw [hsre, abs_of_pos (by linarith)]; linarith)).continuousAt
  obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 (ζ := s) hμ
    (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq
    (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
    (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
  have hslit : cepsF D θ ρW γ μ q s ∈ slitPlane :=
    Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre)
  have hline : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) y := by fun_prop
  have h1 : ContinuousAt (fun y : ℝ => Complex.log (cepsF D θ ρW γ μ q (c + y * I))) y :=
    ContinuousAt.comp (g := fun z => Complex.log (cepsF D θ ρW γ μ q z)) (hF.clog hslit) hline
  have hne : (c : ℂ) + y * I - ζ ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith
  exact h1.div (hline.sub continuousAt_const) hne

/-- **C-3(a): integrability.** -/
theorem integrable_cepsCanonL_integrand {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < c) :
    Integrable (cepsLineIntegrand D θ ρW γ c μ q ζ) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  obtain ⟨hB, -⟩ := integrable_cepsLineBound hW hθ hD (c := c) (by linarith) (by linarith) hζ
  refine (hB.const_mul dom.CL).mono'
    (dom.continuous_lineIntegrand hW hθ hD hγ1 hγ2 hc1 hc2 hμ hμη hq hζ).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  exact dom.norm_lineIntegrand_le hW hθ hD hγ1 hγ2 hc1 hc2 hμ
    (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq hζ


/-- `‖∫ integrand‖ ≤ CL (4πD²/θ + π/(c - Re ζ) + π/c)`. -/
theorem norm_integral_lineIntegrand_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < c) :
    ‖∫ y, cepsLineIntegrand D θ ρW γ c μ q ζ y‖ ≤
      dom.CL * (4 * Real.pi * D ^ 2 / θ + Real.pi / (c - ζ.re) + Real.pi / c) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  obtain ⟨hB, hBle⟩ := integrable_cepsLineBound hW hθ hD (c := c) (by linarith) (by linarith) hζ
  have hCL : 0 ≤ dom.CL := by unfold CL Linf; have := dom.ρA_pos; positivity
  calc ‖∫ y, cepsLineIntegrand D θ ρW γ c μ q ζ y‖
      ≤ ∫ y, dom.CL * cepsLineBound ρW c ζ y :=
        norm_integral_le_of_norm_le (hB.const_mul _) (Eventually.of_forall fun y =>
          dom.norm_lineIntegrand_le hW hθ hD hγ1 hγ2 hc1 hc2 hμ
            (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq hζ)
    _ = dom.CL * ∫ y, cepsLineBound ρW c ζ y := integral_const_mul _ _
    _ ≤ dom.CL * (4 * Real.pi * D ^ 2 / θ + Real.pi / (c - ζ.re) + Real.pi / c) :=
        mul_le_mul_of_nonneg_left hBle hCL

/-- **C-3(b).** `‖L(ζ) + log(γ - ζ)‖ ≤ CL (2D²/θ + 3/(2 c₀))` for `Re ζ ≤ c₀/2`. -/
theorem norm_cepsCanonL_add_log_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re ≤ dom.c₀ / 2) :
    ‖cepsCanonL D θ ρW γ c μ q ζ + Complex.log (γ - ζ)‖ ≤
      dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)) := by
  have hc0 := dom.c₀_pos
  have hζ' : ζ.re < c := by linarith
  have h := dom.norm_integral_lineIntegrand_le hW hθ hD hγ1 hγ2 hc1 hc2 hμ hμη hq hζ'
  have hCL : 0 ≤ dom.CL := by unfold CL Linf; have := dom.ρA_pos; positivity
  rw [cepsCanonL_eq, sub_add_cancel, norm_mul, norm_inv, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]]
  have hpi := Real.pi_pos
  have hcr : dom.c₀ / 2 ≤ c - ζ.re := by linarith
  have b1 : Real.pi / (c - ζ.re) ≤ Real.pi / (dom.c₀ / 2) :=
    div_le_div_of_nonneg_left hpi.le (by positivity) hcr
  have b2 : Real.pi / c ≤ Real.pi / dom.c₀ := div_le_div_of_nonneg_left hpi.le hc0 hc1
  calc (2 * Real.pi)⁻¹ * ‖∫ y, cepsLineIntegrand D θ ρW γ c μ q ζ y‖
      ≤ (2 * Real.pi)⁻¹ * (dom.CL * (4 * Real.pi * D ^ 2 / θ + Real.pi / (c - ζ.re) +
          Real.pi / c)) := by gcongr
    _ ≤ (2 * Real.pi)⁻¹ * (dom.CL * (4 * Real.pi * D ^ 2 / θ + Real.pi / (dom.c₀ / 2) +
          Real.pi / dom.c₀)) := by gcongr
    _ = dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)) := by field_simp; ring

/-- **C-3(b).** `‖L(ζ)‖ ≤ CL (2D²/θ + 3/(2 c₀)) + |log(1/4)| + |log 2| + π` for `‖ζ‖ ≤ c₀/2`. -/
theorem norm_cepsCanonL_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 2) :
    ‖cepsCanonL D θ ρW γ c μ q ζ‖ ≤
      dom.CL * (2 * D ^ 2 / θ + 3 / (2 * dom.c₀)) +
        (|Real.log (1 / 4)| + |Real.log 2| + Real.pi) := by
  have hc0 := dom.c₀_pos
  have hcle : dom.c₀ ≤ 1 / 1000 := by have := dom.c₀_le; have := dom.ρA_one; linarith
  have h := dom.norm_cepsCanonL_add_log_le hW hθ hD hγ1 hγ2 hc1 hc2 hμ hμη hq
    ((re_le_norm ζ).trans hζ)
  have hlog : ‖Complex.log (γ - ζ)‖ ≤ |Real.log (1 / 4)| + |Real.log 2| + Real.pi := by
    refine norm_log_le_of_re_ge (by norm_num) ?_ ?_
    · rw [sub_re, ofReal_re]; linarith [re_le_norm ζ]
    · calc ‖(γ : ℂ) - ζ‖ ≤ ‖(γ : ℂ)‖ + ‖ζ‖ := norm_sub_le _ _
        _ ≤ 2 := by
            rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; linarith
  calc ‖cepsCanonL D θ ρW γ c μ q ζ‖
      = ‖(cepsCanonL D θ ρW γ c μ q ζ + Complex.log (γ - ζ)) - Complex.log (γ - ζ)‖ := by ring_nf
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add h hlog


/-- Holomorphy of `q ↦ log F(ζ; μ, q)` on the lines. -/
theorem differentiableAt_logF_q {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q s : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |s.im| ≤ dom.η) (hq : ‖q‖ ≤ dom.q₀)
    (h2 : dom.c₀ ≤ |s.re|) (h3 : |s.re| ≤ 2 * dom.c₀) :
    DifferentiableAt ℂ (fun q => Complex.log (cepsF D θ ρW γ μ q s)) q := by
  have hc0 := dom.c₀_pos
  have hsn : dom.c₀ / 2 ≤ ‖s‖ := by have := abs_re_le_norm s; linarith
  obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 hμ hμη hq h2 h3
  have hslit : cepsF D θ ρW γ μ q s ∈ slitPlane := Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre)
  exact (dom.differentiableAt_cepsF_q hW hθ hD (γ := γ) hμ hq hsn).clog hslit

/-- Continuity in `y` of `log F(c + i y; μ, q)`. -/
theorem continuous_logF_line {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) :
    Continuous fun y : ℝ => Complex.log (cepsF D θ ρW γ μ q (c + y * I)) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  refine continuous_iff_continuousAt.mpr fun y => ?_
  set s : ℂ := c + y * I with hs
  have hsre : s.re = c := by simp [hs]
  have hsn : dom.c₀ / 2 ≤ ‖s‖ := by
    have := re_le_norm s; rw [hsre] at this; linarith
  have hF := (dom.differentiableAt_cepsF_z hW hθ hD (γ := γ) hμ hq hsn
    (by rw [hsre, abs_of_pos (by linarith)]; linarith)).continuousAt
  obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 (ζ := s) hμ
    (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq
    (by rw [hsre, abs_of_pos (by linarith)]; exact hc1)
    (by rw [hsre, abs_of_pos (by linarith)]; exact hc2)
  have hslit : cepsF D θ ρW γ μ q s ∈ slitPlane :=
    Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre)
  have hline : ContinuousAt (fun y : ℝ => (c : ℂ) + y * I) y := by fun_prop
  exact ContinuousAt.comp (g := fun z => Complex.log (cepsF D θ ρW γ μ q z)) (hF.clog hslit) hline

set_option maxHeartbeats 1000000 in
/-- **C-3(a): holomorphy.** `(ζ, q) ↦ L(ζ; μ, q)` is jointly holomorphic on
`{Re ζ < c} × B(0, q₀)` (real `μ`). -/
theorem differentiableOn_cepsCanonL {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {μ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : μ.im = 0) :
    DifferentiableOn ℂ (fun x : ℂ × ℂ => cepsCanonL D θ ρW γ c μ x.2 x.1)
      {x : ℂ × ℂ | x.1.re < c ∧ ‖x.2‖ < dom.q₀} := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hη0 : |μ.im| * 0 ≤ dom.η := by rw [mul_zero]; exact dom.η_pos.le
  have hadm : ∀ y : ℝ, |μ.im| * |((c : ℂ) + y * I).im| ≤ dom.η := by
    intro y; rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le
  have hsre : ∀ y : ℝ, ((c : ℂ) + y * I).re = c := by intro y; simp
  have hs2 : ∀ y : ℝ, dom.c₀ ≤ |((c : ℂ) + y * I).re| := by
    intro y; rw [hsre, abs_of_pos (by linarith)]; exact hc1
  have hs3 : ∀ y : ℝ, |((c : ℂ) + y * I).re| ≤ 2 * dom.c₀ := by
    intro y; rw [hsre, abs_of_pos (by linarith)]; exact hc2
  rintro ⟨ζ₀, q₀'⟩ ⟨hζ₀, hq₀'⟩
  simp only at hζ₀ hq₀'
  set δ : ℝ := min ((c - ζ₀.re) / 2) ((dom.q₀ - ‖q₀'‖) / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (c - ζ₀.re) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (dom.q₀ - ‖q₀'‖) / 4 := min_le_right _ _
  set x₀ : ℂ × ℂ := (ζ₀, q₀') with hx₀
  -- the logarithmic integrand as a function of `(ζ, q)`
  set G : ℝ → ℂ → ℂ := fun y q => Complex.log (cepsF D θ ρW γ μ q (c + y * I)) with hG
  set g : ℂ × ℂ → ℝ → ℂ := fun x y => G y x.2 / ((c : ℂ) + y * I - x.1) with hg
  have hgeq : ∀ x : ℂ × ℂ, (fun y => g x y) = cepsLineIntegrand D θ ρW γ c μ x.2 x.1 := by
    intro x; funext y; rfl
  set g' : ℂ × ℂ → ℝ → ℂ × ℂ →L[ℂ] ℂ := fun x y =>
    (G y x.2 / ((c : ℂ) + y * I - x.1) ^ 2) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (deriv (G y) x.2 / ((c : ℂ) + y * I - x.1)) • ContinuousLinearMap.snd ℂ ℂ ℂ with hg'
  have hball : ∀ x ∈ ball x₀ δ, x.1.re < c - δ ∧ ‖x.2‖ < dom.q₀ - 2 * δ ∧ ‖x.1 - ζ₀‖ < δ := by
    intro x hx
    rw [mem_ball, Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hx
    refine ⟨?_, ?_, hx.1⟩
    · have := (re_le_norm (x.1 - ζ₀)).trans_lt hx.1; rw [sub_re] at this; linarith
    · have := norm_sub_norm_le x.2 q₀'; linarith [hx.2]
  -- `log F` bounds and holomorphy in `q` on the closed disc `‖q‖ ≤ q₀`
  have hlogb : ∀ (y : ℝ) (q : ℂ), ‖q‖ ≤ dom.q₀ →
      ‖G y q‖ ≤ dom.CL * (‖stepTransform ρW (c + y * I)‖ + 1 / ‖(c : ℂ) + y * I‖) := by
    intro y q hq
    exact dom.norm_log_cepsF_le hW hθ hD hγ1 hγ2 hμ (hadm y) hq (hs2 y) (hs3 y)
  have hGd : ∀ (y : ℝ) (q : ℂ), ‖q‖ ≤ dom.q₀ → DifferentiableAt ℂ (G y) q := by
    intro y q hq
    exact dom.differentiableAt_logF_q hW hθ hD hγ1 hγ2 hμ (hadm y) hq (hs2 y) (hs3 y)
  -- derivative bound in `q` (Cauchy on `B(q, 2δ)`)
  have hGd' : ∀ (y : ℝ) (q : ℂ), ‖q‖ < dom.q₀ - 2 * δ →
      ‖deriv (G y) q‖ ≤ dom.CL * (‖stepTransform ρW (c + y * I)‖ + 1 / ‖(c : ℂ) + y * I‖) /
        δ := by
    intro y q hq
    have hdiff : DifferentiableOn ℂ (G y) (ball q (2 * δ)) := by
      intro q' hq'
      have : ‖q'‖ ≤ dom.q₀ := by
        rw [mem_ball, dist_eq_norm] at hq'
        have := norm_sub_norm_le q' q; linarith
      exact (hGd y q' this).differentiableWithinAt
    have hb : ∀ q' ∈ ball q (2 * δ), ‖G y q'‖ ≤
        dom.CL * (‖stepTransform ρW (c + y * I)‖ + 1 / ‖(c : ℂ) + y * I‖) := by
      intro q' hq'
      rw [mem_ball, dist_eq_norm] at hq'
      have := norm_sub_norm_le q' q
      exact hlogb y q' (by linarith)
    have := norm_iteratedDeriv_le_of_ball 1 (by positivity) hdiff hb
    rw [iteratedDeriv_one] at this
    calc ‖deriv (G y) q‖ ≤ (Nat.factorial 1) * (dom.CL * (‖stepTransform ρW (c + y * I)‖ +
          1 / ‖(c : ℂ) + y * I‖)) / (2 * δ / 2) ^ 1 := this
      _ = _ := by simp
  -- the dominating function
  obtain ⟨hB, -⟩ := integrable_cepsLineBound hW hθ hD (c := c) (by linarith) (by linarith) hζ₀
  have hCL : 0 ≤ dom.CL := by unfold CL Linf; have := dom.ρA_pos; positivity
  set bound : ℝ → ℝ := fun y => 4 * dom.CL / δ * cepsLineBound ρW c ζ₀ y with hbound
  have hlow : ∀ (y : ℝ), 2 * δ ≤ ‖(c : ℂ) + y * I - ζ₀‖ := by
    intro y
    have := re_le_norm ((c : ℂ) + y * I - ζ₀)
    rw [sub_re, hsre] at this; linarith
  have hlow2 : ∀ (y : ℝ) (x : ℂ × ℂ), x ∈ ball x₀ δ →
      ‖(c : ℂ) + y * I - ζ₀‖ / 2 ≤ ‖(c : ℂ) + y * I - x.1‖ := by
    intro y x hx
    have h1 := (hball x hx).2.2
    have h2 := hlow y
    have : ‖(c : ℂ) + y * I - ζ₀‖ ≤ ‖(c : ℂ) + y * I - x.1‖ + ‖x.1 - ζ₀‖ := by
      calc ‖(c : ℂ) + y * I - ζ₀‖ = ‖((c : ℂ) + y * I - x.1) + (x.1 - ζ₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  have hlow3 : ∀ (y : ℝ) (x : ℂ × ℂ), x ∈ ball x₀ δ → δ ≤ ‖(c : ℂ) + y * I - x.1‖ := by
    intro y x hx
    have h1 := (hball x hx).1
    have := re_le_norm ((c : ℂ) + y * I - x.1)
    rw [sub_re, hsre] at this; linarith
  have hderiv : ∀ y, ∀ x ∈ ball x₀ δ, HasFDerivAt (fun x => g x y) (g' x y) x := by
    intro y x hx
    obtain ⟨h1, h2, -⟩ := hball x hx
    have hne : (c : ℂ) + y * I - x.1 ≠ 0 := by
      intro h0; have := congrArg re h0; rw [sub_re, hsre, zero_re] at this; linarith
    have hGx : HasDerivAt (G y) (deriv (G y) x.2) x.2 :=
      (hGd y x.2 (by linarith)).hasDerivAt
    have hA : HasFDerivAt (fun x : ℂ × ℂ => G y x.2)
        ((deriv (G y) x.2) • ContinuousLinearMap.snd ℂ ℂ ℂ) x :=
      hGx.comp_hasFDerivAt x (hasFDerivAt_snd (p := x))
    have hK : HasFDerivAt (fun x : ℂ × ℂ => ((c : ℂ) + y * I - x.1)⁻¹)
        ((((c : ℂ) + y * I - x.1) ^ 2)⁻¹ • ContinuousLinearMap.fst ℂ ℂ ℂ) x := by
      have h1 : HasDerivAt (fun z : ℂ => ((c : ℂ) + y * I - z)⁻¹)
          (-(((c : ℂ) + y * I - x.1) ^ 2)⁻¹ * (-1)) x.1 :=
        (hasDerivAt_inv hne).comp x.1 ((hasDerivAt_id x.1).const_sub ((c : ℂ) + y * I))
      have h2 := h1.comp_hasFDerivAt x (hasFDerivAt_fst (𝕜 := ℂ) (p := x))
      rw [show -(((c : ℂ) + y * I - x.1) ^ 2)⁻¹ * (-1) = (((c : ℂ) + y * I - x.1) ^ 2)⁻¹ by ring]
        at h2
      exact h2
    have hprod : HasFDerivAt (fun x : ℂ × ℂ => G y x.2 * ((c : ℂ) + y * I - x.1)⁻¹)
        (G y x.2 • ((((c : ℂ) + y * I - x.1) ^ 2)⁻¹ • ContinuousLinearMap.fst ℂ ℂ ℂ) +
          ((c : ℂ) + y * I - x.1)⁻¹ • ((deriv (G y) x.2) • ContinuousLinearMap.snd ℂ ℂ ℂ)) x :=
      hA.mul hK
    have e1 : (fun x : ℂ × ℂ => G y x.2 * ((c : ℂ) + y * I - x.1)⁻¹) = fun x => g x y := by
      funext x; simp only [hg, div_eq_mul_inv]
    rw [e1] at hprod
    convert hprod using 1
    refine ContinuousLinearMap.ext fun v => ?_
    simp [hg', div_eq_mul_inv]
    ring
  have hderiv_bound : ∀ y, ∀ x ∈ ball x₀ δ, ‖g' x y‖ ≤ bound y := by
    intro y x hx
    obtain ⟨h1, h2, h3⟩ := hball x hx
    have hl := hlow2 y x hx
    have hl0 := hlow y
    have hl3 := hlow3 y x hx
    set a := ‖stepTransform ρW (c + y * I)‖ with ha
    set e := 1 / ‖(c : ℂ) + y * I‖ with he
    set b := 1 / ‖(c : ℂ) + y * I - ζ₀‖ with hb
    set w := ‖(c : ℂ) + y * I - x.1‖ with hw
    have hw0 : 0 < w := lt_of_lt_of_le hδ0 hl3
    have hb0 : 0 ≤ b := by positivity
    have ha0 : 0 ≤ a := norm_nonneg _
    have he0 : 0 ≤ e := by positivity
    have hinv : 1 / w ≤ 2 * b := by
      have h00 : 0 < ‖(c : ℂ) + y * I - ζ₀‖ := by linarith
      calc 1 / w ≤ 1 / (‖(c : ℂ) + y * I - ζ₀‖ / 2) :=
            one_div_le_one_div_of_le (by positivity) hl
        _ = 2 * b := by rw [hb]; field_simp
    have hinvδ : 1 / w ≤ 1 / δ := one_div_le_one_div_of_le hδ0 hl3
    have hG1 := hlogb y x.2 (by linarith)
    have hG2 := hGd' y x.2 h2
    have hnorm : ‖g' x y‖ ≤ ‖G y x.2‖ / w ^ 2 + ‖deriv (G y) x.2‖ / w := by
      simp only [hg']
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, norm_div, norm_pow, ← hw]
        exact mul_le_of_le_one_right (by positivity) (ContinuousLinearMap.norm_fst_le ℂ ℂ ℂ)
      · rw [norm_smul, norm_div, ← hw]
        exact mul_le_of_le_one_right (by positivity) (ContinuousLinearMap.norm_snd_le ℂ ℂ ℂ)
    have hb2 : b ^ 2 = ((y - ζ₀.im) ^ 2 + (c - ζ₀.re) ^ 2)⁻¹ := by
      rw [hb, one_div, inv_pow, norm_line_sub_sq]
    have he2 : e ^ 2 = ((y - 0) ^ 2 + c ^ 2)⁻¹ := by
      rw [he, one_div, inv_pow, norm_line_sq]
    have hlb : cepsLineBound ρW c ζ₀ y = a ^ 2 + b ^ 2 + e ^ 2 := by
      rw [cepsLineBound, hb2, he2]
    have hamgm : (a + e) * b ≤ a ^ 2 + b ^ 2 + e ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (e - b), sq_nonneg a, sq_nonneg e]
    have t1 : ‖G y x.2‖ / w ^ 2 ≤ dom.CL * (a + e) * (2 * b) * (1 / δ) := by
      rw [div_eq_mul_one_div, show 1 / w ^ 2 = (1 / w) * (1 / w) by ring]
      have : 1 / w * (1 / w) ≤ 2 * b * (1 / δ) :=
        mul_le_mul hinv hinvδ (by positivity) (by positivity)
      calc ‖G y x.2‖ * (1 / w * (1 / w)) ≤ dom.CL * (a + e) * (2 * b * (1 / δ)) :=
            mul_le_mul hG1 this (by positivity) (by positivity)
        _ = _ := by ring
    have t2 : ‖deriv (G y) x.2‖ / w ≤ dom.CL * (a + e) * (2 * b) * (1 / δ) := by
      rw [div_eq_mul_one_div]
      calc ‖deriv (G y) x.2‖ * (1 / w) ≤ dom.CL * (a + e) / δ * (2 * b) :=
            mul_le_mul hG2 hinv (by positivity) (by positivity)
        _ = _ := by ring
    calc ‖g' x y‖ ≤ ‖G y x.2‖ / w ^ 2 + ‖deriv (G y) x.2‖ / w := hnorm
      _ ≤ 4 * dom.CL / δ * ((a + e) * b) := by
          have := add_le_add t1 t2
          have e2 : dom.CL * (a + e) * (2 * b) * (1 / δ) + dom.CL * (a + e) * (2 * b) * (1 / δ) =
              4 * dom.CL / δ * ((a + e) * b) := by field_simp; ring
          linarith
      _ ≤ 4 * dom.CL / δ * (a ^ 2 + b ^ 2 + e ^ 2) :=
          mul_le_mul_of_nonneg_left hamgm (by positivity)
      _ = bound y := by
          show _ = 4 * dom.CL / δ * cepsLineBound ρW c ζ₀ y
          rw [hlb]
  -- measurability of `g' x₀`
  have hGcont : ∀ q : ℂ, ‖q‖ ≤ dom.q₀ → Continuous fun y => G y q := fun q hq =>
    dom.continuous_logF_line hW hθ hD hγ1 hγ2 hc1 hc2 hμ hμη hq
  have hden : Continuous fun y : ℝ => (c : ℂ) + y * I - ζ₀ := by fun_prop
  have hden0 : ∀ y : ℝ, (c : ℂ) + y * I - ζ₀ ≠ 0 := by
    intro y h0; have := hlow y; rw [h0, norm_zero] at this; linarith
  have hmeasA : AEStronglyMeasurable (fun y : ℝ =>
      G y q₀' / ((c : ℂ) + y * I - ζ₀) ^ 2) volume :=
    ((hGcont q₀' hq₀'.le).div (hden.pow 2) (fun y => pow_ne_zero 2 (hden0 y))).aestronglyMeasurable
  have hmeasD : AEStronglyMeasurable (fun y : ℝ => deriv (G y) q₀') volume := by
    refine aestronglyMeasurable_deriv_param (h := fun n : ℕ => ((δ / (n + 1) : ℝ) : ℂ))
      (fun n => ofReal_ne_zero.mpr (by positivity)) ?_
      (fun n => (hGcont _ ?_).aestronglyMeasurable)
      (hGcont q₀' hq₀'.le).aestronglyMeasurable (fun y => hGd y q₀' hq₀'.le)
    · have h2 : Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have h3 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ
        rw [mul_zero] at h3
        refine h3.congr fun n => ?_
        rw [mul_one_div]
      have h4 := (continuous_ofReal.tendsto 0).comp h2
      rw [ofReal_zero] at h4
      exact h4
    · have hn : ‖((δ / (n + 1) : ℝ) : ℂ)‖ ≤ δ := by
        rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        exact div_le_self hδ0.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      calc ‖q₀' + ((δ / (n + 1) : ℝ) : ℂ)‖ ≤ ‖q₀'‖ + δ := (norm_add_le _ _).trans (by linarith)
        _ ≤ dom.q₀ := by linarith
  have hmeasB : AEStronglyMeasurable (fun y : ℝ =>
      deriv (G y) q₀' / ((c : ℂ) + y * I - ζ₀)) volume :=
    hmeasD.mul ((hden.inv₀ hden0).aestronglyMeasurable) |>.congr (Eventually.of_forall
      fun y => by simp [div_eq_mul_inv])
  have hmeas' : AEStronglyMeasurable (g' x₀) volume := by
    have := (hmeasA.smul_const (ContinuousLinearMap.fst ℂ ℂ ℂ)).add
      (hmeasB.smul_const (ContinuousLinearMap.snd ℂ ℂ ℂ))
    exact this
  have hmain := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume) (F := g) (F' := g')
    (bound := bound) (x₀ := x₀) (ball_mem_nhds x₀ hδ0)
    (Filter.eventually_of_mem (ball_mem_nhds x₀ hδ0) fun x hx => ?_) ?_ hmeas'
    (Eventually.of_forall fun y x hx => hderiv_bound y x hx) (hB.const_mul _)
    (Eventually.of_forall fun y x hx => hderiv y x hx)
  · -- conclude
    have hlog : DifferentiableAt ℂ (fun x : ℂ × ℂ => Complex.log ((γ : ℂ) - x.1)) x₀ := by
      have hslit : (γ : ℂ) - ζ₀ ∈ slitPlane := by
        left; rw [sub_re, ofReal_re]
        have : c ≤ 2 * dom.c₀ := hc2
        have : dom.c₀ ≤ 1 / 1000 := by have := dom.c₀_le; have := dom.ρA_one; linarith
        linarith
      exact ((differentiableAt_const _).sub differentiableAt_fst).clog hslit
    have e : (fun x : ℂ × ℂ => cepsCanonL D θ ρW γ c μ x.2 x.1) =
        fun x => (2 * Real.pi : ℂ)⁻¹ * (∫ y, g x y) - Complex.log ((γ : ℂ) - x.1) := by
      funext x; rw [cepsCanonL_eq, ← hgeq x]
    rw [e]
    exact ((hmain.differentiableAt.const_mul _).sub hlog).differentiableWithinAt
  · obtain ⟨h1, h2, -⟩ := hball x hx
    have h := (dom.continuous_lineIntegrand hW hθ hD hγ1 hγ2 hc1 hc2 hμ hμη (q := x.2)
      (ζ := x.1) (by linarith) (by linarith)).aestronglyMeasurable (μ := volume)
    rw [← hgeq x] at h
    exact h
  · have h := dom.integrable_cepsCanonL_integrand hW hθ hD hγ1 hγ2 hc1 hc2 hμ hμη hq₀'.le hζ₀
    rw [← hgeq x₀] at h
    exact h


set_option maxHeartbeats 1000000 in
/-- **C-3(a): continuity in the real drift.** -/
theorem continuousOn_cepsCanonL_mu {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c : ℝ}
    (hc1 : dom.c₀ ≤ c) (hc2 : c ≤ 2 * dom.c₀) {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < c) :
    ContinuousOn (fun t : ℝ => cepsCanonL D θ ρW γ c t q ζ) (Icc (-dom.μ₀) dom.μ₀) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hμt : ∀ t ∈ Icc (-dom.μ₀) dom.μ₀, ‖(t : ℂ)‖ ≤ dom.μ₀ := by
    intro t ht; rw [norm_real, Real.norm_eq_abs]; exact abs_le.mpr ht
  obtain ⟨hB, -⟩ := integrable_cepsLineBound hW hθ hD (c := c) (by linarith) (by linarith) hζ
  have hint : ContinuousOn (fun t : ℝ => ∫ y, cepsLineIntegrand D θ ρW γ c t q ζ y)
      (Icc (-dom.μ₀) dom.μ₀) := by
    refine continuousOn_of_dominated (bound := fun y => dom.CL * cepsLineBound ρW c ζ y)
      (fun t ht => (dom.continuous_lineIntegrand hW hθ hD hγ1 hγ2 hc1 hc2 (hμt t ht)
        (by simp) hq hζ).aestronglyMeasurable)
      (fun t ht => Eventually.of_forall fun y => dom.norm_lineIntegrand_le hW hθ hD hγ1 hγ2
        hc1 hc2 (hμt t ht) (by simp; exact dom.η_pos.le) hq hζ)
      (hB.const_mul _) (Eventually.of_forall fun y => ?_)
    intro t ht
    set z : ℂ := c + y * I with hz
    have hzre : z.re = c := by simp [hz]
    have hzn : dom.c₀ / 2 ≤ ‖z‖ := by have := re_le_norm z; rw [hzre] at this; linarith
    have hF := dom.continuousAt_cepsF_mu hW hθ hD (γ := γ) (hμt t ht) hq hzn
      (by rw [hzre, abs_of_pos (by linarith)]; linarith)
    obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 (ζ := z) (hμt t ht)
      (by simp; exact dom.η_pos.le) hq
      (by rw [hzre, abs_of_pos (by linarith)]; exact hc1)
      (by rw [hzre, abs_of_pos (by linarith)]; exact hc2)
    have hslit : cepsF D θ ρW γ (t : ℂ) q z ∈ slitPlane :=
      Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre)
    have hpair : ContinuousAt (fun t : ℝ => (((t : ℂ), z) : ℂ × ℂ)) t := by fun_prop
    have h1 : ContinuousAt ((fun x : ℂ × ℂ => cepsF D θ ρW γ x.1 q x.2) ∘
        (fun t : ℝ => (((t : ℂ), z) : ℂ × ℂ))) t := ContinuousAt.comp hF hpair
    have h2 := (h1.clog hslit).div (continuousAt_const (y := z - ζ)) (by
      intro h0; have := congrArg re h0; rw [sub_re, hzre, zero_re] at this; linarith)
    exact h2.continuousWithinAt
  have e : (fun t : ℝ => cepsCanonL D θ ρW γ c t q ζ) = fun t : ℝ =>
      (2 * Real.pi : ℂ)⁻¹ * (∫ y, cepsLineIntegrand D θ ρW γ c t q ζ y) -
        Complex.log (γ - ζ) := by
    funext t; rfl
  rw [e]
  exact (hint.const_smul ((2 * Real.pi : ℂ)⁻¹)).sub continuousOn_const

set_option maxHeartbeats 1000000 in
/-- Horizontal edges of the strip between two lines. -/
theorem norm_edge_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c c' : ℝ}
    (hc1 : dom.c₀ ≤ c) (hcc : c ≤ c') (hc2 : c' ≤ 2 * dom.c₀) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (T : ℝ)
    (hT : ‖ζ‖ + 1 ≤ abs T) :
    ‖∫ σ in c..c', Complex.log (cepsF D θ ρW γ μ q (σ + T * I)) / ((σ : ℂ) + T * I - ζ)‖ ≤
      dom.CL * ((2 + 128 * D / θ) + 1 / dom.c₀) / (abs T - ‖ζ‖) * abs (c' - c) := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  have hCL : 0 ≤ dom.CL := by unfold CL Linf; have := dom.ρA_pos; positivity
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
  rw [uIoc_of_le hcc] at hσ
  set z : ℂ := σ + T * I with hz
  have hzre : z.re = σ := by simp [hz]
  have hzim : z.im = T := by simp [hz]
  have hlog := dom.norm_log_cepsF_le hW hθ hD hγ1 hγ2 (ζ := z) hμ
    (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq
    (by rw [hzre, abs_of_pos (by linarith [hσ.1])]; linarith [hσ.1])
    (by rw [hzre, abs_of_pos (by linarith [hσ.1])]; linarith [hσ.2])
  have hM : ‖stepTransform ρW z‖ ≤ 2 + 128 * D / θ :=
    norm_stepTransform_le_strip hW hθ hD.le (by rw [hzre, abs_of_pos (by linarith [hσ.1])]; linarith [hσ.2])
  have hz1 : 1 / ‖z‖ ≤ 1 / dom.c₀ := by
    apply one_div_le_one_div_of_le hc0
    have := re_le_norm z; rw [hzre] at this; linarith [hσ.1]
  have hzζ : abs T - ‖ζ‖ ≤ ‖z - ζ‖ := by
    have h1 := abs_im_le_norm (z - ζ)
    rw [sub_im, hzim] at h1
    have h2 := abs_im_le_norm ζ
    have h3 : abs T - abs ζ.im ≤ abs (T - ζ.im) := abs_sub_abs_le_abs_sub T ζ.im
    linarith
  have hpos : 0 < abs T - ‖ζ‖ := by linarith
  have hlog' : ‖Complex.log (cepsF D θ ρW γ μ q z)‖ ≤ dom.CL * ((2 + 128 * D / θ) + 1 / dom.c₀) :=
    hlog.trans (mul_le_mul_of_nonneg_left (add_le_add hM hz1) hCL)
  rw [norm_div, div_le_div_iff₀ (by linarith) hpos]
  exact mul_le_mul hlog' hzζ hpos.le (by positivity)

set_option maxHeartbeats 1000000 in
/-- **C-3(a): independence of the abscissa.** For `c ≤ c'` in `[c₀, 2c₀]` and `Re ζ < c`, the
two contour integrals agree. -/
theorem cepsCanonL_eq_of_abscissa {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c c' : ℝ}
    (hc1 : dom.c₀ ≤ c) (hcc : c ≤ c') (hc2 : c' ≤ 2 * dom.c₀) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : μ.im = 0) (hq : ‖q‖ ≤ dom.q₀) (hζ : ζ.re < c) :
    cepsCanonL D θ ρW γ c μ q ζ = cepsCanonL D θ ρW γ c' μ q ζ := by
  have hc0 := dom.c₀_pos
  have hθc := dom.two_c₀_lt
  set f : ℂ → ℂ := fun z => Complex.log (cepsF D θ ρW γ μ q z) / (z - ζ) with hf
  have hstrip : ∀ z : ℂ, z.re ∈ Icc c c' →
      DifferentiableAt ℂ f z := by
    intro z hz
    have hzn : dom.c₀ / 2 ≤ ‖z‖ := by have := re_le_norm z; linarith [hz.1]
    have hF := dom.differentiableAt_cepsF_z hW hθ hD (γ := γ) hμ hq hzn
      (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2])
    obtain ⟨hre, -⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 (ζ := z) hμ
      (by rw [hμη, abs_zero, zero_mul]; exact dom.η_pos.le) hq
      (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.1])
      (by rw [abs_of_pos (by linarith [hz.1])]; linarith [hz.2])
    have hslit : cepsF D θ ρW γ μ q z ∈ slitPlane := Or.inl (lt_of_lt_of_le (dom.d₀_pos hD) hre)
    have hne : z - ζ ≠ 0 := by
      intro h0; have := congrArg re h0; rw [sub_re, zero_re] at this; linarith [hz.1]
    exact (hF.clog hslit).div (differentiableAt_id.sub_const ζ) hne
  have hline : ∀ a : ℝ, dom.c₀ ≤ a → a ≤ 2 * dom.c₀ → ζ.re < a →
      Integrable fun t : ℝ => f (a + t * I) := fun a ha1 ha2 haζ =>
    dom.integrable_cepsCanonL_integrand hW hθ hD hγ1 hγ2 ha1 ha2 hμ hμη hq haζ
  set CM : ℝ := 2 + 128 * D / θ with hCM
  have hedge := dom.norm_edge_le hW hθ hD hγ1 hγ2 hc1 hcc hc2 hμ hμη hq (ζ := ζ)
  have hlim : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
      Tendsto (fun k : ℕ => ∫ σ in c..c', f (σ + ((sgn * (k + ‖ζ‖ + 1) : ℝ) : ℂ) * I)) atTop
        (𝓝 0) := by
    intro sgn hsgn
    have habs : ∀ k : ℕ, |sgn * ((k : ℝ) + ‖ζ‖ + 1)| = (k : ℝ) + ‖ζ‖ + 1 := by
      intro k
      have hp : (0 : ℝ) < k + ‖ζ‖ + 1 := by positivity
      rcases hsgn with h | h
      · rw [h, one_mul, abs_of_pos hp]
      · rw [h, neg_one_mul, abs_neg, abs_of_pos hp]
    refine squeeze_zero_norm (a := fun k : ℕ =>
      dom.CL * (CM + 1 / dom.c₀) / ((k : ℝ) + 1) * (abs (c' - c))) (fun k => ?_) ?_
    · have := hedge (sgn * ((k : ℝ) + ‖ζ‖ + 1)) (by rw [habs k]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      rw [habs k] at this
      convert this using 2; ring
    · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (h1.const_mul (dom.CL * (CM + 1 / dom.c₀))).mul_const (abs (c' - c))
      simp only [mul_zero, zero_mul] at h2
      refine h2.congr fun k => ?_
      ring
  have hT : Tendsto (fun k : ℕ => ((k : ℝ) + ‖ζ‖ + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hvert : (∫ t : ℝ, f (c + t * I)) = ∫ t : ℝ, f (c' + t * I) := by
    refine integral_vertical_eq_of_tendsto (f := f) hcc ?_ ?_
      (hline c hc1 (by linarith) hζ) (hline c' (by linarith) hc2 (by linarith)) hT hT ?_ ?_
    · exact fun z hz => (hstrip z hz).continuousAt.continuousWithinAt
    · exact fun z hz => hstrip z ⟨hz.1.le, hz.2.le⟩
    · have h := hlim 1 (Or.inl rfl)
      simp only [one_mul] at h
      exact h
    · have h := hlim (-1) (Or.inr rfl)
      simp only [neg_one_mul, ofReal_neg] at h
      refine h.congr fun k => ?_
      push_cast
      ring_nf
  rw [cepsCanonL_eq, cepsCanonL_eq]
  have e1 : (∫ y : ℝ, cepsLineIntegrand D θ ρW γ c μ q ζ y) = ∫ t : ℝ, f (c + t * I) := rfl
  have e2 : (∫ y : ℝ, cepsLineIntegrand D θ ρW γ c' μ q ζ y) = ∫ t : ℝ, f (c' + t * I) := rfl
  rw [e1, e2, hvert]

end

end CepsCanonDomain

end PGM
