import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LargeDeviation
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Holomorphic
import PLAStochastic.ForMathlib.Analysis.Complex.CauchyBound
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# CEPS WP3: the cumulant generating function on the step class

For a centred step law `ρW` in the class `IsStepLaw ρW fW D θ v` (density `f_W ≤ D e^{-θ|x|}`,
mean zero, `E W² ≤ v`) let `M₀ = stepTransform ρW` and `ψ₀ = cepsCgf ρW = log M₀`. With the
class radius `r₀ = cepsCgfRadius D θ = min (θ/4) (θ²/(128 D))`:

* `norm_stepTransform_sub_one_le`: `‖M₀(ζ) - 1‖ ≤ (256 D/θ³) ‖ζ‖²` for `‖ζ‖ ≤ θ/2`;
* `differentiableOn_stepTransform_ball`: `M₀` is holomorphic on `B(0, θ/2)`;
* `differentiableOn_cepsCgf`, `norm_cepsCgf_le`: `ψ₀` is holomorphic on `B(0, r₀)`, `‖ψ₀‖ ≤ 3/4`;
* `cepsCgf_zero`, `deriv_cepsCgf_zero`, `deriv_deriv_cepsCgf_zero`:
  `ψ₀(0) = 0`, `ψ₀'(0) = 0`, `ψ₀''(0) = E W² = cepsStepVar ρW`;
* `cepsStepVar_ge`, `cepsStepVar_le`: `1/(256 D²) ≤ E W² ≤ v` (the lower bound follows from the
  density bound; no variance lower bound is assumed);
* `norm_deriv3_cepsCgf_le`: `‖ψ₀'''‖ ≤ 288/r₀³` on `B(0, r₀/2)`;
* `norm_deriv2_cepsCgf_sub_le`: `‖ψ₀''(ζ) - E W²‖ ≤ (288/r₀³) ‖ζ‖` on `B(0, r₀/2)`.

All constants depend only on `(D, θ)` (and `v` for the upper variance bound).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `ψ₀ = log M₀`, the (principal) cumulant generating function of the step law. -/
def cepsCgf (ρW : Measure ℝ) (ζ : ℂ) : ℂ := Complex.log (stepTransform ρW ζ)

/-- The step variance `E W²`. -/
def cepsStepVar (ρW : Measure ℝ) : ℝ := ∫ x, x ^ 2 ∂ρW

/-- The class radius `r₀ = min (θ/4) (θ²/(128 D))` on which `‖M₀ - 1‖ ≤ 1/2`. -/
def cepsCgfRadius (D θ : ℝ) : ℝ := min (θ / 4) (θ ^ 2 / (128 * D))

theorem cepsCgfRadius_pos {D θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsCgfRadius D θ :=
  lt_min (by positivity) (by positivity)

theorem cepsCgfRadius_le {D θ : ℝ} : cepsCgfRadius D θ ≤ θ / 4 := min_le_left _ _

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

theorem stepLaw_integrable_exp_abs (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) :
    Integrable (fun w => Real.exp (θ / 2 * |w|)) ρW := by
  have h1 := (hW.integral_exp_le hθ hD (t := θ / 2) (by rw [abs_of_pos (by positivity)])).1
  have h2 := (hW.integral_exp_le hθ hD (t := -(θ / 2))
    (by rw [abs_neg, abs_of_pos (by positivity)])).1
  refine (h1.add h2).mono' (by fun_prop) (Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Pi.add_apply]
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw]; linarith [Real.exp_pos (-(θ / 2) * w)]
  · rw [abs_of_nonpos hw, show θ / 2 * -w = -(θ / 2) * w by ring]
    linarith [Real.exp_pos (θ / 2 * w)]

theorem stepLaw_integrable_cexp (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) {ζ : ℂ}
    (hζ : |ζ.re| ≤ θ / 2) : Integrable (fun w : ℝ => cexp (ζ * w)) ρW := by
  refine (stepLaw_integrable_exp_abs hW hθ hD).mono' (by fun_prop) (Eventually.of_forall fun w => ?_)
  rw [Complex.norm_exp]
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  apply Real.exp_le_exp.mpr
  calc ζ.re * w ≤ |ζ.re * w| := le_abs_self _
    _ = |ζ.re| * |w| := abs_mul _ _
    _ ≤ θ / 2 * |w| := mul_le_mul_of_nonneg_right hζ (abs_nonneg w)

theorem stepLaw_mem_interior_integrableExpSet (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D)
    {t : ℝ} (ht : |t| < θ / 2) : t ∈ interior (integrableExpSet id ρW) := by
  have hsub : Ioo (-(θ / 2)) (θ / 2) ⊆ integrableExpSet id ρW := by
    intro s hs
    have : |s| ≤ θ / 2 := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
    exact (hW.integral_exp_le hθ hD this).1
  exact interior_mono hsub (by rw [interior_Ioo]; exact abs_lt.mp ht)

/-- `M₀` is holomorphic on `B(0, θ/2)`. -/
theorem differentiableOn_stepTransform_ball (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 ≤ D) : DifferentiableOn ℂ (stepTransform ρW) (ball 0 (θ / 2)) := by
  intro ζ hζ
  have hre : |ζ.re| < θ / 2 := by
    rw [mem_ball, dist_zero_right] at hζ
    exact (abs_re_le_norm ζ).trans_lt hζ
  have h := ProbabilityTheory.hasDerivAt_complexMGF (X := id) (μ := ρW) (z := ζ)
    (stepLaw_mem_interior_integrableExpSet hW hθ hD hre)
  exact h.differentiableAt.differentiableWithinAt

/-- `‖M₀(ζ) - 1‖ ≤ (256 D/θ³) ‖ζ‖²` for `‖ζ‖ ≤ θ/2`. -/
theorem norm_stepTransform_sub_one_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ θ / 2) :
    ‖stepTransform ρW ζ - 1‖ ≤ 256 * D / θ ^ 3 * ‖ζ‖ ^ 2 := by
  have := hW.isProbabilityMeasure
  have hre : |ζ.re| ≤ θ / 2 := (abs_re_le_norm ζ).trans hζ
  have hi := stepLaw_integrable_cexp hW hθ hD hre
  have hid : Integrable (fun w : ℝ => ζ * (w : ℂ)) ρW :=
    (hW.integrable_id.ofReal).const_mul ζ
  obtain ⟨hKi, hK⟩ := hW.integral_sq_mul_exp_le hθ hD
  have e : ∫ w, (cexp (ζ * w) - 1 - ζ * w) ∂ρW = stepTransform ρW ζ - 1 := by
    have h1 : ∫ w, (cexp (ζ * w) - 1 - ζ * w) ∂ρW =
        ∫ w, (cexp (ζ * w) - 1) ∂ρW - ∫ w : ℝ, ζ * (w : ℂ) ∂ρW :=
      integral_sub (hi.sub (integrable_const 1)) hid
    have h2 : ∫ w, (cexp (ζ * w) - 1) ∂ρW = ∫ w, cexp (ζ * w) ∂ρW - ∫ _ : ℝ, (1 : ℂ) ∂ρW :=
      integral_sub hi (integrable_const 1)
    have h3 : ∫ w : ℝ, ζ * (w : ℂ) ∂ρW = 0 := by
      rw [integral_const_mul]
      have e : ∫ x : ℝ, (x : ℂ) ∂ρW = ((∫ x, x ∂ρW : ℝ) : ℂ) := integral_ofReal
      rw [e, hW.integral_id]; simp
    rw [h1, h2, h3]
    simp [stepTransform]
  rw [← e]
  have hpt : ∀ w : ℝ, ‖cexp (ζ * w) - 1 - ζ * w‖ ≤ ‖ζ‖ ^ 2 * (w ^ 2 * Real.exp (θ / 2 * |w|)) := by
    intro w
    have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (ζ * w) 2
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, pow_zero,
      Nat.factorial, Nat.cast_one, div_one, zero_add, pow_one, Nat.succ_eq_add_one,
      Nat.mul_one] at h
    have h' : ‖cexp (ζ * w) - 1 - ζ * w‖ ≤ ‖ζ * w‖ ^ 2 * Real.exp ‖ζ * w‖ := by
      convert h using 2; ring
    have hn : ‖ζ * (w : ℂ)‖ = ‖ζ‖ * |w| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [hn] at h'
    calc ‖cexp (ζ * w) - 1 - ζ * w‖ ≤ (‖ζ‖ * |w|) ^ 2 * Real.exp (‖ζ‖ * |w|) := h'
      _ ≤ (‖ζ‖ * |w|) ^ 2 * Real.exp (θ / 2 * |w|) := by
          gcongr
      _ = ‖ζ‖ ^ 2 * (w ^ 2 * Real.exp (θ / 2 * |w|)) := by rw [mul_pow, sq_abs]; ring
  calc ‖∫ w, (cexp (ζ * w) - 1 - ζ * w) ∂ρW‖
      ≤ ∫ w, ‖ζ‖ ^ 2 * (w ^ 2 * Real.exp (θ / 2 * |w|)) ∂ρW :=
        norm_integral_le_of_norm_le (hKi.const_mul _) (Eventually.of_forall hpt)
    _ = ‖ζ‖ ^ 2 * ∫ w, w ^ 2 * Real.exp (θ / 2 * |w|) ∂ρW := integral_const_mul _ _
    _ ≤ ‖ζ‖ ^ 2 * (256 * D / θ ^ 3) := by gcongr
    _ = 256 * D / θ ^ 3 * ‖ζ‖ ^ 2 := by ring

theorem norm_stepTransform_sub_one_le_half (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {ζ : ℂ} (hζ : ‖ζ‖ ≤ cepsCgfRadius D θ) :
    ‖stepTransform ρW ζ - 1‖ ≤ 1 / 2 := by
  have h1 : ‖ζ‖ ≤ θ / 4 := hζ.trans cepsCgfRadius_le
  have h2 : ‖ζ‖ ≤ θ ^ 2 / (128 * D) := hζ.trans (min_le_right _ _)
  have h := norm_stepTransform_sub_one_le hW hθ hD.le (ζ := ζ) (by linarith)
  refine h.trans ?_
  have hsq : ‖ζ‖ ^ 2 ≤ θ / 4 * (θ ^ 2 / (128 * D)) := by
    rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  calc 256 * D / θ ^ 3 * ‖ζ‖ ^ 2 ≤ 256 * D / θ ^ 3 * (θ / 4 * (θ ^ 2 / (128 * D))) := by
        gcongr
    _ = 1 / 2 := by field_simp; ring

theorem stepTransform_mem_slitPlane (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ)
    (hD : 0 < D) {ζ : ℂ} (hζ : ‖ζ‖ ≤ cepsCgfRadius D θ) :
    stepTransform ρW ζ ∈ slitPlane := by
  have h := norm_stepTransform_sub_one_le_half hW hθ hD hζ
  have hre : (1 : ℝ) / 2 ≤ (stepTransform ρW ζ).re := by
    have := (abs_re_le_norm (stepTransform ρW ζ - 1)).trans h
    rw [sub_re, one_re] at this
    linarith [neg_abs_le ((stepTransform ρW ζ).re - 1)]
  exact Or.inl (by linarith)

/-- `ψ₀` is holomorphic on `B(0, r₀)`. -/
theorem differentiableOn_cepsCgf (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) :
    DifferentiableOn ℂ (cepsCgf ρW) (ball 0 (cepsCgfRadius D θ)) := by
  intro ζ hζ
  have hζ' : ‖ζ‖ < cepsCgfRadius D θ := by rwa [mem_ball, dist_zero_right] at hζ
  have hθ2 : ζ ∈ ball (0 : ℂ) (θ / 2) := by
    rw [mem_ball, dist_zero_right]
    have := cepsCgfRadius_le (D := D) (θ := θ)
    linarith
  have hM := (differentiableOn_stepTransform_ball hW hθ hD.le ζ hθ2).differentiableAt
    (isOpen_ball.mem_nhds hθ2)
  exact (hM.clog (stepTransform_mem_slitPlane hW hθ hD hζ'.le)).differentiableWithinAt

/-- `‖ψ₀‖ ≤ 3/4` on `B(0, r₀)`. -/
theorem norm_cepsCgf_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ cepsCgfRadius D θ) : ‖cepsCgf ρW ζ‖ ≤ 3 / 4 := by
  have h := norm_stepTransform_sub_one_le_half hW hθ hD hζ
  have := Complex.norm_log_one_add_half_le_self h
  rw [add_sub_cancel] at this
  unfold cepsCgf
  linarith

theorem stepTransform_zero (hW : IsStepLaw ρW fW D θ v) : stepTransform ρW 0 = 1 := by
  have := hW.isProbabilityMeasure
  simp [stepTransform]

theorem cepsCgf_zero (hW : IsStepLaw ρW fW D θ v) : cepsCgf ρW 0 = 0 := by
  simp [cepsCgf, stepTransform_zero hW]

theorem hasDerivAt_cepsCgf (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) {ζ : ℂ}
    (hζ : ‖ζ‖ < cepsCgfRadius D θ) :
    HasDerivAt (cepsCgf ρW) (deriv (stepTransform ρW) ζ / stepTransform ρW ζ) ζ := by
  have hθ2 : ζ ∈ ball (0 : ℂ) (θ / 2) := by
    rw [mem_ball, dist_zero_right]
    have := cepsCgfRadius_le (D := D) (θ := θ)
    linarith
  have hM := (differentiableOn_stepTransform_ball hW hθ hD.le ζ hθ2).differentiableAt
    (isOpen_ball.mem_nhds hθ2)
  exact hM.hasDerivAt.clog (stepTransform_mem_slitPlane hW hθ hD hζ.le)

theorem deriv_stepTransform_zero (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) :
    deriv (stepTransform ρW) 0 = 0 := by
  have h := ProbabilityTheory.hasDerivAt_complexMGF (X := id) (μ := ρW) (z := 0)
    (stepLaw_mem_interior_integrableExpSet hW hθ hD (by simp; positivity))
  rw [show stepTransform ρW = complexMGF id ρW from rfl, h.deriv]
  simp only [id, zero_mul, Complex.exp_zero, mul_one]
  have e : ∫ x : ℝ, (x : ℂ) ∂ρW = ((∫ x, x ∂ρW : ℝ) : ℂ) := integral_ofReal
  rw [e, hW.integral_id, ofReal_zero]

theorem deriv_deriv_stepTransform_zero (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 ≤ D) :
    deriv (deriv (stepTransform ρW)) 0 = cepsStepVar ρW := by
  have h := ProbabilityTheory.iteratedDeriv_complexMGF (X := id) (μ := ρW) (z := 0)
    (stepLaw_mem_interior_integrableExpSet hW hθ hD (by simp; positivity)) 2
  rw [iteratedDeriv_succ, iteratedDeriv_one] at h
  rw [show stepTransform ρW = complexMGF id ρW from rfl, h]
  simp only [id, zero_mul, Complex.exp_zero, mul_one]
  have e : ∫ x : ℝ, ((x ^ 2 : ℝ) : ℂ) ∂ρW = ((∫ x, x ^ 2 ∂ρW : ℝ) : ℂ) := integral_ofReal
  rw [show (fun x : ℝ => (x : ℂ) ^ 2) = fun x : ℝ => ((x ^ 2 : ℝ) : ℂ) by
    funext x; push_cast; ring, e]
  rfl

theorem deriv_cepsCgf_zero (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) :
    deriv (cepsCgf ρW) 0 = 0 := by
  rw [(hasDerivAt_cepsCgf hW hθ hD (by simpa using cepsCgfRadius_pos hD hθ)).deriv,
    deriv_stepTransform_zero hW hθ hD.le, zero_div]

theorem deriv_deriv_cepsCgf_zero (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) :
    deriv (deriv (cepsCgf ρW)) 0 = cepsStepVar ρW := by
  have hr := cepsCgfRadius_pos hD hθ
  have hev : deriv (cepsCgf ρW) =ᶠ[𝓝 0]
      fun ζ => deriv (stepTransform ρW) ζ / stepTransform ρW ζ := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with ζ hζ
    rw [mem_ball, dist_zero_right] at hζ
    exact (hasDerivAt_cepsCgf hW hθ hD hζ).deriv
  rw [hev.deriv_eq]
  have hθ2 : (0 : ℂ) ∈ ball (0 : ℂ) (θ / 2) := mem_ball_self (by positivity)
  have hdiff := differentiableOn_stepTransform_ball hW hθ hD.le
  have h1 : HasDerivAt (stepTransform ρW) (deriv (stepTransform ρW) 0) 0 :=
    (hdiff 0 hθ2).differentiableAt (isOpen_ball.mem_nhds hθ2) |>.hasDerivAt
  have h2 : HasDerivAt (deriv (stepTransform ρW)) (deriv (deriv (stepTransform ρW)) 0) 0 :=
    ((hdiff.deriv isOpen_ball) 0 hθ2).differentiableAt (isOpen_ball.mem_nhds hθ2) |>.hasDerivAt
  have h3 := h2.div h1 (by rw [stepTransform_zero hW]; exact one_ne_zero)
  rw [show (fun ζ => deriv (stepTransform ρW) ζ / stepTransform ρW ζ) =
    deriv (stepTransform ρW) / stepTransform ρW from rfl, h3.deriv,
    deriv_deriv_stepTransform_zero hW hθ hD.le, deriv_stepTransform_zero hW hθ hD.le,
    stepTransform_zero hW]
  simp

theorem cepsStepVar_le (hW : IsStepLaw ρW fW D θ v) : cepsStepVar ρW ≤ v := hW.integral_sq_le

/-- The density bound forces `E W² ≥ 1/(256 D²)`. -/
theorem cepsStepVar_ge (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) :
    1 / (256 * D ^ 2) ≤ cepsStepVar ρW := by
  have := hW.isProbabilityMeasure
  set m : ℝ := ∫ x, max x 0 ∂ρW with hm
  have hm16 : 1 / (16 * D) ≤ m := hW.integral_pos_part_ge hθ.le hD
  have hmpos : 0 ≤ m := le_trans (by positivity) hm16
  have hpt : ∀ x : ℝ, 2 * m * max x 0 - m ^ 2 ≤ x ^ 2 := by
    intro x
    have : (max x 0) ^ 2 ≤ x ^ 2 := by
      rcases le_total x 0 with h | h
      · rw [max_eq_right h]; nlinarith [sq_nonneg x]
      · rw [max_eq_left h]
    nlinarith [sq_nonneg (max x 0 - m)]
  have hint : Integrable (fun x : ℝ => max x 0) ρW :=
    (hW.integrable_id.abs).mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have h := integral_mono (f := fun x => 2 * m * max x 0 - m ^ 2)
    ((hint.const_mul (2 * m)).sub (integrable_const (m ^ 2))) hW.integrable_sq hpt
  have h' : ∫ x, (2 * m * max x 0 - m ^ 2) ∂ρW = 2 * m * m - m ^ 2 := by
    rw [integral_sub (hint.const_mul (2 * m)) (integrable_const _), integral_const_mul,
      integral_const]
    simp [hm]
  rw [h'] at h
  unfold cepsStepVar
  have : 1 / (256 * D ^ 2) ≤ m ^ 2 := by
    have : (1 / (16 * D)) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ (by positivity) hm16 2
    calc 1 / (256 * D ^ 2) = (1 / (16 * D)) ^ 2 := by field_simp; ring
      _ ≤ m ^ 2 := this
  nlinarith

/-- `‖ψ₀'''‖ ≤ 288/r₀³` on `B(0, r₀/2)`. -/
theorem norm_deriv3_cepsCgf_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) (cepsCgfRadius D θ / 2)) :
    ‖deriv (deriv (deriv (cepsCgf ρW))) ζ‖ ≤ 288 / cepsCgfRadius D θ ^ 3 := by
  have hr := cepsCgfRadius_pos hD hθ
  have h := norm_iteratedDeriv_le_of_ball_half 3 hr (differentiableOn_cepsCgf hW hθ hD)
    (fun z hz => norm_cepsCgf_le hW hθ hD (by rw [mem_ball, dist_zero_right] at hz; exact hz.le))
    hζ
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at h
  calc _ ≤ (Nat.factorial 3) * (3 / 4) / (cepsCgfRadius D θ / 4) ^ 3 := h
    _ = 288 / cepsCgfRadius D θ ^ 3 := by simp [Nat.factorial]; field_simp; ring

/-- `‖ψ₀''(ζ) - E W²‖ ≤ (288/r₀³) ‖ζ‖` on `B(0, r₀/2)`. -/
theorem norm_deriv2_cepsCgf_sub_le (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
    {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) (cepsCgfRadius D θ / 2)) :
    ‖deriv (deriv (cepsCgf ρW)) ζ - cepsStepVar ρW‖ ≤ 288 / cepsCgfRadius D θ ^ 3 * ‖ζ‖ := by
  have hr := cepsCgfRadius_pos hD hθ
  have hsub : ball (0 : ℂ) (cepsCgfRadius D θ / 2) ⊆ ball 0 (cepsCgfRadius D θ) :=
    ball_subset_ball (by linarith)
  have hd2 : DifferentiableOn ℂ (deriv (deriv (cepsCgf ρW))) (ball 0 (cepsCgfRadius D θ)) :=
    ((differentiableOn_cepsCgf hW hθ hD).deriv isOpen_ball).deriv isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) (cepsCgfRadius D θ / 2) := mem_ball_self (by positivity)
  have := (convex_ball (0 : ℂ) (cepsCgfRadius D θ / 2)).norm_image_sub_le_of_norm_deriv_le
    (f := deriv (deriv (cepsCgf ρW)))
    (fun x hx => (hd2 x (hsub hx)).differentiableAt (isOpen_ball.mem_nhds (hsub hx)))
    (fun x hx => norm_deriv3_cepsCgf_le hW hθ hD hx) h0 hζ
  rw [deriv_deriv_cepsCgf_zero hW hθ hD, sub_zero] at this
  exact this

end PGM
