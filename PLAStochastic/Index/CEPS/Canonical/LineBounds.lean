import PLAStochastic.Index.CEPS.Canonical.Cumulant
import PLAStochastic.Index.GEP.OrbitClosure.SumDensity
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Plancherel

/-!
# CEPS WP3, lemma C-1: class-uniform bounds for `M₀` on vertical lines

For a step law in `IsStepLaw ρW fW D θ v` and `M₀ = stepTransform ρW`:

* `stepTransform_eq_integral`: `M₀(ζ) = ∫ e^{ζ x} f_W(x) dx`;
* `norm_stepTransform_I_le`: the class Fourier gap `‖M₀(i y)‖ ≤ 1 - cepsGap D v Y` for
  `|y| ≥ Y > 0`, from the existing `one_sub_norm_charFun_sq_ge` (bounded density, variance
  bounds `1/(256 D²) ≤ E W² ≤ v`);
* `norm_stepTransform_shift_le`: `‖M₀(c + i y) - M₀(i y)‖ ≤ |c| C_W` for `|c| ≤ θ/2`, with
  `C_W = cepsShiftConst D θ = 1 + 64 D/θ + 128 D/θ³`;
* `lintegral_norm_sq_stepTransform_le`: the line `L²` bound
  `∫ |M₀(c + i y)|² dy ≤ 2π · 2 D²/θ` for `|c| ≤ θ/2` (Plancherel for `e^{c x} f_W(x)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex Filter
open PGM.WienerHopf
open scoped ENNReal

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

/-- The class Fourier gap at frequency threshold `Y`. -/
def cepsGap (D v Y : ℝ) : ℝ := c0CharFn * min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) / (2 * D ^ 2 * v)

/-- `C_W = 1 + 64 D/θ + 128 D/θ³ ≥ E[|W| e^{θ|W|/2}]`. -/
def cepsShiftConst (D θ : ℝ) : ℝ := 1 + 64 * D / θ + 128 * D / θ ^ 3

theorem cepsGap_pos {Y : ℝ} (hD : 0 < D) (hv : 0 < v) (hY : 0 < Y) : 0 < cepsGap D v Y := by
  have := c0CharFn_pos
  unfold cepsGap
  have : 0 < min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) := lt_min one_pos (by positivity)
  positivity

theorem cepsShiftConst_pos (hD : 0 < D) (hθ : 0 < θ) : 0 < cepsShiftConst D θ := by
  unfold cepsShiftConst; positivity

section

variable (hW : IsStepLaw ρW fW D θ v)
include hW

theorem stepTransform_eq_integral (ζ : ℂ) :
    stepTransform ρW ζ = ∫ x, (fW x : ℂ) * cexp (ζ * x) := by
  rw [stepTransform, hW.eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (fW x))
      (ENNReal.measurable_ofReal.comp hW.measurable)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1; funext x
  rw [ENNReal.toReal_ofReal (hW.nonneg x), real_smul]

/-- A bounded density gives `LocBd D`. -/
theorem stepLaw_locBd (hθ : 0 ≤ θ) (hD : 0 ≤ D) : LocBd D ρW := by
  intro A hA
  rw [hW.eq_withDensity, withDensity_apply _ hA]
  calc ∫⁻ x in A, ENNReal.ofReal (fW x) ≤ ∫⁻ _ in A, ENNReal.ofReal D :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hW.le_D hθ hD x)
    _ = ENNReal.ofReal D * volume A := by rw [setLIntegral_const]

omit hW in
/-- The characteristic function is `M₀` on the imaginary axis. -/
theorem charFun_eq_stepTransform (y : ℝ) : charFun ρW y = stepTransform ρW (y * I) := by
  rw [charFun_apply_real, stepTransform]
  congr 1; funext x; congr 1; ring

/-- **Class Fourier gap.** `‖M₀(i y)‖ ≤ 1 - cepsGap D v Y` for `|y| ≥ Y > 0`. -/
theorem norm_stepTransform_I_le (hθ : 0 < θ) (hD : 0 < D) {Y y : ℝ} (hY : 0 < Y)
    (hy : Y ≤ |y|) : ‖stepTransform ρW (y * I)‖ ≤ 1 - cepsGap D v Y := by
  have := hW.isProbabilityMeasure
  have hvW := cepsStepVar_ge hW hθ hD
  have hvW0 : 0 < cepsStepVar ρW := lt_of_lt_of_le (by positivity) hvW
  have hvv := cepsStepVar_le hW
  have hv : 0 < v := lt_of_lt_of_le hvW0 hvv
  set σ := Real.sqrt (cepsStepVar ρW) with hσ
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hvW0
  have hσ2 : σ ^ 2 = cepsStepVar ρW := Real.sq_sqrt hvW0.le
  have h2 : MemLp id 2 ρW := (memLp_two_iff_integrable_sq (by fun_prop)).mpr hW.integrable_sq
  have hvar : ∫ x, (x - 0) ^ 2 ∂ρW = σ ^ 2 := by
    rw [hσ2]; simp [cepsStepVar]
  have hg := one_sub_norm_charFun_sq_ge (stepLaw_locBd hW hθ.le hD.le) h2 hW.integral_id hvar
    hσ0 y
  rw [charFun_eq_stepTransform] at hg
  set p := ‖stepTransform ρW (y * I)‖ with hp
  have hp0 : 0 ≤ p := norm_nonneg _
  set g := cepsGap D v Y with hgdef
  have hgpos : 0 < g := cepsGap_pos hD hv hY
  -- `2 g ≤ c₀ min(1, y² σ²)/(D σ)²`
  have hmin : min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) ≤ min 1 (y ^ 2 * σ ^ 2) := by
    refine min_le_min le_rfl ?_
    rw [hσ2]
    have hY2 : Y ^ 2 ≤ y ^ 2 := by
      rw [← sq_abs y]; exact pow_le_pow_left₀ hY.le hy 2
    exact mul_le_mul hY2 hvW (by positivity) (sq_nonneg _)
  have h2g : 2 * g ≤ c0CharFn * min 1 (y ^ 2 * σ ^ 2) / (D * σ) ^ 2 := by
    rw [hgdef, cepsGap, mul_pow, hσ2]
    have hc0 := c0CharFn_pos
    have hm0 : 0 < min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) := lt_min one_pos (by positivity)
    rw [show 2 * (c0CharFn * min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) / (2 * D ^ 2 * v)) =
      c0CharFn * min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) / (D ^ 2 * v) by field_simp]
    calc c0CharFn * min 1 (Y ^ 2 * (1 / (256 * D ^ 2))) / (D ^ 2 * v)
        ≤ c0CharFn * min 1 (y ^ 2 * σ ^ 2) / (D ^ 2 * v) := by gcongr
      _ ≤ c0CharFn * min 1 (y ^ 2 * σ ^ 2) / (D ^ 2 * cepsStepVar ρW) := by
          have : 0 < min 1 (y ^ 2 * σ ^ 2) := lt_of_lt_of_le hm0 hmin
          gcongr
      _ = c0CharFn * min 1 (y ^ 2 * cepsStepVar ρW) / (D ^ 2 * cepsStepVar ρW) := by
          rw [hσ2]
  have hp2 : p ^ 2 ≤ (1 - g) ^ 2 := by nlinarith
  have hg1 : g ≤ 1 := by nlinarith
  exact (pow_le_pow_iff_left₀ hp0 (by linarith) (by norm_num)).mp hp2

/-- `E[|W| e^{θ|W|/2}] ≤ C_W`. -/
theorem integral_abs_mul_exp_le (hθ : 0 < θ) (hD : 0 ≤ D) :
    Integrable (fun x : ℝ => |x| * Real.exp (θ / 2 * |x|)) ρW ∧
      ∫ x, |x| * Real.exp (θ / 2 * |x|) ∂ρW ≤ cepsShiftConst D θ := by
  have := hW.isProbabilityMeasure
  obtain ⟨hKi, hK⟩ := hW.integral_sq_mul_exp_le hθ hD
  have h1 := hW.integral_exp_le hθ hD (t := θ / 2) (by rw [abs_of_pos (by positivity)])
  have h2 := hW.integral_exp_le hθ hD (t := -(θ / 2))
    (by rw [abs_neg, abs_of_pos (by positivity)])
  have hE : Integrable (fun x : ℝ => Real.exp (θ / 2 * x) + Real.exp (-(θ / 2) * x)) ρW :=
    h1.1.add h2.1
  have hpt : ∀ x : ℝ, |x| * Real.exp (θ / 2 * |x|) ≤
      ((Real.exp (θ / 2 * x) + Real.exp (-(θ / 2) * x)) + x ^ 2 * Real.exp (θ / 2 * |x|)) / 2 := by
    intro x
    have he : Real.exp (θ / 2 * |x|) ≤ Real.exp (θ / 2 * x) + Real.exp (-(θ / 2) * x) := by
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]; linarith [Real.exp_pos (-(θ / 2) * x)]
      · rw [abs_of_nonpos hx, show θ / 2 * -x = -(θ / 2) * x by ring]
        linarith [Real.exp_pos (θ / 2 * x)]
    have hab : |x| ≤ (1 + x ^ 2) / 2 := by nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
    have hexp := Real.exp_pos (θ / 2 * |x|)
    calc |x| * Real.exp (θ / 2 * |x|) ≤ (1 + x ^ 2) / 2 * Real.exp (θ / 2 * |x|) :=
          mul_le_mul_of_nonneg_right hab hexp.le
      _ = (Real.exp (θ / 2 * |x|) + x ^ 2 * Real.exp (θ / 2 * |x|)) / 2 := by ring
      _ ≤ _ := by gcongr
  have hR : Integrable (fun x : ℝ => ((Real.exp (θ / 2 * x) + Real.exp (-(θ / 2) * x)) +
      x ^ 2 * Real.exp (θ / 2 * |x|)) / 2) ρW := (hE.add hKi).div_const 2
  have hint : Integrable (fun x : ℝ => |x| * Real.exp (θ / 2 * |x|)) ρW :=
    hR.mono' (by fun_prop) (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (by positivity)]; exact hpt x)
  refine ⟨hint, (integral_mono hint hR hpt).trans ?_⟩
  rw [integral_div, integral_add hE hKi, integral_add h1.1 h2.1]
  have e1 := h1.2; have e2 := h2.2
  unfold cepsShiftConst
  have : (θ / 2) ^ 2 * (256 * D / θ ^ 3) = 64 * D / θ := by field_simp; ring
  have : (-(θ / 2)) ^ 2 * (256 * D / θ ^ 3) = 64 * D / θ := by field_simp; ring
  have : 256 * D / θ ^ 3 / 2 = 128 * D / θ ^ 3 := by ring
  linarith

/-- `‖M₀(c + i y) - M₀(i y)‖ ≤ |c| C_W` for `|c| ≤ θ/2`. -/
theorem norm_stepTransform_shift_le (hθ : 0 < θ) (hD : 0 ≤ D) {c : ℝ} (hc : |c| ≤ θ / 2)
    (y : ℝ) : ‖stepTransform ρW (c + y * I) - stepTransform ρW (y * I)‖ ≤
      |c| * cepsShiftConst D θ := by
  have := hW.isProbabilityMeasure
  obtain ⟨hKi, hK⟩ := integral_abs_mul_exp_le hW hθ hD
  have hi1 := stepLaw_integrable_cexp hW hθ hD (ζ := c + y * I) (by simpa using hc)
  have hi2 := stepLaw_integrable_cexp hW hθ hD (ζ := y * I) (by simp; positivity)
  rw [stepTransform, stepTransform, ← integral_sub hi1 hi2]
  have hpt : ∀ x : ℝ, ‖cexp ((c + y * I) * x) - cexp (y * I * x)‖ ≤
      |c| * (|x| * Real.exp (θ / 2 * |x|)) := by
    intro x
    have e : cexp ((c + y * I) * x) - cexp (y * I * x) = cexp (y * I * x) * (cexp (c * x) - 1) := by
      rw [mul_sub, ← Complex.exp_add, mul_one]; ring_nf
    rw [e, norm_mul]
    have h1 : ‖cexp (y * I * x)‖ = 1 := by
      rw [Complex.norm_exp]; simp
    have h2 := Complex.norm_exp_sub_sum_le_norm_mul_exp ((c : ℂ) * x) 1
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, pow_one] at h2
    have hn : ‖(c : ℂ) * x‖ = |c| * |x| := by
      rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [hn] at h2
    rw [h1, one_mul]
    calc ‖cexp (c * x) - 1‖ ≤ |c| * |x| * Real.exp (|c| * |x|) := h2
      _ ≤ |c| * |x| * Real.exp (θ / 2 * |x|) := by gcongr
      _ = |c| * (|x| * Real.exp (θ / 2 * |x|)) := by ring
  calc ‖∫ x, (cexp ((c + y * I) * x) - cexp (y * I * x)) ∂ρW‖
      ≤ ∫ x, |c| * (|x| * Real.exp (θ / 2 * |x|)) ∂ρW :=
        norm_integral_le_of_norm_le (hKi.const_mul _) (Eventually.of_forall hpt)
    _ = |c| * ∫ x, |x| * Real.exp (θ / 2 * |x|) ∂ρW := integral_const_mul _ _
    _ ≤ |c| * cepsShiftConst D θ := by gcongr

/-- **Line `L²` bound.** `∫ ‖M₀(c + i y)‖² dy ≤ 2π · 2D²/θ` for `|c| ≤ θ/2`. -/
theorem lintegral_norm_sq_stepTransform_le (hθ : 0 < θ) {c : ℝ}
    (hc : |c| ≤ θ / 2) :
    ∫⁻ y : ℝ, ENNReal.ofReal (‖stepTransform ρW (c + y * I)‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (2 * D ^ 2 / θ) := by
  set f : ℝ → ℂ := fun x => (Real.exp (c * x) : ℂ) * (fW x : ℂ) with hf
  have hfm : Measurable f := by
    have := hW.measurable; fun_prop
  have hfb : ∀ x, ‖f x‖ ≤ D * Real.exp (-(θ / 2) * |x|) := by
    intro x
    rw [hf, norm_mul, norm_real, norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (hW.nonneg x)]
    have h1 := hW.le_exp x
    have h2 : Real.exp (c * x) ≤ Real.exp (θ / 2 * |x|) := by
      apply Real.exp_le_exp.mpr
      calc c * x ≤ |c * x| := le_abs_self _
        _ = |c| * |x| := abs_mul _ _
        _ ≤ θ / 2 * |x| := mul_le_mul_of_nonneg_right hc (abs_nonneg x)
    calc Real.exp (c * x) * fW x ≤ Real.exp (θ / 2 * |x|) * (D * Real.exp (-θ * |x|)) :=
          mul_le_mul h2 h1 (hW.nonneg x) (Real.exp_pos _).le
      _ = D * Real.exp (-(θ / 2) * |x|) := by
          rw [mul_comm, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hint_env : Integrable (fun x : ℝ => D * Real.exp (-(θ / 2) * |x|)) := by
    have h := IsStepLaw.lintegral_exp_neg_abs (θ / 2) (by positivity)
    refine Integrable.const_mul ⟨by fun_prop, ?_⟩ D
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => (Real.exp_pos _).le), h]
    exact ENNReal.ofReal_lt_top
  have hfi : Integrable f := hint_env.mono' hfm.aestronglyMeasurable
    (Eventually.of_forall hfb)
  have hP := lintegral_norm_sq_lineFourier_le hfi hfm
  have hline : ∀ y : ℝ, stepTransform ρW (c + y * I) = lineFourier f y := by
    intro y
    rw [stepTransform_eq_integral hW, lineFourier]
    congr 1; funext x
    simp only [hf]
    rw [show ((c : ℂ) + y * I) * x = I * y * x + ((c * x : ℝ) : ℂ) by push_cast; ring,
      Complex.exp_add, ← Complex.ofReal_exp]
    ring
  simp_rw [hline]
  refine hP.trans ?_
  gcongr
  calc ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (D ^ 2 * Real.exp (-θ * |x|)) := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        calc ‖f x‖ ^ 2 ≤ (D * Real.exp (-(θ / 2) * |x|)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hfb x) 2
          _ = D ^ 2 * Real.exp (-θ * |x|) := by
              rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    _ = ENNReal.ofReal (D ^ 2) * ENNReal.ofReal (2 / θ) := by
        rw [← IsStepLaw.lintegral_exp_neg_abs θ hθ, ← lintegral_const_mul _ (by fun_prop)]
        congr 1; funext x; rw [ENNReal.ofReal_mul (sq_nonneg D)]
    _ = ENNReal.ofReal (2 * D ^ 2 / θ) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg D)]; congr 1; ring

end

end PGM
