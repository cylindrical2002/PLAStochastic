import PLAStochastic.Index.GEP.Universality.ClassProperties
import PLAStochastic.Index.LocalCount.MaximalBernstein
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# WP5: centered exponential tilts and uniform exponential moments

Tilting the original gap law by `lambda * (x - 1)` leaves the coordinate
unchanged. Its centered exponential moment is uniform whenever the tilt and
the remaining exponential weight fit inside the original weight. The
normalizer is at least one by the mean-one condition, without a density
assumption. These are moment inputs to the tilted Cramer and local limit steps.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- Exponential tilt by the centered gap, still as a law of the original coordinate. -/
def centeredTilt (ν : ProbabilityMeasure ℝ) (lam : ℝ) : Measure ℝ :=
  (ν : Measure ℝ).tilted (fun x => lam * (x - 1))

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

/-- The two-sided centered exponential bound also includes integrability. -/
theorem UnivClass.integrable_exp_abs_sub_one (h : UnivClass vlo vhi κ₃ B θ ν)
    {s : ℝ} (hs : 0 ≤ s) (hsθ : s ≤ θ) :
    Integrable (fun x : ℝ => Real.exp (s * |x - 1|)) (ν : Measure ℝ) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.exp_nonneg _)]
  exact (h.lintegral_exp_abs_sub_one_le hs hsθ).trans_lt ENNReal.ofReal_lt_top

/-- Every tilt inside the exponential-moment interval has a finite normalizer. -/
theorem UnivClass.integrable_exp_centered (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) :
    Integrable (fun x : ℝ => Real.exp (lam * (x - 1))) (ν : Measure ℝ) := by
  refine (h.integrable_exp_abs_sub_one (abs_nonneg lam) hlam).mono' (by fun_prop) ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans_eq (abs_mul _ _)

/-- Centering at the true mean makes the tilt normalizer at least one. -/
theorem UnivClass.one_le_integral_exp_centered (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) :
    1 ≤ ∫ x : ℝ, Real.exp (lam * (x - 1)) ∂(ν : Measure ℝ) := by
  have hx : Integrable (fun x : ℝ => x) (ν : Measure ℝ) :=
    h.memLp3.integrable (by norm_num)
  have hc : ∫ x : ℝ, (x - 1) ∂(ν : Measure ℝ) = 0 := by
    rw [integral_sub hx (integrable_const 1)]
    change lawMean ν - _ = 0
    simp [h.mean]
  have hlin : Integrable (fun x : ℝ => lam * (x - 1)) (ν : Measure ℝ) :=
    (hx.sub (integrable_const 1)).const_mul lam
  calc
    1 = ∫ x : ℝ, 1 + lam * (x - 1) ∂(ν : Measure ℝ) := by
      rw [integral_add (integrable_const 1) hlin,
        integral_const_mul, hc]
      simp
    _ ≤ ∫ x : ℝ, Real.exp (lam * (x - 1)) ∂(ν : Measure ℝ) := by
      apply integral_mono ((integrable_const 1).add hlin)
        (h.integrable_exp_centered hlam)
      intro x
      change 1 + lam * (x - 1) ≤ Real.exp (lam * (x - 1))
      linarith [Real.add_one_le_exp (lam * (x - 1))]

/-- The centered tilt is a probability measure throughout the admissible interval. -/
theorem UnivClass.isProbabilityMeasure_centeredTilt (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam : ℝ} (hlam : |lam| ≤ θ) : IsProbabilityMeasure (centeredTilt ν lam) :=
  isProbabilityMeasure_tilted (h.integrable_exp_centered hlam)

/-- A uniform exponential moment remains after reserving room for the tilt. -/
theorem UnivClass.centeredTilt_exp_abs_le (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam s : ℝ} (hs : 0 ≤ s) (hlam : |lam| + s ≤ θ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (s * |x - 1|)) ∂centeredTilt ν lam ≤
      ENNReal.ofReal (Real.exp θ * B) := by
  have hl : |lam| ≤ θ := by linarith
  have hθ : 0 ≤ θ := (abs_nonneg lam).trans hl
  have hM := h.one_le_integral_exp_centered hl
  change (∫⁻ x, ENNReal.ofReal (Real.exp (s * |x - 1|))
    ∂(ν : Measure ℝ).tilted (fun x => lam * (x - 1))) ≤ _
  rw [lintegral_tilted]
  apply le_trans (lintegral_mono (fun x => ?_)) (h.lintegral_exp_abs_sub_one_le hθ le_rfl)
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  calc
    Real.exp (lam * (x - 1)) /
        (∫ z : ℝ, Real.exp (lam * (z - 1)) ∂(ν : Measure ℝ)) *
        Real.exp (s * |x - 1|)
      ≤ Real.exp (lam * (x - 1)) * Real.exp (s * |x - 1|) := by
        gcongr
        exact div_le_self (Real.exp_nonneg _) hM
    _ = Real.exp (lam * (x - 1) + s * |x - 1|) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (θ * |x - 1|) := by
      apply Real.exp_le_exp.mpr
      have ha : lam * (x - 1) ≤ |lam| * |x - 1| := by
        calc lam * (x - 1) ≤ |lam * (x - 1)| := le_abs_self _
          _ = |lam| * |x - 1| := abs_mul _ _
      nlinarith [mul_le_mul_of_nonneg_right hlam (abs_nonneg (x - 1))]

/-- The remaining exponential moment is finite, including for singular input laws. -/
theorem UnivClass.centeredTilt_integrable_exp_abs (h : UnivClass vlo vhi κ₃ B θ ν)
    {lam s : ℝ} (hs : 0 ≤ s) (hlam : |lam| + s ≤ θ) :
    Integrable (fun x : ℝ => Real.exp (s * |x - 1|)) (centeredTilt ν lam) := by
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => Real.exp_nonneg _)]
  exact (h.centeredTilt_exp_abs_le hs hlam).trans_lt ENNReal.ofReal_lt_top

/-- A uniform second moment about the original center under every half-range tilt. -/
theorem UnivClass.centeredTilt_second_moment (h : UnivClass vlo vhi κ₃ B θ ν)
    (hθ : 0 < θ) {lam : ℝ} (hlam : |lam| ≤ θ / 2) :
    Integrable (fun x : ℝ => (x - 1) ^ 2) (centeredTilt ν lam) ∧
      (∫ x : ℝ, (x - 1) ^ 2 ∂centeredTilt ν lam) ≤
        (8 / θ ^ 2) * (Real.exp θ * B) := by
  have hs : 0 ≤ θ / 2 := by positivity
  have hls : |lam| + θ / 2 ≤ θ := by linarith
  have he := h.centeredTilt_integrable_exp_abs hs hls
  have hb := h.centeredTilt_exp_abs_le hs hls
  have hpt (x : ℝ) : (x - 1) ^ 2 ≤
      (8 / θ ^ 2) * Real.exp (θ / 2 * |x - 1|) := by
    have hq := lcbb_sq_le_two_exp (show 0 ≤ θ / 2 * |x - 1| by positivity)
    rw [mul_pow, div_pow, sq_abs] at hq
    rw [div_mul_eq_mul_div, le_div_iff₀ (sq_pos_of_pos hθ)]
    nlinarith
  have hi : Integrable (fun x : ℝ => (x - 1) ^ 2) (centeredTilt ν lam) := by
    refine (he.const_mul (8 / θ ^ 2)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (x - 1))] using hpt x
  refine ⟨hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal he (ae_of_all _ fun x => Real.exp_nonneg _)] at hb
  have heB : (∫ x : ℝ, Real.exp (θ / 2 * |x - 1|) ∂centeredTilt ν lam) ≤
      Real.exp θ * B := by
    have hB : 0 ≤ Real.exp θ * B := by
      have hbase := h.lintegral_exp_abs_sub_one_le hθ.le le_rfl
      have hint := h.integrable_exp_abs_sub_one hθ.le le_rfl
      rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => Real.exp_nonneg _)]
        at hbase
      rcases (ENNReal.ofReal_le_ofReal_iff').mp hbase with hbase | hbase
      · exact (integral_nonneg fun x => Real.exp_nonneg _).trans hbase
      · exact False.elim ((not_le_of_gt (integral_exp_pos hint)) hbase)
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb
  calc
    (∫ x : ℝ, (x - 1) ^ 2 ∂centeredTilt ν lam) ≤
        ∫ x : ℝ, (8 / θ ^ 2) * Real.exp (θ / 2 * |x - 1|) ∂centeredTilt ν lam :=
      integral_mono hi (he.const_mul _) hpt
    _ = (8 / θ ^ 2) * ∫ x : ℝ, Real.exp (θ / 2 * |x - 1|) ∂centeredTilt ν lam :=
      integral_const_mul _ _
    _ ≤ (8 / θ ^ 2) * (Real.exp θ * B) :=
      mul_le_mul_of_nonneg_left heB (by positivity)

end

end PGM
