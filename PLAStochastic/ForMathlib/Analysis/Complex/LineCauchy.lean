import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineShift
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LineInversion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Cauchy transforms on a vertical line

For `φ : ℝ → ℂ` and the line `Re s = c`, `lineCauchy φ c ζ = ∫ φ(y)/(c + i y - ζ) dy`.

* `integrable_lineCauchy_integrand`: integrability at one point off the line gives integrability
  at every point off the line;
* `hasDerivAt_lineCauchy`: the transform is holomorphic off the line;
* `tendsto_lineCauchy_atBot`: it tends to `0` along the real axis to `-∞`;
* `integral_inv_mul_vline_opposite`, `integral_inv_mul_vline_right`: `∫ ((s - p)(s - ζ))⁻¹ dy`
  equals `-2Real.pi/(p - ζ)` when `Re ζ < c < Re p`, and `0` when both points lie right of the line
  (explicit logarithmic primitives);
* `vline_cauchy_strip` (Cauchy's formula on a strip): for `h` holomorphic and bounded on the
  closed strip `a ≤ Re ≤ b`, `∫_b h/(s - ζ) dy - ∫_a h/(s - ζ) dy = 2Real.pi h(ζ)` for `a < Re ζ < b`.
-/

noncomputable section

open MeasureTheory Set Complex Filter Topology Metric intervalIntegral
open PGM.WienerHopf

namespace PGM

/-! ### The vertical line -/

theorem norm_vline_sub_sq (c y : ℝ) (ζ : ℂ) :
    ‖(c : ℂ) + y * I - ζ‖ ^ 2 = (y - ζ.im) ^ 2 + (c - ζ.re) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, sub_im, add_im, mul_im]
  ring

theorem abs_sub_re_le_norm_vline (c y : ℝ) (ζ : ℂ) : |c - ζ.re| ≤ ‖(c : ℂ) + y * I - ζ‖ := by
  have := abs_re_le_norm ((c : ℂ) + y * I - ζ)
  simpa using this

theorem abs_sub_im_le_norm_vline (c y : ℝ) (ζ : ℂ) : |y - ζ.im| ≤ ‖(c : ℂ) + y * I - ζ‖ := by
  have := abs_im_le_norm ((c : ℂ) + y * I - ζ)
  simpa using this

theorem vline_sub_ne_zero {c : ℝ} {ζ : ℂ} (hζ : ζ.re ≠ c) (y : ℝ) : (c : ℂ) + y * I - ζ ≠ 0 := by
  intro h
  have h1 := abs_sub_re_le_norm_vline c y ζ
  rw [h, norm_zero] at h1
  exact hζ (by linarith [abs_nonneg (c - ζ.re), abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))])

/-- `‖s - ζ₀‖ ≤ (1 + ‖ζ - ζ₀‖/|c - Re ζ|) ‖s - ζ‖` on the line `s = c + i y`. -/
theorem norm_vline_sub_le_mul {c : ℝ} {ζ : ℂ} (hζ : ζ.re ≠ c) (ζ₀ : ℂ) (y : ℝ) :
    ‖(c : ℂ) + y * I - ζ₀‖ ≤ (1 + ‖ζ - ζ₀‖ / |c - ζ.re|) * ‖(c : ℂ) + y * I - ζ‖ := by
  have hd : 0 < |c - ζ.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hζ))
  have h1 := abs_sub_re_le_norm_vline c y ζ
  have h2 : ‖ζ - ζ₀‖ ≤ ‖ζ - ζ₀‖ / |c - ζ.re| * ‖(c : ℂ) + y * I - ζ‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hd]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  calc ‖(c : ℂ) + y * I - ζ₀‖ = ‖((c : ℂ) + y * I - ζ) + (ζ - ζ₀)‖ := by ring_nf
    _ ≤ ‖(c : ℂ) + y * I - ζ‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
    _ ≤ ‖(c : ℂ) + y * I - ζ‖ + ‖ζ - ζ₀‖ / |c - ζ.re| * ‖(c : ℂ) + y * I - ζ‖ := by linarith
    _ = _ := by ring

theorem norm_vline_ratio_le {c : ℝ} {ζ : ℂ} (hζ : ζ.re ≠ c) (ζ₀ : ℂ) (y : ℝ) :
    ‖((c : ℂ) + y * I - ζ₀) / ((c : ℂ) + y * I - ζ)‖ ≤ 1 + ‖ζ - ζ₀‖ / |c - ζ.re| := by
  rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr (vline_sub_ne_zero hζ y))]
  exact norm_vline_sub_le_mul hζ ζ₀ y

/-! ### The Cauchy transform -/

/-- The Cauchy transform `∫ φ(y)/(c + i y - ζ) dy` on the line `Re s = c`. -/
def lineCauchy (φ : ℝ → ℂ) (c : ℝ) (ζ : ℂ) : ℂ := ∫ y : ℝ, φ y / ((c : ℂ) + y * I - ζ)

theorem vline_div_eq {c : ℝ} {ζ₀ : ℂ} (hζ₀ : ζ₀.re ≠ c) (φ : ℝ → ℂ) (ζ : ℂ) (y : ℝ) :
    φ y / ((c : ℂ) + y * I - ζ) =
      φ y / ((c : ℂ) + y * I - ζ₀) * (((c : ℂ) + y * I - ζ₀) / ((c : ℂ) + y * I - ζ)) := by
  have hne := vline_sub_ne_zero hζ₀ y
  rw [div_mul_div_comm, mul_comm (φ y), mul_div_mul_left _ _ hne]

theorem integrable_lineCauchy_integrand {φ : ℝ → ℂ} {c : ℝ} {ζ₀ ζ : ℂ} (hζ₀ : ζ₀.re ≠ c)
    (h0 : Integrable fun y : ℝ => φ y / ((c : ℂ) + y * I - ζ₀)) (hζ : ζ.re ≠ c) :
    Integrable fun y : ℝ => φ y / ((c : ℂ) + y * I - ζ) := by
  have hm : AEStronglyMeasurable
      (fun y : ℝ => ((c : ℂ) + y * I - ζ₀) / ((c : ℂ) + y * I - ζ)) volume :=
    (Continuous.div (by fun_prop) (by fun_prop) (vline_sub_ne_zero hζ)).aestronglyMeasurable
  have := h0.mul_bdd hm (Eventually.of_forall fun y => norm_vline_ratio_le hζ ζ₀ y)
  refine this.congr (Eventually.of_forall fun y => ?_)
  exact (vline_div_eq hζ₀ φ ζ y).symm

/-- **Holomorphy of the Cauchy transform off the line.** -/
theorem hasDerivAt_lineCauchy {φ : ℝ → ℂ} {c : ℝ} {ζ₀ ζ : ℂ} (hζ₀ : ζ₀.re ≠ c)
    (h0 : Integrable fun y : ℝ => φ y / ((c : ℂ) + y * I - ζ₀)) (hζ : ζ.re ≠ c) :
    HasDerivAt (lineCauchy φ c) (∫ y : ℝ, φ y / ((c : ℂ) + y * I - ζ) ^ 2) ζ := by
  set ε : ℝ := |c - ζ.re| / 2 with hεdef
  have hd0 : 0 < |c - ζ.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hζ))
  have hε : 0 < ε := by positivity
  have hball : ∀ z ∈ ball ζ ε, ε ≤ |c - z.re| ∧ z.re ≠ c ∧ ‖z - ζ₀‖ ≤ ‖ζ - ζ₀‖ + ε := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : |z.re - ζ.re| ≤ ‖z - ζ‖ := by simpa using abs_re_le_norm (z - ζ)
    have h2 : |c - ζ.re| ≤ |c - z.re| + |z.re - ζ.re| := by
      calc |c - ζ.re| = |(c - z.re) + (z.re - ζ.re)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h3 : ε ≤ |c - z.re| := by linarith
    refine ⟨h3, ?_, ?_⟩
    · intro h; rw [h, sub_self, abs_zero] at h3; linarith
    · calc ‖z - ζ₀‖ = ‖(z - ζ) + (ζ - ζ₀)‖ := by ring_nf
        _ ≤ ‖z - ζ‖ + ‖ζ - ζ₀‖ := norm_add_le _ _
        _ ≤ _ := by linarith
  set K : ℝ := (1 + (‖ζ - ζ₀‖ + ε) / ε) / ε with hK
  have hderiv : ∀ y : ℝ, ∀ z ∈ ball ζ ε, HasDerivAt (fun z => φ y / ((c : ℂ) + y * I - z))
      (φ y / ((c : ℂ) + y * I - z) ^ 2) z := by
    intro y z hz
    have hne := vline_sub_ne_zero (hball z hz).2.1 y
    have h1 : HasDerivAt (fun z : ℂ => (c : ℂ) + y * I - z) (-1) z :=
      (hasDerivAt_id z).const_sub _
    have h2 : HasDerivAt (fun z => ((c : ℂ) + y * I - z)⁻¹)
        (-(-1) / ((c : ℂ) + y * I - z) ^ 2) z := h1.inv hne
    have h3 : HasDerivAt (fun z => φ y * ((c : ℂ) + y * I - z)⁻¹)
        (φ y * (-(-1) / ((c : ℂ) + y * I - z) ^ 2)) z := h2.const_mul (φ y)
    have e1 : (fun z => φ y / ((c : ℂ) + y * I - z)) =
        fun z => φ y * ((c : ℂ) + y * I - z)⁻¹ := by
      funext z; rw [div_eq_mul_inv]
    rw [e1]
    convert h3 using 1
    ring
  have hbound : ∀ y : ℝ, ∀ z ∈ ball ζ ε, ‖φ y / ((c : ℂ) + y * I - z) ^ 2‖ ≤
      K * ‖φ y / ((c : ℂ) + y * I - ζ₀)‖ := by
    intro y z hz
    obtain ⟨h1, h2, h3⟩ := hball z hz
    have hne := vline_sub_ne_zero h2 y
    have hne0 := vline_sub_ne_zero hζ₀ y
    set A := ‖(c : ℂ) + y * I - z‖ with hA
    set B := ‖(c : ℂ) + y * I - ζ₀‖ with hB
    set P := ‖φ y‖ with hP
    have hA0 : ε ≤ A := h1.trans (abs_sub_re_le_norm_vline c y z)
    have hB0 : 0 < B := norm_pos_iff.mpr hne0
    have hr := norm_vline_sub_le_mul h2 ζ₀ y
    have hM : 1 + ‖z - ζ₀‖ / |c - z.re| ≤ 1 + (‖ζ - ζ₀‖ + ε) / ε := by
      gcongr
    have key : B ≤ K * A ^ 2 := by
      have hA1 : A ≤ A * (A / ε) := by
        have : 1 ≤ A / ε := (one_le_div hε).mpr hA0
        nlinarith [norm_nonneg ((c : ℂ) + y * I - z)]
      calc B ≤ (1 + ‖z - ζ₀‖ / |c - z.re|) * A := hr
        _ ≤ (1 + (‖ζ - ζ₀‖ + ε) / ε) * A := by gcongr
        _ ≤ (1 + (‖ζ - ζ₀‖ + ε) / ε) * (A * (A / ε)) := by
            gcongr
        _ = K * A ^ 2 := by rw [hK]; ring
    rw [norm_div, norm_pow, norm_div, ← hA, ← hB, ← hP, div_le_iff₀ (by positivity)]
    have h1' : 1 ≤ K * A ^ 2 / B := (one_le_div hB0).mpr key
    calc P = P * 1 := (mul_one P).symm
      _ ≤ P * (K * A ^ 2 / B) := mul_le_mul_of_nonneg_left h1' (norm_nonneg _)
      _ = K * (P / B) * A ^ 2 := by field_simp
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun y : ℝ => φ y / ((c : ℂ) + y * I - z)) volume := by
    intro z
    have hm : AEStronglyMeasurable
        (fun y : ℝ => ((c : ℂ) + y * I - ζ₀) / ((c : ℂ) + y * I - z)) volume :=
      (by fun_prop : Measurable fun y : ℝ => ((c : ℂ) + y * I - ζ₀) /
        ((c : ℂ) + y * I - z)).aestronglyMeasurable
    exact (h0.aestronglyMeasurable.mul hm).congr
      (Eventually.of_forall fun y => (vline_div_eq hζ₀ φ z y).symm)
  have hmeas' : AEStronglyMeasurable (fun y : ℝ => φ y / ((c : ℂ) + y * I - ζ) ^ 2) volume := by
    have hm : AEStronglyMeasurable
        (fun y : ℝ => ((c : ℂ) + y * I - ζ₀) / ((c : ℂ) + y * I - ζ) ^ 2) volume :=
      (by fun_prop : Measurable fun y : ℝ => ((c : ℂ) + y * I - ζ₀) /
        ((c : ℂ) + y * I - ζ) ^ 2).aestronglyMeasurable
    refine (h0.aestronglyMeasurable.mul hm).congr (Eventually.of_forall fun y => ?_)
    have hne0 := vline_sub_ne_zero hζ₀ y
    simp only [Pi.mul_apply]
    rw [div_mul_div_comm, mul_comm (φ y), mul_div_mul_left _ _ hne0]
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z y => φ y / ((c : ℂ) + y * I - z))
    (F' := fun z y => φ y / ((c : ℂ) + y * I - z) ^ 2) (x₀ := ζ)
    (bound := fun y => K * ‖φ y / ((c : ℂ) + y * I - ζ₀)‖) (ball_mem_nhds ζ hε)
    (Eventually.of_forall fun z => hmeas z)
    (integrable_lineCauchy_integrand hζ₀ h0 hζ) hmeas'
    (Eventually.of_forall fun y z hz => hbound y z hz) (h0.norm.const_mul K)
    (Eventually.of_forall fun y z hz => hderiv y z hz)
  exact hmain.2

theorem differentiableAt_lineCauchy {φ : ℝ → ℂ} {c : ℝ} {ζ₀ ζ : ℂ} (hζ₀ : ζ₀.re ≠ c)
    (h0 : Integrable fun y : ℝ => φ y / ((c : ℂ) + y * I - ζ₀)) (hζ : ζ.re ≠ c) :
    DifferentiableAt ℂ (lineCauchy φ c) ζ :=
  (hasDerivAt_lineCauchy hζ₀ h0 hζ).differentiableAt

/-- The Cauchy transform tends to `0` along the real axis to `-∞`. -/
theorem tendsto_lineCauchy_atBot {φ : ℝ → ℂ} {c : ℝ} {ζ₀ : ℂ} (hζ₀ : ζ₀.re ≠ c)
    (h0 : Integrable fun y : ℝ => φ y / ((c : ℂ) + y * I - ζ₀)) :
    Tendsto (fun t : ℝ => lineCauchy φ c t) atBot (𝓝 0) := by
  have hc1 : ((c - 1 : ℝ) : ℂ).re ≠ c := by simp
  have h1 := integrable_lineCauchy_integrand hζ₀ h0 hc1
  have hle : ∀ t : ℝ, t ≤ c - 1 → ∀ y : ℝ,
      ‖φ y / ((c : ℂ) + y * I - t)‖ ≤ ‖φ y / ((c : ℂ) + y * I - ((c - 1 : ℝ) : ℂ))‖ := by
    intro t ht y
    rw [norm_div, norm_div]
    refine div_le_div_of_nonneg_left (norm_nonneg _)
      (norm_pos_iff.mpr (vline_sub_ne_zero hc1 y)) ?_
    have e1 := norm_vline_sub_sq c y (t : ℂ)
    have e2 := norm_vline_sub_sq c y ((c - 1 : ℝ) : ℂ)
    simp only [ofReal_re, ofReal_im] at e1 e2
    have : ‖(c : ℂ) + y * I - ((c - 1 : ℝ) : ℂ)‖ ^ 2 ≤ ‖(c : ℂ) + y * I - (t : ℂ)‖ ^ 2 := by
      rw [e1, e2]; nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atBot)
    (F := fun (t : ℝ) (y : ℝ) => φ y / ((c : ℂ) + y * I - t)) (f := fun _ => (0 : ℂ))
    (fun y => ‖φ y / ((c : ℂ) + y * I - ((c - 1 : ℝ) : ℂ))‖)
    (Eventually.of_forall fun t => (by
      have hm : AEStronglyMeasurable
          (fun y : ℝ => ((c : ℂ) + y * I - ((c - 1 : ℝ) : ℂ)) / ((c : ℂ) + y * I - t)) volume :=
        (by fun_prop : Measurable fun y : ℝ => ((c : ℂ) + y * I - ((c - 1 : ℝ) : ℂ)) /
          ((c : ℂ) + y * I - t)).aestronglyMeasurable
      exact (h1.aestronglyMeasurable.mul hm).congr
        (Eventually.of_forall fun y => (vline_div_eq hc1 φ t y).symm)))
    ((eventually_le_atBot (c - 1)).mono fun t ht => Eventually.of_forall fun y => hle t ht y)
    h1.norm (Eventually.of_forall fun y => ?_)
  · simpa [lineCauchy] using hlim
  · -- pointwise decay
    have hdec : Tendsto (fun t : ℝ => ‖φ y‖ / (c - t)) atBot (𝓝 0) := by
      have h2 : Tendsto (fun t : ℝ => c - t) atBot atTop := by
        have := tendsto_neg_atBot_atTop.atTop_add (tendsto_const_nhds (x := c))
        simpa [sub_eq_add_neg, add_comm] using this
      exact tendsto_const_nhds.div_atTop h2
    refine squeeze_zero_norm' ?_ hdec
    filter_upwards [eventually_lt_atBot c] with t ht
    rw [norm_div]
    have hct : 0 < c - t := by linarith
    refine div_le_div_of_nonneg_left (norm_nonneg _) hct ?_
    have := abs_sub_re_le_norm_vline c y (t : ℂ)
    simp only [ofReal_re] at this
    rwa [abs_of_pos hct] at this

/-! ### Principal values on a vertical line -/

theorem tendsto_norm_vline_div (w : ℂ) {σ : ℝ} (hσ : |σ| = 1) :
    Tendsto (fun T : ℝ => ‖w + ((σ * T : ℝ) : ℂ) * I‖ / T) atTop (𝓝 1) := by
  have key : ∀ T : ℝ, 0 < T → |‖w + ((σ * T : ℝ) : ℂ) * I‖ / T - 1| ≤ ‖w‖ / T := by
    intro T hT
    have h1 : ‖((σ * T : ℝ) : ℂ) * I‖ = T := by
      rw [norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs, abs_mul, hσ, one_mul,
        abs_of_pos hT]
    have h2 : |‖w + ((σ * T : ℝ) : ℂ) * I‖ - ‖((σ * T : ℝ) : ℂ) * I‖| ≤ ‖w‖ := by
      have := abs_norm_sub_norm_le (w + ((σ * T : ℝ) : ℂ) * I) (((σ * T : ℝ) : ℂ) * I)
      simpa using this
    rw [h1] at h2
    rw [show ‖w + ((σ * T : ℝ) : ℂ) * I‖ / T - 1 = (‖w + ((σ * T : ℝ) : ℂ) * I‖ - T) / T by
      field_simp, abs_div, abs_of_pos hT]
    exact div_le_div_of_nonneg_right h2 hT.le
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun T : ℝ => ‖w‖ / T) (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_const_nhds.div_atTop tendsto_id)
  filter_upwards [eventually_gt_atTop 0] with T hT
  rw [Real.norm_eq_abs]
  exact key T hT

theorem tendsto_arg_vline {w : ℂ} (hw : 0 < w.re) {σ : ℝ} (hσ : |σ| = 1) :
    Tendsto (fun T : ℝ => arg (w + ((σ * T : ℝ) : ℂ) * I)) atTop (𝓝 (Real.arcsin σ)) := by
  have hn := tendsto_norm_vline_div w hσ
  have him : Tendsto (fun T : ℝ => (w.im / T + σ)) atTop (𝓝 (0 + σ)) :=
    (tendsto_const_nhds.div_atTop tendsto_id).add tendsto_const_nhds
  have hq := him.div hn one_ne_zero
  rw [zero_add, div_one] at hq
  have hq' : Tendsto (fun T : ℝ => (w + ((σ * T : ℝ) : ℂ) * I).im /
      ‖w + ((σ * T : ℝ) : ℂ) * I‖) atTop (𝓝 σ) := by
    refine hq.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hn0 : ‖w + ((σ * T : ℝ) : ℂ) * I‖ ≠ 0 := by
      rw [norm_ne_zero_iff]; intro h
      have := congrArg re h; simp at this; linarith
    have hi : (w + ((σ * T : ℝ) : ℂ) * I).im = w.im + σ * T := by simp
    show (w.im / T + σ) / (‖w + ((σ * T : ℝ) : ℂ) * I‖ / T) = _
    rw [hi]
    field_simp
  have harc := (Real.continuous_arcsin.tendsto σ).comp hq'
  refine harc.congr fun T => ?_
  simp only [Function.comp_apply]
  rw [arg_of_re_nonneg]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    add_zero]
  exact hw.le

theorem tendsto_log_vline_sub {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun T : ℝ => log (w + T * I) - log (w + ((-T : ℝ) : ℂ) * I)) atTop
      (𝓝 (Real.pi * I)) := by
  have hσ1 : |(1 : ℝ)| = 1 := by simp
  have hσ2 : |(-1 : ℝ)| = 1 := by simp
  have e1 : ∀ T : ℝ, w + ((1 * T : ℝ) : ℂ) * I = w + T * I := fun T => by simp
  have e2 : ∀ T : ℝ, w + ((-1 * T : ℝ) : ℂ) * I = w + ((-T : ℝ) : ℂ) * I := fun T => by simp
  have hn1 := tendsto_norm_vline_div w hσ1
  have hn2 := tendsto_norm_vline_div w hσ2
  simp only [e1, e2] at hn1 hn2
  have ha1 := tendsto_arg_vline hw hσ1
  have ha2 := tendsto_arg_vline hw hσ2
  simp only [e1, e2] at ha1 ha2
  rw [Real.arcsin_one] at ha1
  rw [Real.arcsin_neg_one] at ha2
  -- real parts
  have hre : Tendsto (fun T : ℝ => Real.log (‖w + T * I‖ / T) -
      Real.log (‖w + ((-T : ℝ) : ℂ) * I‖ / T)) atTop (𝓝 (Real.log 1 - Real.log 1)) :=
    (((Real.continuousAt_log one_ne_zero).tendsto).comp hn1).sub
      (((Real.continuousAt_log one_ne_zero).tendsto).comp hn2)
  rw [Real.log_one, sub_zero] at hre
  have hre' : Tendsto (fun T : ℝ => (log (w + T * I) - log (w + ((-T : ℝ) : ℂ) * I)).re) atTop
      (𝓝 0) := by
    refine hre.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with T hT
    have hp1 : 0 < ‖w + T * I‖ := by
      rw [norm_pos_iff]; intro h; have := congrArg re h; simp at this; linarith
    have hp2 : 0 < ‖w + ((-T : ℝ) : ℂ) * I‖ := by
      rw [norm_pos_iff]; intro h; have := congrArg re h; simp at this; linarith
    rw [sub_re, log_re, log_re, Real.log_div hp1.ne' hT.ne', Real.log_div hp2.ne' hT.ne']
    ring
  have him' : Tendsto (fun T : ℝ => (log (w + T * I) - log (w + ((-T : ℝ) : ℂ) * I)).im) atTop
      (𝓝 Real.pi) := by
    have := ha1.sub ha2
    rw [show Real.pi / 2 - -(Real.pi / 2) = Real.pi by ring] at this
    refine this.congr fun T => ?_
    rw [sub_im, log_im, log_im]
  have hc := ((continuous_ofReal.tendsto 0).comp hre').add
    (((continuous_ofReal.tendsto Real.pi).comp him').mul_const I)
  rw [ofReal_zero, zero_add] at hc
  refine hc.congr fun T => ?_
  simp only [Function.comp_apply]
  exact re_add_im _

/-- `-i log(w + i y)` is a primitive of `(w + i y)⁻¹` for `Re w > 0`. -/
theorem hasDerivAt_log_vline {w : ℂ} (hw : 0 < w.re) (y : ℝ) :
    HasDerivAt (fun y : ℝ => -I * log (w + y * I)) ((w + y * I)⁻¹) y := by
  have hf : HasDerivAt (fun y : ℝ => w + (y : ℂ) * I) I y := by
    have := (((hasDerivAt_id (y : ℂ)).mul_const I).const_add w).comp_ofReal
    simpa using this
  have hslit : w + (y : ℂ) * I ∈ slitPlane := by
    left; simp; exact hw
  have hne : w + (y : ℂ) * I ≠ 0 := slitPlane_ne_zero hslit
  have h : HasDerivAt (fun t : ℝ => -I * log (w + (t : ℂ) * I)) (-I * (I / (w + (y : ℂ) * I))) y :=
    (hf.clog_real hslit).const_mul (-I)
  convert h using 1
  rw [← mul_div_assoc, show -I * I = 1 by rw [neg_mul, I_mul_I, neg_neg], one_div]

/-- The principal value `∫_{-T}^{T} (w + i y)⁻¹ dy → π` for `Re w > 0`. -/
theorem tendsto_integral_inv_vline_pos {w : ℂ} (hw : 0 < w.re) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T, (w + y * I)⁻¹) atTop (𝓝 (Real.pi : ℂ)) := by
  have hint : ∀ T : ℝ, ∫ y in (-T)..T, (w + y * I)⁻¹ =
      -I * (log (w + T * I) - log (w + ((-T : ℝ) : ℂ) * I)) := by
    intro T
    rw [integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_log_vline hw y)]
    · ring
    · refine (Continuous.inv₀ (by fun_prop) fun y => ?_).intervalIntegrable _ _
      intro h; have := congrArg re h; simp at this; linarith
  have h := (tendsto_log_vline_sub hw).const_mul (-I)
  rw [show -I * (Real.pi * I) = (Real.pi : ℂ) * -(I * I) by ring, I_mul_I, neg_neg, mul_one] at h
  exact h.congr fun T => (hint T).symm

/-- The principal value `∫_{-T}^{T} (w + i y)⁻¹ dy → -π` for `Re w < 0`. -/
theorem tendsto_integral_inv_vline_neg {w : ℂ} (hw : w.re < 0) :
    Tendsto (fun T : ℝ => ∫ y in (-T)..T, (w + y * I)⁻¹) atTop (𝓝 (-Real.pi : ℂ)) := by
  have hw' : 0 < (-w).re := by simp; linarith
  have h := (tendsto_integral_inv_vline_pos hw').neg
  refine h.congr fun T => ?_
  have e : ∀ y : ℝ, (w + y * I)⁻¹ = -((-w) + ((-y : ℝ) : ℂ) * I)⁻¹ := by
    intro y; push_cast; rw [← inv_neg]; ring_nf
  rw [intervalIntegral.integral_congr (g := fun y : ℝ => -((-w) + ((-y : ℝ) : ℂ) * I)⁻¹)
    (fun y _ => e y), intervalIntegral.integral_neg]
  congr 1
  have := intervalIntegral.integral_comp_neg (a := -T) (b := T)
    (fun y : ℝ => ((-w) + (y : ℂ) * I)⁻¹)
  simp only [neg_neg] at this
  rw [← this]

/-! ### The kernel `((s - p)(s - ζ))⁻¹` -/

theorem integrable_inv_sq_vline {c : ℝ} {p : ℂ} (hp : p.re ≠ c) :
    Integrable fun y : ℝ => (‖(c : ℂ) + y * I - p‖ ^ 2)⁻¹ := by
  have hd : 0 < |c - p.re| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hp))
  obtain ⟨h1, -⟩ := integral_inv_sq_add_sq hd p.im
  refine h1.congr (Eventually.of_forall fun y => ?_)
  simp only
  rw [norm_vline_sub_sq, sq_abs]

theorem integrable_inv_mul_vline {c : ℝ} {p ζ : ℂ} (hp : p.re ≠ c) (hζ : ζ.re ≠ c) :
    Integrable fun y : ℝ => (((c : ℂ) + y * I - p) * ((c : ℂ) + y * I - ζ))⁻¹ := by
  refine ((integrable_inv_sq_vline hp).add (integrable_inv_sq_vline hζ)).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (Continuous.inv₀ (by fun_prop) fun y => mul_ne_zero (vline_sub_ne_zero hp y)
      (vline_sub_ne_zero hζ y)).aestronglyMeasurable
  · have ha : 0 < ‖(c : ℂ) + y * I - p‖ := norm_pos_iff.mpr (vline_sub_ne_zero hp y)
    have hb : 0 < ‖(c : ℂ) + y * I - ζ‖ := norm_pos_iff.mpr (vline_sub_ne_zero hζ y)
    rw [norm_inv, norm_mul]
    set a := ‖(c : ℂ) + y * I - p‖
    set b := ‖(c : ℂ) + y * I - ζ‖
    show (a * b)⁻¹ ≤ (a ^ 2)⁻¹ + (b ^ 2)⁻¹
    rw [inv_le_iff_one_le_mul₀' (by positivity)]
    have : (a ^ 2)⁻¹ + (b ^ 2)⁻¹ = (a ^ 2 + b ^ 2) / (a ^ 2 * b ^ 2) := by field_simp; ring
    rw [this, show a * b * ((a ^ 2 + b ^ 2) / (a ^ 2 * b ^ 2)) = (a ^ 2 + b ^ 2) / (a * b) by
      field_simp, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (a - b)]

/-- The kernel integral through principal values: `∫ ((s - p)(s - ζ))⁻¹ dy` equals
`(PV_p - PV_ζ)/(p - ζ)` where `PV = ∓π` is the principal value of `∫ (c - · + i y)⁻¹`. -/
theorem integral_inv_mul_vline_of_tendsto {c : ℝ} {p ζ : ℂ} (hp : p.re ≠ c) (hζ : ζ.re ≠ c)
    (hpζ : p ≠ ζ) {Vp Vζ : ℂ}
    (hVp : Tendsto (fun T : ℝ => ∫ y in (-T)..T, (((c : ℂ) - p) + y * I)⁻¹) atTop (𝓝 Vp))
    (hVζ : Tendsto (fun T : ℝ => ∫ y in (-T)..T, (((c : ℂ) - ζ) + y * I)⁻¹) atTop (𝓝 Vζ)) :
    ∫ y : ℝ, (((c : ℂ) + y * I - p) * ((c : ℂ) + y * I - ζ))⁻¹ = (Vp - Vζ) / (p - ζ) := by
  have hint := integrable_inv_mul_vline hp hζ
  have hlim := intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hpq : p - ζ ≠ 0 := sub_ne_zero.mpr hpζ
  have hsplit : ∀ T : ℝ, ∫ y in (-T)..T, (((c : ℂ) + y * I - p) * ((c : ℂ) + y * I - ζ))⁻¹ =
      ((∫ y in (-T)..T, (((c : ℂ) - p) + y * I)⁻¹) -
        ∫ y in (-T)..T, (((c : ℂ) - ζ) + y * I)⁻¹) / (p - ζ) := by
    intro T
    have hi1 : IntervalIntegrable (fun y : ℝ => (((c : ℂ) - p) + y * I)⁻¹) volume (-T) T :=
      (Continuous.inv₀ (by fun_prop) fun y => by
        have := vline_sub_ne_zero hp y; ring_nf at this ⊢; exact this).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun y : ℝ => (((c : ℂ) - ζ) + y * I)⁻¹) volume (-T) T :=
      (Continuous.inv₀ (by fun_prop) fun y => by
        have := vline_sub_ne_zero hζ y; ring_nf at this ⊢; exact this).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hi1 hi2, ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun y _ => ?_
    have h1 := vline_sub_ne_zero hp y
    have h2 := vline_sub_ne_zero hζ y
    have h1' : ((c : ℂ) - p) + y * I ≠ 0 := by ring_nf at h1 ⊢; exact h1
    have h2' : ((c : ℂ) - ζ) + y * I ≠ 0 := by ring_nf at h2 ⊢; exact h2
    field_simp
    ring
  have h2 := (hVp.sub hVζ).div_const (p - ζ)
  exact tendsto_nhds_unique hlim (h2.congr fun T => (hsplit T).symm)

/-- `∫ ((s - p)(s - ζ))⁻¹ dy = -2π/(p - ζ)` for `Re ζ < c < Re p`. -/
theorem integral_inv_mul_vline_opposite {c : ℝ} {p ζ : ℂ} (hζ : ζ.re < c) (hp : c < p.re) :
    ∫ y : ℝ, (((c : ℂ) + y * I - p) * ((c : ℂ) + y * I - ζ))⁻¹ = -2 * Real.pi / (p - ζ) := by
  have hpζ : p ≠ ζ := by intro h; rw [h] at hp; linarith
  rw [integral_inv_mul_vline_of_tendsto hp.ne' hζ.ne hpζ
    (tendsto_integral_inv_vline_neg (by simp; linarith))
    (tendsto_integral_inv_vline_pos (by simp; linarith))]
  ring

/-- `∫ ((s - p)(s - ζ))⁻¹ dy = 0` when both points lie right of the line. -/
theorem integral_inv_mul_vline_right {c : ℝ} {p ζ : ℂ} (hζ : c < ζ.re) (hp : c < p.re)
    (hpζ : p ≠ ζ) :
    ∫ y : ℝ, (((c : ℂ) + y * I - p) * ((c : ℂ) + y * I - ζ))⁻¹ = 0 := by
  rw [integral_inv_mul_vline_of_tendsto hp.ne' hζ.ne' hpζ
    (tendsto_integral_inv_vline_neg (by simp; linarith))
    (tendsto_integral_inv_vline_neg (by simp; linarith))]
  simp

/-! ### Cauchy's formula on a vertical strip -/

/-- **Cauchy's formula on a strip.** If `h` is holomorphic and bounded on the closed strip
`a ≤ Re ≤ b` and `h(s)/(s - ζ)` is integrable on both lines, then for `a < Re ζ < b`,
`∫ h(b + i y)/(b + i y - ζ) dy - ∫ h(a + i y)/(a + i y - ζ) dy = 2π h(ζ)`. -/
theorem vline_cauchy_strip {h : ℂ → ℂ} {a b : ℝ} (hab : a < b)
    (hd : ∀ z : ℂ, z.re ∈ Icc a b → DifferentiableAt ℂ h z) {M : ℝ}
    (hM : ∀ z : ℂ, z.re ∈ Icc a b → ‖h z‖ ≤ M) {ζ : ℂ} (hζa : a < ζ.re) (hζb : ζ.re < b)
    (ha : Integrable fun y : ℝ => h (a + y * I) / ((a : ℂ) + y * I - ζ))
    (hb : Integrable fun y : ℝ => h (b + y * I) / ((b : ℂ) + y * I - ζ)) :
    (∫ y : ℝ, h (b + y * I) / ((b : ℂ) + y * I - ζ)) -
      ∫ y : ℝ, h (a + y * I) / ((a : ℂ) + y * I - ζ) = 2 * Real.pi * h ζ := by
  set p : ℂ := ((b + 1 : ℝ) : ℂ) with hp
  have hpre : p.re = b + 1 := by simp [hp]
  have hpζ : ζ - p ≠ 0 := by
    intro h0; have := congrArg re h0; rw [sub_re, hpre, zero_re] at this; linarith
  set φ : ℂ → ℂ := fun s => h s - h ζ * ((ζ - p) / (s - p)) with hφ
  have hφζ : φ ζ = 0 := by simp only [hφ]; rw [div_self hpζ, mul_one, sub_self]
  set k : ℂ → ℂ := dslope φ ζ with hk
  have hk_of_ne : ∀ s, s ≠ ζ → k s = φ s / (s - ζ) := by
    intro s hs; rw [hk, dslope_of_ne _ hs, slope_def_field, hφζ, sub_zero]
  have hsp : ∀ s : ℂ, s.re ≤ b → s - p ≠ 0 := by
    intro s hs h0; have := congrArg re h0; rw [sub_re, hpre, zero_re] at this; linarith
  have hφd : ∀ z : ℂ, z.re ∈ Icc a b → DifferentiableAt ℂ φ z := by
    intro z hz
    exact (hd z hz).sub ((differentiableAt_const _).mul
      ((differentiableAt_const _).div (differentiableAt_id.sub_const p) (hsp z hz.2)))
  have hkd : ∀ z : ℂ, z.re ∈ Icc a b → DifferentiableAt ℂ k z := by
    intro z hz
    by_cases hzζ : z = ζ
    · subst hzζ
      set U : Set ℂ := {s : ℂ | s.re ∈ Ioo a b} with hU
      have hUo : IsOpen U := isOpen_Ioo.preimage continuous_re
      have hφU : DifferentiableOn ℂ φ U := fun s hs =>
        (hφd s ⟨hs.1.le, hs.2.le⟩).differentiableWithinAt
      have hkU := (differentiableOn_dslope (hUo.mem_nhds ⟨hζa, hζb⟩)).mpr hφU
      exact hkU.differentiableAt (hUo.mem_nhds ⟨hζa, hζb⟩)
    · have heq : k =ᶠ[𝓝 z] fun s => φ s / (s - ζ) :=
        (eventually_ne_nhds hzζ).mono fun s hs => hk_of_ne s hs
      exact ((hφd z hz).div (differentiableAt_id.sub_const ζ) (sub_ne_zero.mpr hzζ)).congr_of_eventuallyEq
        heq
  -- the integrands on the two lines
  have hline : ∀ c : ℝ, c ≠ ζ.re → c ≤ b → ∀ y : ℝ, k (c + y * I) =
      h (c + y * I) / ((c : ℂ) + y * I - ζ) -
        h ζ * (ζ - p) * (((c : ℂ) + y * I - p) * ((c : ℂ) + y * I - ζ))⁻¹ := by
    intro c hc hcb y
    have hne : (c : ℂ) + y * I - ζ ≠ 0 := vline_sub_ne_zero (Ne.symm hc) y
    have hne' : (c : ℂ) + y * I ≠ ζ := sub_ne_zero.mp hne
    have hpne : (c : ℂ) + y * I - p ≠ 0 := hsp _ (by simpa using hcb)
    rw [hk_of_ne _ hne']
    simp only [hφ]
    field_simp
  have hpre' : (p.re) ≠ a := by rw [hpre]; linarith
  have hpre'' : (p.re) ≠ b := by rw [hpre]; linarith
  have hKa := integrable_inv_mul_vline (c := a) hpre' (ne_of_gt hζa)
  have hKb := integrable_inv_mul_vline (c := b) hpre'' (ne_of_lt hζb)
  have hia : Integrable fun y : ℝ => k (a + y * I) := by
    refine (ha.sub (hKa.const_mul (h ζ * (ζ - p)))).congr (Eventually.of_forall fun y => ?_)
    exact (hline a (ne_of_lt hζa) hab.le y).symm
  have hib : Integrable fun y : ℝ => k (b + y * I) := by
    refine (hb.sub (hKb.const_mul (h ζ * (ζ - p)))).congr (Eventually.of_forall fun y => ?_)
    exact (hline b (ne_of_gt hζb) le_rfl y).symm
  -- horizontal edges
  set C : ℝ := M + ‖h ζ‖ * ‖ζ - p‖ with hC
  have hedge : ∀ T : ℝ, ‖ζ‖ + 1 ≤ |T| →
      ‖∫ σ in a..b, k (σ + T * I)‖ ≤ C / (|T| - ‖ζ‖) * |b - a| := by
    intro T hT
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun σ hσ => ?_
    rw [uIoc_of_le hab.le] at hσ
    set z : ℂ := σ + T * I with hz
    have hzre : z.re = σ := by simp [hz]
    have hzim : z.im = T := by simp [hz]
    have hzζ : z ≠ ζ := by
      intro h0
      have h1 : T = ζ.im := by rw [← hzim, h0]
      have h2 := abs_im_le_norm ζ
      rw [← h1] at h2
      linarith
    have hpos : 0 < |T| - ‖ζ‖ := by linarith
    have hzζn : |T| - ‖ζ‖ ≤ ‖z - ζ‖ := by
      have h1 := abs_im_le_norm (z - ζ)
      rw [sub_im, hzim] at h1
      have h2 := abs_im_le_norm ζ
      have h3 : |T| - |ζ.im| ≤ |T - ζ.im| := abs_sub_abs_le_abs_sub T ζ.im
      linarith
    have hzp : 1 ≤ ‖z - p‖ := by
      have := abs_re_le_norm (z - p)
      rw [sub_re, hzre, hpre] at this
      have h1 : |σ - (b + 1)| = b + 1 - σ := by
        rw [abs_sub_comm, abs_of_pos (by linarith [hσ.2])]
      linarith [hσ.2]
    have hφz : ‖φ z‖ ≤ C := by
      simp only [hφ]
      have hb1 : ‖h z‖ ≤ M := hM z ⟨by rw [hzre]; exact hσ.1.le, by rw [hzre]; exact hσ.2⟩
      have hb2 : ‖h ζ * ((ζ - p) / (z - p))‖ ≤ ‖h ζ‖ * ‖ζ - p‖ := by
        rw [norm_mul, norm_div]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact div_le_self (norm_nonneg _) hzp
      calc ‖h z - h ζ * ((ζ - p) / (z - p))‖ ≤ ‖h z‖ + ‖h ζ * ((ζ - p) / (z - p))‖ :=
            norm_sub_le _ _
        _ ≤ C := by rw [hC]; linarith
    rw [hk_of_ne z hzζ, norm_div, div_le_div_iff₀ (lt_of_lt_of_le hpos hzζn) hpos]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans hφz
    calc ‖φ z‖ * (|T| - ‖ζ‖) ≤ C * (|T| - ‖ζ‖) := mul_le_mul_of_nonneg_right hφz hpos.le
      _ ≤ C * ‖z - ζ‖ := mul_le_mul_of_nonneg_left hzζn hC0
  have hlim : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 →
      Tendsto (fun j : ℕ => ∫ σ in a..b, k (σ + ((sgn * (j + ‖ζ‖ + 1) : ℝ) : ℂ) * I)) atTop
        (𝓝 0) := by
    intro sgn hsgn
    have habs : ∀ j : ℕ, |sgn * ((j : ℝ) + ‖ζ‖ + 1)| = (j : ℝ) + ‖ζ‖ + 1 := by
      intro j
      have hp0 : (0 : ℝ) < j + ‖ζ‖ + 1 := by positivity
      rcases hsgn with h | h
      · rw [h, one_mul, abs_of_pos hp0]
      · rw [h, neg_one_mul, abs_neg, abs_of_pos hp0]
    refine squeeze_zero_norm (a := fun j : ℕ => C / ((j : ℝ) + 1) * |b - a|) (fun j => ?_) ?_
    · have := hedge (sgn * ((j : ℝ) + ‖ζ‖ + 1))
        (by rw [habs j]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      rw [habs j] at this
      convert this using 2; ring
    · have h1 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      have h2 := (h1.const_mul C).mul_const |b - a|
      simp only [mul_zero, zero_mul] at h2
      refine h2.congr fun j => ?_
      ring
  have hT : Tendsto (fun j : ℕ => ((j : ℝ) + ‖ζ‖ + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hvert : (∫ t : ℝ, k (a + t * I)) = ∫ t : ℝ, k (b + t * I) := by
    refine integral_vertical_eq_of_tendsto (f := k) hab.le ?_ ?_ hia hib hT hT ?_ ?_
    · exact fun z hz => (hkd z hz).continuousAt.continuousWithinAt
    · exact fun z hz => hkd z ⟨hz.1.le, hz.2.le⟩
    · have h := hlim 1 (Or.inl rfl)
      simp only [one_mul] at h
      exact h
    · have h := hlim (-1) (Or.inr rfl)
      simp only [neg_one_mul, ofReal_neg] at h
      refine h.congr fun j => ?_
      push_cast
      ring_nf
  have hA : (∫ t : ℝ, k (a + t * I)) = ∫ y : ℝ, h (a + y * I) / ((a : ℂ) + y * I - ζ) := by
    rw [integral_congr_ae (Eventually.of_forall fun y => hline a (ne_of_lt hζa) hab.le y),
      integral_sub ha (hKa.const_mul _), MeasureTheory.integral_const_mul,
      integral_inv_mul_vline_right hζa (by rw [hpre]; linarith)
        (by intro h0; rw [← h0, hpre] at hζb; linarith), mul_zero, sub_zero]
  have hB : (∫ t : ℝ, k (b + t * I)) =
      (∫ y : ℝ, h (b + y * I) / ((b : ℂ) + y * I - ζ)) - 2 * Real.pi * h ζ := by
    rw [integral_congr_ae (Eventually.of_forall fun y => hline b (ne_of_gt hζb) le_rfl y),
      integral_sub hb (hKb.const_mul _), MeasureTheory.integral_const_mul,
      integral_inv_mul_vline_opposite hζb (by rw [hpre]; linarith)]
    have hpζ' : p - ζ ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.mpr hpζ
    have e : h ζ * (ζ - p) * (-2 * (Real.pi : ℂ) / (p - ζ)) = 2 * Real.pi * h ζ := by
      rw [← neg_sub p ζ]
      field_simp
    rw [e]
  rw [← hA, hvert, hB]
  ring

end PGM
