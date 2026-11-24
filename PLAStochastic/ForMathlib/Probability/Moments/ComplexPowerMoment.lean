import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Complex power moments of a positive random variable

For a positive random variable all of whose real powers are integrable, the complex
moment `q ↦ ∫ X ^ q` is entire: the derivative `X ^ q log X` is dominated on unit discs
by two real powers. For `Re q < 0`, Tonelli–Fubini with `x ^ q = -q ∫_x^∞ t ^ (q-1) dt`
gives the Mellin form against the survival function.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- Two real powers dominate the derivative of `q ↦ x ^ q` on the strip `|Re q| + 1 ≤ b`. -/
theorem norm_ofReal_cpow_mul_log_le {x : ℝ} (hx : 0 < x) {q : ℂ} {b : ℝ}
    (hb : |q.re| + 1 ≤ b) :
    ‖(x : ℂ) ^ q * Complex.log x‖ ≤ x ^ b + x ^ (-b) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, ← Complex.ofReal_log hx.le,
    Complex.norm_real, Real.norm_eq_abs]
  have hre := abs_le.mp (show |q.re| ≤ b - 1 by linarith)
  rcases le_or_gt 1 x with hx1 | hx1
  · have hlog : |Real.log x| ≤ x := by
      rw [abs_of_nonneg (Real.log_nonneg hx1)]
      linarith [Real.log_le_sub_one_of_pos hx]
    have hpow : x ^ q.re ≤ x ^ (b - 1) := Real.rpow_le_rpow_of_exponent_le hx1 hre.2
    have hmain : x ^ q.re * |Real.log x| ≤ x ^ b := by
      calc
        x ^ q.re * |Real.log x| ≤ x ^ (b - 1) * x :=
          mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
        _ = x ^ b := by
          rw [Real.rpow_sub_one hx.ne', div_mul_cancel₀ _ hx.ne']
    linarith [Real.rpow_nonneg hx.le (-b)]
  · have hlog : |Real.log x| ≤ x⁻¹ := by
      rw [abs_of_nonpos (Real.log_nonpos hx.le hx1.le), ← Real.log_inv]
      linarith [Real.log_le_sub_one_of_pos (inv_pos.mpr hx)]
    have hpow : x ^ q.re ≤ x ^ (1 - b) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1.le (by linarith [hre.1])
    have hmain : x ^ q.re * |Real.log x| ≤ x ^ (-b) := by
      calc
        x ^ q.re * |Real.log x| ≤ x ^ (1 - b) * x⁻¹ :=
          mul_le_mul hpow hlog (abs_nonneg _) (by positivity)
        _ = x ^ (-b) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
          ring_nf
    linarith [Real.rpow_nonneg hx.le b]

/-- If every real power of a positive random variable is integrable, its complex moment
function is entire. -/
theorem differentiable_integral_ofReal_cpow (hX : AEMeasurable X μ)
    (hpos : ∀ᵐ ω ∂μ, 0 < X ω) (hint : ∀ p : ℝ, Integrable (fun ω => X ω ^ p) μ) :
    Differentiable ℂ (fun q : ℂ => ∫ ω, (X ω : ℂ) ^ q ∂μ) := by
  intro q₀
  set b : ℝ := |q₀.re| + 2
  have hXc : AEMeasurable (fun ω => (X ω : ℂ)) μ :=
    Complex.measurable_ofReal.comp_aemeasurable hX
  have hmeas (q : ℂ) : AEStronglyMeasurable (fun ω => (X ω : ℂ) ^ q) μ :=
    (hXc.pow_const q).aestronglyMeasurable
  have hint₀ : Integrable (fun ω => (X ω : ℂ) ^ q₀) μ := by
    refine (hint q₀.re).mono' (hmeas q₀) ?_
    filter_upwards [hpos] with ω hω
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hω]
  have hF'meas : AEStronglyMeasurable
      (fun ω => (X ω : ℂ) ^ q₀ * Complex.log (X ω)) μ :=
    ((hXc.pow_const q₀).mul hXc.clog).aestronglyMeasurable
  have hbound : ∀ᵐ ω ∂μ, ∀ q ∈ Metric.ball q₀ 1,
      ‖(X ω : ℂ) ^ q * Complex.log (X ω)‖ ≤ X ω ^ b + X ω ^ (-b) := by
    filter_upwards [hpos] with ω hω q hq
    apply norm_ofReal_cpow_mul_log_le hω
    have hd : |q.re - q₀.re| < 1 := by
      calc
        |q.re - q₀.re| = |(q - q₀).re| := by rw [Complex.sub_re]
        _ ≤ ‖q - q₀‖ := Complex.abs_re_le_norm _
        _ < 1 := by rwa [← dist_eq_norm]
    have h₁ := abs_sub_abs_le_abs_sub q.re q₀.re
    linarith
  have hdiff : ∀ᵐ ω ∂μ, ∀ q ∈ Metric.ball q₀ 1,
      HasDerivAt (fun q => (X ω : ℂ) ^ q) ((X ω : ℂ) ^ q * Complex.log (X ω)) q := by
    filter_upwards [hpos] with ω hω q _
    exact (Complex.hasStrictDerivAt_const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hω.ne'))).hasDerivAt
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds q₀ one_pos)
    (Eventually.of_forall hmeas) hint₀ hF'meas hbound ((hint b).add (hint (-b))) hdiff).2
    |>.differentiableAt

/-- The Mellin form of a negative complex moment against the strict survival function. -/
theorem integral_ofReal_cpow_eq_mellin [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
    (hpos : ∀ᵐ ω ∂μ, 0 < X ω) {q : ℂ} (hq : q.re < 0)
    (hint : Integrable (fun ω => X ω ^ q.re) μ) :
    ∫ ω, (X ω : ℂ) ^ q ∂μ =
      q * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((μ.real {ω | t < X ω} : ℂ) - 1) := by
  set Y : Ω → ℝ := hX.mk X
  have hY : Measurable Y := hX.measurable_mk
  have hXY : X =ᵐ[μ] Y := hX.ae_eq_mk
  have hYpos : ∀ᵐ ω ∂μ, 0 < Y ω := by
    filter_upwards [hpos, hXY] with ω h₁ h₂
    rwa [← h₂]
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hq
  have hre : (q - 1).re < -1 := by
    rw [Complex.sub_re, Complex.one_re]
    linarith
  let F : Ω → ℝ → ℂ := fun ω t => if Y ω ≤ t then (t : ℂ) ^ (q - 1) else 0
  have hFind (ω : Ω) :
      (fun t => F ω t) = (Ici (Y ω)).indicator (fun t : ℝ => (t : ℂ) ^ (q - 1)) := by
    funext t
    simp only [F, indicator_apply, mem_Ici]
  have hFnorm (ω : Ω) :
      (fun t => ‖F ω t‖) = (Ici (Y ω)).indicator (fun t : ℝ => ‖(t : ℂ) ^ (q - 1)‖) := by
    funext t
    simp only [F, indicator_apply, mem_Ici]
    split_ifs <;> simp
  have hrestrict {ω : Ω} (hω : 0 < Y ω) :
      (volume.restrict (Ioi (0 : ℝ))).restrict (Ici (Y ω)) = volume.restrict (Ici (Y ω)) := by
    rw [Measure.restrict_restrict measurableSet_Ici,
      inter_eq_left.mpr (Ici_subset_Ioi.mpr hω)]
  -- The inner time integral of a fixed path.
  have hinner {ω : Ω} (hω : 0 < Y ω) :
      ∫ t in Ioi (0 : ℝ), F ω t = -(Y ω : ℂ) ^ q / q := by
    rw [hFind ω, integral_indicator measurableSet_Ici, hrestrict hω, integral_Ici_eq_integral_Ioi,
      integral_Ioi_cpow_of_lt hre hω, sub_add_cancel]
  have hinner_norm {ω : Ω} (hω : 0 < Y ω) :
      ∫ t in Ioi (0 : ℝ), ‖F ω t‖ = Y ω ^ q.re / (-q.re) := by
    rw [hFnorm ω, integral_indicator measurableSet_Ici, hrestrict hω,
      integral_Ici_eq_integral_Ioi]
    have hre' : q.re - 1 < -1 := by linarith
    calc
      ∫ t in Ioi (Y ω), ‖(t : ℂ) ^ (q - 1)‖ = ∫ t in Ioi (Y ω), t ^ (q.re - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change ‖(t : ℂ) ^ (q - 1)‖ = t ^ (q.re - 1)
        rw [Complex.norm_cpow_eq_rpow_re_of_pos (hω.trans ht), Complex.sub_re, Complex.one_re]
      _ = Y ω ^ q.re / (-q.re) := by
        rw [integral_Ioi_rpow_of_lt hre' hω, sub_add_cancel, neg_div, div_neg]
  have hinner_int {ω : Ω} (hω : 0 < Y ω) :
      Integrable (fun t => F ω t) (volume.restrict (Ioi (0 : ℝ))) := by
    rw [hFind ω, integrable_indicator_iff measurableSet_Ici, IntegrableOn, hrestrict hω]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_Ioi_cpow_of_lt hre hω)
  -- Joint integrability on the product space.
  have hFmeas : Measurable (Function.uncurry F) := by
    apply Measurable.ite (measurableSet_le (hY.comp measurable_fst) measurable_snd)
    · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
    · exact measurable_const
  have hYint : Integrable (fun ω => Y ω ^ q.re) μ :=
    hint.congr (hXY.fun_comp fun x => x ^ q.re)
  have hFint : Integrable (Function.uncurry F) (μ.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff hFmeas.aestronglyMeasurable]
    constructor
    · filter_upwards [hYpos] with ω hω
      exact hinner_int hω
    · refine (hYint.div_const (-q.re)).congr ?_
      filter_upwards [hYpos] with ω hω
      exact (hinner_norm hω).symm
  -- The inner path integral at a fixed time.
  have houter (t : ℝ) :
      ∫ ω, F ω t ∂μ = (t : ℂ) ^ (q - 1) * (1 - (μ.real {ω | t < X ω} : ℂ)) := by
    have hset : MeasurableSet {ω | Y ω ≤ t} := measurableSet_le hY measurable_const
    have hF : (fun ω => F ω t) = {ω | Y ω ≤ t}.indicator (fun _ => (t : ℂ) ^ (q - 1)) := by
      funext ω
      simp only [F, indicator_apply]
      rfl
    have hcompl : {ω | Y ω ≤ t} = {ω | t < Y ω}ᶜ := by
      ext ω
      simp [not_lt]
    have hsurv : μ.real {ω | t < Y ω} = μ.real {ω | t < X ω} := by
      apply measureReal_congr
      filter_upwards [hXY] with ω hω
      change (t < Y ω) = (t < X ω)
      rw [hω]
    rw [hF, integral_indicator_const _ hset, hcompl,
      measureReal_compl (measurableSet_lt measurable_const hY), probReal_univ, hsurv,
      Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, mul_comm]
  calc
    ∫ ω, (X ω : ℂ) ^ q ∂μ = ∫ ω, -q * (∫ t in Ioi (0 : ℝ), F ω t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hXY, hYpos] with ω h₁ h₂
      rw [hinner h₂, h₁]
      field_simp
    _ = -q * ∫ t in Ioi (0 : ℝ), ∫ ω, F ω t ∂μ := by
      rw [integral_const_mul, integral_integral_swap hFint]
    _ = q * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((μ.real {ω | t < X ω} : ℂ) - 1) := by
      simp_rw [houter]
      rw [← neg_neg (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((μ.real {ω | t < X ω} : ℂ) - 1)),
        ← integral_neg]
      have : ∀ t : ℝ, -((t : ℂ) ^ (q - 1) * ((μ.real {ω | t < X ω} : ℂ) - 1)) =
          (t : ℂ) ^ (q - 1) * (1 - (μ.real {ω | t < X ω} : ℂ)) := fun t => by ring
      simp_rw [this]
      ring

end BrownianAffine
