import PLAStochastic.ForMathlib.Probability.Hellinger.Observables
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Translation estimates from actual integrable derivatives

The proof integrates the fundamental theorem of calculus over the unit interval
and then uses translation invariance of Lebesgue measure. In particular the
`L²` estimate applies to square roots of strictly positive smoothed densities.
-/

set_option autoImplicit false

namespace MeasureTheory

noncomputable section

open Set

theorem integral_sq_le_integral_sq_of_probability
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {g : α → ℝ} (hg : MemLp g 2 μ) : (∫ x, g x ∂μ) ^ 2 ≤ ∫ x, g x ^ 2 ∂μ := by
  have h1 : MemLp (fun _ : α => (1 : ℝ)) 2 μ := memLp_const 1
  have hn : ‖h1.toLp (fun _ : α => (1 : ℝ))‖ = 1 := by
    have h := ProbabilityTheory.HellingerDensity.norm_toLp_sq h1
    simp only [one_pow, integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    nlinarith [norm_nonneg (h1.toLp (fun _ : α => (1 : ℝ)))]
  have h := abs_real_inner_le_norm (hg.toLp g) (h1.toLp (fun _ : α => (1 : ℝ)))
  rw [ProbabilityTheory.HellingerDensity.inner_toLp_eq_integral_mul hg h1, hn,
    mul_one] at h
  simp only [mul_one] at h
  have he := ProbabilityTheory.HellingerDensity.norm_toLp_sq hg
  nlinarith [sq_abs (∫ x, g x ∂μ), abs_nonneg (∫ x, g x ∂μ), norm_nonneg (hg.toLp g)]

theorem integrable_translate_prod_unit {g : ℝ → ℝ}
    (hg : Measurable g) (hgi : Integrable g volume) (s : ℝ) :
    Integrable (fun z : ℝ × ℝ => g (z.1 + s * z.2))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
  have hm : Measurable (fun z : ℝ × ℝ => g (z.1 + s * z.2)) :=
    hg.comp (measurable_fst.add (measurable_const.mul measurable_snd))
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun t => hgi.comp_add_right (s * t)
  · have he : (fun t => ∫ x, ‖g (x + s * t)‖) = fun _ : ℝ => ∫ x, ‖g x‖ := by
      funext t
      exact integral_add_right_eq_self (fun x => ‖g x‖) (s * t)
    rw [he]
    exact integrable_const _

theorem integral_translate_prod_unit {g : ℝ → ℝ}
    (hg : Measurable g) (hgi : Integrable g volume) (s : ℝ) :
    (∫ x, ∫ t in Ioc (0 : ℝ) 1, g (x + s * t)) = ∫ x, g x := by
  rw [integral_integral_swap (integrable_translate_prod_unit hg hgi s)]
  simp only [integral_add_right_eq_self, integral_const,
    Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
    ENNReal.ofReal_one, ENNReal.toReal_one, smul_eq_mul, one_mul]

set_option backward.isDefEq.respectTransparency.types false in
theorem translation_increment_eq_integral
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hi : Integrable f' volume) (x s : ℝ) :
    f (x + s) - f x = s * ∫ t in Ioc (0 : ℝ) 1, f' (x + s * t) := by
  by_cases hs : s = 0
  · simp [hs]
  have hd : ∀ t, HasDerivAt (fun t => f (x + s * t)) (s * f' (x + s * t)) t := by
    intro t
    convert (hf (x + s * t)).comp t
      ((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul s)) using 1 <;>
      first | rfl | simp [mul_comm]
  have hint : IntervalIntegrable (fun t => s * f' (x + s * t)) volume 0 1 :=
    ((hi.comp_add_left x).comp_mul_left' hs).intervalIntegrable.const_mul s
  have he := (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hint).symm
  simpa only [intervalIntegral.integral_of_le zero_le_one, zero_mul, mul_zero,
    add_zero, mul_one, integral_const_mul] using he

theorem integral_abs_translation_sub_le
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hm : Measurable f') (hi : Integrable f' volume) (hfi : Integrable f volume)
    (s : ℝ) :
    (∫ x, |f (x + s) - f x|) ≤ |s| * ∫ x, |f' x| := by
  have hmabs : Measurable (fun x => |f' x|) := by simpa only [Real.norm_eq_abs] using hm.norm
  have hint := (integrable_translate_prod_unit hmabs hi.abs s).integral_prod_left
  calc
    (∫ x, |f (x + s) - f x|) ≤
        ∫ x, |s| * ∫ t in Ioc (0 : ℝ) 1, |f' (x + s * t)| := by
      apply integral_mono ((hfi.comp_add_right s).sub hfi).abs (hint.const_mul _)
      intro x
      change |f (x + s) - f x| ≤ |s| * ∫ t in Ioc (0 : ℝ) 1, |f' (x + s * t)|
      rw [translation_increment_eq_integral hf hi x s, abs_mul]
      have hb := norm_integral_le_integral_norm
        (μ := volume.restrict (Ioc (0 : ℝ) 1)) (fun t => f' (x + s * t))
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using hb) (abs_nonneg s)
    _ = |s| * ∫ x, |f' x| := by
      rw [integral_const_mul, integral_translate_prod_unit hmabs hi.abs s]

theorem integral_abs_translation_remainder_le
    {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hm' : Measurable f') (hm'' : Measurable f'')
    (hi : Integrable f volume) (hi' : Integrable f' volume) (hi'' : Integrable f'' volume)
    (s : ℝ) :
    (∫ x, |f (x + s) - f x - s * f' x|) ≤ s ^ 2 * ∫ x, |f'' x| := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  have hj : Integrable (fun z : ℝ × ℝ => f' (z.1 + s * z.2) - f' z.1)
      (volume.prod μ) :=
    (integrable_translate_prod_unit hm' hi' s).sub (hi'.comp_fst μ)
  have hint := hj.abs.integral_prod_left
  have hpoint : ∀ x, f (x + s) - f x - s * f' x =
      s * ∫ t in Ioc (0 : ℝ) 1, (f' (x + s * t) - f' x) := by
    intro x
    by_cases hs : s = 0
    · simp [hs]
    rw [translation_increment_eq_integral hf hi' x s,
      integral_sub ((hi'.comp_add_left x).comp_mul_left' hs).integrableOn (integrable_const _)]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
      sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, smul_eq_mul, one_mul]
    ring
  calc
    (∫ x, |f (x + s) - f x - s * f' x|) ≤
        ∫ x, |s| * ∫ t, |f' (x + s * t) - f' x| ∂μ := by
      apply integral_mono (((hi.comp_add_right s).sub hi).sub (hi'.const_mul s)).abs
        (hint.const_mul _)
      intro x
      change |f (x + s) - f x - s * f' x| ≤ |s| * ∫ t, |f' (x + s * t) - f' x| ∂μ
      rw [hpoint x, abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := μ) (fun t => f' (x + s * t) - f' x))
        (abs_nonneg s)
    _ = |s| * ∫ t, (∫ x, |f' (x + s * t) - f' x|) ∂μ := by
      rw [integral_const_mul, integral_integral_swap hj.abs]
    _ ≤ |s| * (|s| * ∫ x, |f'' x|) := by
      apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg s)
      have hb : ∀ᵐ t ∂μ, (∫ x, |f' (x + s * t) - f' x|) ≤ |s| * ∫ x, |f'' x| := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht1 : |t| ≤ 1 := by rw [abs_of_pos ht.1]; exact ht.2
        calc
          (∫ x, |f' (x + s * t) - f' x|) ≤ |s * t| * ∫ x, |f'' x| :=
            integral_abs_translation_sub_le hf' hm'' hi'' hi' (s * t)
          _ ≤ |s| * ∫ x, |f'' x| := by
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right
              (by simpa using mul_le_mul_of_nonneg_left ht1 (abs_nonneg s))
              (integral_nonneg fun _ => abs_nonneg _)
      simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul] using
        integral_mono_ae hj.abs.integral_prod_right (integrable_const _) hb
    _ = _ := by rw [← mul_assoc, ← sq_abs]; ring

set_option backward.isDefEq.respectTransparency.types false in
theorem integral_sq_translation_sub_le
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hm : Measurable f') (hi : Integrable (fun x => f' x ^ 2) volume)
    (hfi : MemLp f 2 volume) (s : ℝ) :
    (∫ x, (f (x + s) - f x) ^ 2) ≤ s ^ 2 * ∫ x, f' x ^ 2 := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have : IsProbabilityMeasure μ := ⟨by simp [μ, Real.volume_Ioc]⟩
  by_cases hs : s = 0
  · simp [hs]
  have hsec : ∀ x, MemLp (fun t => f' (x + s * t)) 2 μ := by
    intro x
    apply (memLp_two_iff_integrable_sq
      (hm.comp (measurable_const.add (measurable_const.mul measurable_id))).aestronglyMeasurable).2
    exact ((hi.comp_add_left x).comp_mul_left' hs).integrableOn
  have hftc : ∀ x, f (x + s) - f x = s * ∫ t, f' (x + s * t) ∂μ := by
    intro x
    have hd : ∀ t, HasDerivAt (fun t => f (x + s * t)) (s * f' (x + s * t)) t := by
      intro t
      convert (hf (x + s * t)).comp t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul s)) using 1 <;>
        first | rfl | simp [mul_comm]
    have hint : IntervalIntegrable (fun t => s * f' (x + s * t)) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact ((hsec x).integrable (by norm_num)).const_mul s
    have he := (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hint).symm
    simpa only [intervalIntegral.integral_of_le zero_le_one, zero_mul, mul_zero,
      add_zero, mul_one, integral_const_mul, μ] using he
  have hd : ∀ x, (f (x + s) - f x) ^ 2 ≤ s ^ 2 * ∫ t, f' (x + s * t) ^ 2 ∂μ := by
    intro x
    rw [hftc x, mul_pow]
    exact mul_le_mul_of_nonneg_left
      (integral_sq_le_integral_sq_of_probability (hsec x)) (sq_nonneg s)
  have hint := (integrable_translate_prod_unit (hm.pow_const 2) hi s).integral_prod_left
  calc
    (∫ x, (f (x + s) - f x) ^ 2) ≤
        ∫ x, s ^ 2 * ∫ t, f' (x + s * t) ^ 2 ∂μ := by
      apply integral_mono ?_ (hint.const_mul _) hd
      exact ((hfi.comp_measurePreserving (measurePreserving_add_right volume s)).sub hfi).integrable_sq
    _ = s ^ 2 * ∫ x, f' x ^ 2 := by
      rw [integral_const_mul, integral_translate_prod_unit (hm.pow_const 2) hi s]

end

end MeasureTheory
