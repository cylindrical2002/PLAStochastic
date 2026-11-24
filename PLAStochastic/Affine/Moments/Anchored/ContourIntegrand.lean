import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ReciprocalSinhMoments
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds

/-! # The regularized contour integrand for anchored integer moments -/
noncomputable section
open MeasureTheory Filter Set Complex
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def momentCosh (z : ℂ) : ℂ := Complex.cosh (Real.pi * z / 2)

def anchoredMomentContour (q : ℕ) (z : ℂ) : ℂ :=
  z * (z + I) ^ q * (z - I) ^ (q - 1) / dslope momentCosh I z

theorem momentCosh_I : momentCosh I = 0 := by
  unfold momentCosh
  rw [show (Real.pi : ℂ) * I / 2 = ((Real.pi : ℂ) / 2) * I by ring,
    Complex.cosh_mul_I, Complex.cos_pi_div_two]

theorem momentCosh_zero_in_strip {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1)
    (hz : momentCosh z = 0) : z = I := by
  unfold momentCosh at hz
  rw [← Complex.cos_mul_I] at hz
  obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hz
  have hre := congrArg Complex.re hk
  have him := congrArg Complex.im hk
  norm_num [Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im] at hre him
  have hzre : z.re = 0 := by nlinarith [Real.pi_pos]
  have hzim : z.im = -(2 * (k : ℝ) + 1) := by nlinarith [Real.pi_pos]
  have hklo : (-1 : ℝ) ≤ k := by linarith
  have hkhi : (k : ℝ) < 0 := by linarith
  have hklo' : (-1 : ℤ) ≤ k := by exact_mod_cast hklo
  have hkhi' : k < 0 := by exact_mod_cast hkhi
  have hkeq : k = -1 := by omega
  apply Complex.ext
  · simpa only [Complex.I_re] using hzre
  · norm_num [hkeq] at hzim
    exact hzim

theorem dslope_momentCosh_I : dslope momentCosh I I = (Real.pi : ℂ) * I / 2 := by
  rw [dslope_same]
  have hd := (Complex.hasDerivAt_cosh _).comp I
    (((hasDerivAt_id I).const_mul (Real.pi : ℂ)).div_const 2)
  change HasDerivAt momentCosh _ I at hd
  rw [hd.deriv]
  simp only [id_eq, mul_one]
  rw [show (Real.pi : ℂ) * I / 2 = ((Real.pi : ℂ) / 2) * I by ring,
    Complex.sinh_mul_I, Complex.sin_pi_div_two]
  ring

theorem dslope_momentCosh_ne_zero {z : ℂ} (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1) :
    dslope momentCosh I z ≠ 0 := by
  by_cases hz : z = I
  · rw [hz, dslope_momentCosh_I]
    exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero)
      (by norm_num)
  · intro hd
    have h := sub_smul_dslope momentCosh I z
    rw [hd, smul_zero, momentCosh_I, sub_zero] at h
    exact hz (momentCosh_zero_in_strip hz0 hz1 h.symm)

theorem differentiable_dslope_momentCosh : Differentiable ℂ (dslope momentCosh I) := by
  rw [← differentiableOn_univ]
  apply (Complex.differentiableOn_dslope (s := univ) (by simp)).mpr
  unfold momentCosh
  fun_prop

theorem differentiableAt_anchoredMomentContour (q : ℕ) {z : ℂ}
    (hz0 : 0 ≤ z.im) (hz1 : z.im ≤ 1) : DifferentiableAt ℂ (anchoredMomentContour q) z := by
  unfold anchoredMomentContour
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => z * (z + I) ^ q * (z - I) ^ (q - 1)) z).div
    (differentiable_dslope_momentCosh z) (dslope_momentCosh_ne_zero hz0 hz1)

theorem anchoredMomentContour_eq {q : ℕ} (hq : 0 < q) {z : ℂ} (hz : z ≠ I) :
    anchoredMomentContour q z = z * (z ^ 2 + 1) ^ q / momentCosh z := by
  have hg : momentCosh z = (z - I) * dslope momentCosh I z := by
    simpa only [smul_eq_mul, momentCosh_I, sub_zero] using (sub_smul_dslope momentCosh I z).symm
  have hp : z ^ 2 + 1 = (z - I) * (z + I) := by
    ring_nf
    rw [I_sq]
    ring
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  unfold anchoredMomentContour
  rw [hg, hp, mul_pow]
  simp only [Nat.succ_sub_one]
  by_cases hd : dslope momentCosh I z = 0
  · simp [hd]
  · have hz' : z - I ≠ 0 := sub_ne_zero.mpr hz
    simp only [pow_succ]
    field_simp

/-- The regularized integrand satisfies the actual rectangle Cauchy identity. -/
theorem anchoredMomentContour_rectangle (q : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ x in 0..R, anchoredMomentContour q (x : ℂ)) -
      (∫ x in 0..R, anchoredMomentContour q ((x : ℂ) + I)) +
      I * (∫ y in (0 : ℝ)..1, anchoredMomentContour q ((R : ℂ) + y * I)) -
      I * (∫ y in (0 : ℝ)..1, anchoredMomentContour q (y * I)) = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (anchoredMomentContour q) 0 ((R : ℂ) + I) (by
      intro z hz
      simp only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.ofReal_re,
        Complex.I_re, add_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
        uIcc_of_le hR, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), Complex.mem_reProdIm,
        mem_Icc] at hz
      exact (differentiableAt_anchoredMomentContour q hz.2.1 hz.2.2).differentiableWithinAt)
  simpa only [Complex.zero_re, Complex.zero_im, Complex.add_re, Complex.ofReal_re,
    Complex.I_re, add_zero, Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add,
    Complex.ofReal_zero, zero_mul, Complex.ofReal_one, one_mul, smul_eq_mul] using h

/-- Reverse triangle inequality gives a uniform lower bound independent of the imaginary part. -/
theorem sinh_re_le_norm_cosh (z : ℂ) : Real.sinh z.re ≤ ‖Complex.cosh z‖ := by
  have h := norm_sub_norm_le (Complex.exp z) (-Complex.exp (-z))
  simp only [norm_neg, Complex.norm_exp, Complex.neg_re, sub_neg_eq_add] at h
  rw [Real.sinh_eq, Complex.cosh, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  exact div_le_div_of_nonneg_right h (by norm_num)

theorem exp_quarter_le_sinh {x : ℝ} (hx : 1 ≤ x) : Real.exp x / 4 ≤ Real.sinh x := by
  have hp := Real.add_one_le_exp x
  have hn : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith

theorem anchoredMomentContour_bound {q : ℕ} (hq : 0 < q) {R y : ℝ}
    (hR : 1 ≤ R) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖anchoredMomentContour q ((R : ℂ) + y * I)‖ ≤
      8 * (5 : ℝ) ^ q * R ^ (2 * q + 1) * Real.exp (-(Real.pi / 2) * R) := by
  let z : ℂ := R + y * I
  have hR0 : 0 ≤ R := by linarith
  have hn : ‖z‖ ≤ 2 * R := by
    have h := norm_add_le (R : ℂ) ((y : ℂ) * I)
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hR0, abs_of_nonneg hy0] at h
    dsimp only [z]
    linarith
  have hn2 : ‖z ^ 2 + 1‖ ≤ 5 * R ^ 2 := by
    calc
      _ ≤ ‖z‖ ^ 2 + 1 := by simpa only [Complex.norm_pow, norm_one] using norm_add_le (z ^ (2 : ℕ)) (1 : ℂ)
      _ ≤ (2 * R) ^ 2 + 1 := by gcongr
      _ ≤ _ := by nlinarith
  have hz : z ≠ I := by
    intro he
    have h := congrArg Complex.re he
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero] at h
    linarith
  have hr : (Real.pi * z / 2).re = Real.pi / 2 * R := by simp [z]; ring
  have hx : 1 ≤ Real.pi / 2 * R := by
    nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr hR) Real.pi_pos.le]
  have hd : Real.exp (Real.pi / 2 * R) / 4 ≤ ‖momentCosh z‖ := by
    exact (exp_quarter_le_sinh hx).trans (hr ▸ sinh_re_le_norm_cosh (Real.pi * z / 2))
  have hdi : ‖momentCosh z‖⁻¹ ≤ 4 * Real.exp (-(Real.pi / 2 * R)) := by
    calc
      _ = 1 / ‖momentCosh z‖ := by rw [one_div]
      _ ≤ 1 / (Real.exp (Real.pi / 2 * R) / 4) :=
        one_div_le_one_div_of_le (by positivity) hd
      _ = 4 * Real.exp (-(Real.pi / 2 * R)) := by rw [Real.exp_neg]; field_simp
  change ‖anchoredMomentContour q z‖ ≤ _
  rw [anchoredMomentContour_eq hq hz, norm_div, norm_mul, Complex.norm_pow, div_eq_mul_inv]
  calc
    _ ≤ (2 * R * (5 * R ^ 2) ^ q) * (4 * Real.exp (-(Real.pi / 2 * R))) := by
      apply mul_le_mul _ hdi (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
      exact mul_le_mul hn (pow_le_pow_left₀ (norm_nonneg _) hn2 q) (by positivity) (by positivity)
    _ = _ := by simp only [mul_pow, ← pow_mul, pow_succ, neg_mul]; ring

theorem tendsto_anchoredMomentContour_bound (q : ℕ) :
    Tendsto (fun R : ℝ => 8 * (5 : ℝ) ^ q * R ^ (2 * q + 1) *
      Real.exp (-(Real.pi / 2) * R)) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
    ((2 * q + 1 : ℕ) : ℝ) (Real.pi / 2) (by positivity)
  simpa only [Real.rpow_natCast, mul_zero, ← mul_assoc] using h.const_mul (8 * (5 : ℝ) ^ q)

/-- The remote vertical side vanishes with an explicit bound uniform in its height. -/
theorem tendsto_anchoredMomentContour_vertical {q : ℕ} (hq : 0 < q) :
    Tendsto (fun R : ℝ => ∫ y in (0 : ℝ)..1, anchoredMomentContour q ((R : ℂ) + y * I))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (tendsto_anchoredMomentContour_bound q)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := 8 * (5 : ℝ) ^ q * R ^ (2 * q + 1) * Real.exp (-(Real.pi / 2) * R))
    (fun y hy => anchoredMomentContour_bound hq hR
      (by have := hy.1; simpa using this.le) (by simpa using hy.2))
  simpa only [sub_zero, abs_one, mul_one] using h

theorem continuous_anchoredMomentContour_horizontal (q : ℕ) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Continuous (fun R : ℝ => anchoredMomentContour q ((R : ℂ) + y * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro R
  have h := (differentiableAt_anchoredMomentContour q
    (z := (R : ℂ) + y * I) (by simpa using hy0) (by simpa using hy1)).continuousAt
  exact ContinuousAt.comp (f := fun R : ℝ => (R : ℂ) + y * I) (g := anchoredMomentContour q) (x := R) h (by fun_prop)

theorem integrableOn_anchoredMomentContour_horizontal {q : ℕ} (hq : 0 < q) {y : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    IntegrableOn (fun R : ℝ => anchoredMomentContour q ((R : ℂ) + y * I)) (Ioi 0) := by
  have hc := continuous_anchoredMomentContour_horizontal q hy0 hy1
  have hB : IntegrableOn (fun R : ℝ => 8 * (5 : ℝ) ^ q * R ^ (2 * q + 1) *
      Real.exp (-(Real.pi / 2) * R)) (Ioi 0) := by
    have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := ((2 * q + 1 : ℕ) : ℝ)) (b := Real.pi / 2)
      (by have := Nat.cast_nonneg (α := ℝ) (2 * q + 1); linarith) (by norm_num) (by positivity)).const_mul (8 * (5 : ℝ) ^ q)
    simpa only [Real.rpow_one, Real.rpow_natCast, ← mul_assoc] using! h
  have ht : IntegrableOn (fun R : ℝ => anchoredMomentContour q ((R : ℂ) + y * I)) (Ioi 1) := by
    refine (hB.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).mono'
      hc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
    exact anchoredMomentContour_bound hq hR.le hy0 hy1
  have hb : IntegrableOn (fun R : ℝ => anchoredMomentContour q ((R : ℂ) + y * I)) (Ioc 0 1) :=
    (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Ioc_subset_Icc_self
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using hb.union ht

/-- The finite Cauchy identities converge to the infinite contour shift. -/
theorem anchoredMomentContour_shift {q : ℕ} (hq : 0 < q) :
    (∫ x : ℝ in Ioi 0, anchoredMomentContour q (x : ℂ)) -
      I * (∫ y in (0 : ℝ)..1, anchoredMomentContour q (y * I)) =
      ∫ x : ℝ in Ioi 0, anchoredMomentContour q ((x : ℂ) + I) := by
  have hb : IntegrableOn (fun x : ℝ => anchoredMomentContour q (x : ℂ)) (Ioi 0) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      integrableOn_anchoredMomentContour_horizontal hq (y := 0) (by norm_num) (by norm_num)
  have ht : IntegrableOn (fun x : ℝ => anchoredMomentContour q ((x : ℂ) + I)) (Ioi 0) := by
    simpa only [Complex.ofReal_one, one_mul] using
      integrableOn_anchoredMomentContour_horizontal hq (y := 1) (by norm_num) (by norm_num)
  have hl := (((intervalIntegral_tendsto_integral_Ioi 0 hb tendsto_id).sub
    (intervalIntegral_tendsto_integral_Ioi 0 ht tendsto_id)).add
    ((tendsto_anchoredMomentContour_vertical hq).const_mul I)).sub
    (tendsto_const_nhds (x := I * (∫ y in (0 : ℝ)..1, anchoredMomentContour q (y * I))))
  simp only [mul_zero, add_zero] at hl
  have hz : Tendsto (fun R : ℝ =>
      (∫ x in 0..R, anchoredMomentContour q (x : ℂ)) -
        (∫ x in 0..R, anchoredMomentContour q ((x : ℂ) + I)) +
        I * (∫ y in (0 : ℝ)..1, anchoredMomentContour q ((R : ℂ) + y * I)) -
        I * (∫ y in (0 : ℝ)..1, anchoredMomentContour q (y * I))) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    exact (anchoredMomentContour_rectangle q hR).symm
  have h := tendsto_nhds_unique hl hz
  linear_combination h

theorem momentCosh_add_I (y : ℝ) : momentCosh ((y : ℂ) + I) =
    I * (Real.sinh (Real.pi * y / 2) : ℂ) := by
  unfold momentCosh
  rw [show (Real.pi : ℂ) * ((y : ℂ) + I) / 2 =
    ((Real.pi * y / 2 : ℝ) : ℂ) + ((Real.pi : ℂ) / 2) * I by push_cast; ring,
    Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp only [mul_zero, one_mul, zero_add, ← Complex.ofReal_sinh]
  ring

theorem anchoredMomentContour_real {q : ℕ} (hq : 0 < q) (x : ℝ) :
    anchoredMomentContour q (x : ℂ) =
      ((x * (x ^ 2 + 1) ^ q / Real.cosh (Real.pi * x / 2) : ℝ) : ℂ) := by
  have hx : (x : ℂ) ≠ I := by
    intro h
    have hh := congrArg Complex.im h
    norm_num at hh
  rw [anchoredMomentContour_eq hq hx]
  unfold momentCosh
  push_cast
  rfl

theorem anchoredMomentContour_imaginary {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ≠ 1) :
    anchoredMomentContour q ((y : ℂ) * I) =
      I * ((y * (1 - y ^ 2) ^ q / Real.cos (Real.pi * y / 2) : ℝ) : ℂ) := by
  have hz : (y : ℂ) * I ≠ I := by
    intro h
    have hh := congrArg Complex.im h
    apply hy
    simpa using hh
  rw [anchoredMomentContour_eq hq hz]
  have hp : ((y : ℂ) * I) ^ (2 : ℕ) + 1 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, I_sq]
    ring
  have hd : momentCosh ((y : ℂ) * I) = (Real.cos (Real.pi * y / 2) : ℂ) := by
    unfold momentCosh
    rw [show (Real.pi : ℂ) * ((y : ℂ) * I) / 2 = ((Real.pi * y / 2 : ℝ) : ℂ) * I by
      push_cast
      ring, Complex.cosh_mul_I, ← Complex.ofReal_cos]
  rw [hp, hd]
  push_cast
  ring

theorem anchoredMomentContour_top_re {q : ℕ} (hq : 0 < q) {y : ℝ} (hy : y ≠ 0) :
    (anchoredMomentContour q ((y : ℂ) + I)).re =
      (((y : ℂ) + I) * ((y : ℂ) ^ 2 + 2 * (y : ℂ) * I) ^ q).im /
        Real.sinh (Real.pi * y / 2) := by
  have hz : (y : ℂ) + I ≠ I := by
    intro h
    have hh := congrArg Complex.re h
    apply hy
    simpa using hh
  rw [anchoredMomentContour_eq hq hz, momentCosh_add_I]
  have hp : ((y : ℂ) + I) ^ (2 : ℕ) + 1 = (y : ℂ) ^ 2 + 2 * (y : ℂ) * I := by
    ring_nf
    rw [I_sq]
    ring
  rw [hp, div_mul_eq_div_div, Complex.div_ofReal_re, Complex.div_I, Complex.neg_re,
    Complex.mul_I_re, neg_neg]

theorem continuousOn_anchoredMomentContour_vertical (q : ℕ) (R : ℝ) :
    ContinuousOn (fun y : ℝ => anchoredMomentContour q ((R : ℂ) + y * I)) (Icc 0 1) := by
  intro y hy
  have h := (differentiableAt_anchoredMomentContour q
    (z := (R : ℂ) + y * I) (by simpa using hy.1) (by simpa using hy.2)).continuousAt
  exact (ContinuousAt.comp (f := fun y : ℝ => (R : ℂ) + y * I)
    (g := anchoredMomentContour q) (x := y) h (by fun_prop)).continuousWithinAt

theorem anchoredMomentContour_vertical_im {q : ℕ} (hq : 0 < q) :
    (∫ y in (0 : ℝ)..1, anchoredMomentContour q (y * I)).im =
      ∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ q / Real.cos (Real.pi * y / 2) := by
  have hc : ContinuousOn (fun y : ℝ => anchoredMomentContour q (y * I)) (Icc 0 1) := by
    simpa only [Complex.ofReal_zero, zero_add] using continuousOn_anchoredMomentContour_vertical q 0
  have hi : IntegrableOn (fun y : ℝ => anchoredMomentContour q (y * I)) (Ioc 0 1) volume :=
    (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have him : (∫ y : ℝ in Ioc 0 1, anchoredMomentContour q (y * I)).im =
      ∫ y : ℝ in Ioc 0 1, (anchoredMomentContour q (y * I)).im := by
    simpa using! (integral_im hi).symm
  rw [him]
  apply integral_congr_ae
  have hne : ∀ᵐ y : ℝ, y ≠ 1 := by simp [ae_iff]
  filter_upwards [ae_restrict_of_ae hne] with y hy
  rw [anchoredMomentContour_imaginary hq hy, Complex.I_mul_im, Complex.ofReal_re]

/-- Taking real parts of the genuine contour shift yields the real hyperbolic moment identity. -/
theorem anchoredMomentContour_real_identity {q : ℕ} (hq : 0 < q) :
    (∫ x : ℝ in Ioi 0, x * (x ^ 2 + 1) ^ q / Real.cosh (Real.pi * x / 2)) +
      (∫ y in (0 : ℝ)..1, y * (1 - y ^ 2) ^ q / Real.cos (Real.pi * y / 2)) =
      ∫ y : ℝ in Ioi 0,
        (((y : ℂ) + I) * ((y : ℂ) ^ 2 + 2 * (y : ℂ) * I) ^ q).im /
          Real.sinh (Real.pi * y / 2) := by
  have hb : (∫ x : ℝ in Ioi 0, anchoredMomentContour q (x : ℂ)).re =
      ∫ x : ℝ in Ioi 0, x * (x ^ 2 + 1) ^ q / Real.cosh (Real.pi * x / 2) := by
    simp_rw [anchoredMomentContour_real hq]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have ht : IntegrableOn (fun x : ℝ => anchoredMomentContour q ((x : ℂ) + I)) (Ioi 0) := by
    simpa only [Complex.ofReal_one, one_mul] using
      integrableOn_anchoredMomentContour_horizontal hq (y := 1) (by norm_num) (by norm_num)
  have he : (∫ x : ℝ in Ioi 0, anchoredMomentContour q ((x : ℂ) + I)).re =
      ∫ y : ℝ in Ioi 0,
        (((y : ℂ) + I) * ((y : ℂ) ^ 2 + 2 * (y : ℂ) * I) ^ q).im /
          Real.sinh (Real.pi * y / 2) := by
    have hre : (∫ x : ℝ in Ioi 0, anchoredMomentContour q ((x : ℂ) + I)).re =
        ∫ x : ℝ in Ioi 0, (anchoredMomentContour q ((x : ℂ) + I)).re := by
      simpa using! (integral_re ht).symm
    rw [hre]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact anchoredMomentContour_top_re hq hy.ne'
  have h := congrArg Complex.re (anchoredMomentContour_shift hq)
  rw [Complex.sub_re, Complex.I_mul_re, sub_neg_eq_add, hb,
    anchoredMomentContour_vertical_im hq, he] at h
  exact h

theorem integrableOn_anchoredMomentCosh {q : ℕ} (hq : 0 < q) :
    IntegrableOn (fun x : ℝ => x * (x ^ 2 + 1) ^ q / Real.cosh (Real.pi * x / 2)) (Ioi 0) := by
  have hi : IntegrableOn (fun x : ℝ => anchoredMomentContour q (x : ℂ)) (Ioi 0) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      integrableOn_anchoredMomentContour_horizontal hq (y := 0) (by norm_num) (by norm_num)
  have hr : IntegrableOn (fun x : ℝ => (anchoredMomentContour q (x : ℂ)).re) (Ioi 0) := by
    simpa using! hi.re
  refine hr.congr (Eventually.of_forall (fun x => ?_))
  dsimp only
  rw [anchoredMomentContour_real hq, Complex.ofReal_re]

theorem intervalIntegrable_anchoredMomentCos {q : ℕ} (hq : 0 < q) :
    IntervalIntegrable (fun y : ℝ => y * (1 - y ^ 2) ^ q / Real.cos (Real.pi * y / 2))
      volume 0 1 := by
  have hc : ContinuousOn (fun y : ℝ => anchoredMomentContour q (y * I)) (Icc 0 1) := by
    simpa only [Complex.ofReal_zero, zero_add] using continuousOn_anchoredMomentContour_vertical q 0
  have hi : IntegrableOn (fun y : ℝ => anchoredMomentContour q (y * I)) (Ioc 0 1) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hr : IntegrableOn (fun y : ℝ => (anchoredMomentContour q (y * I)).im) (Ioc 0 1) := by
    simpa using! hi.im
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
  apply hr.congr
  have hne : ∀ᵐ y : ℝ, y ≠ 1 := by simp [ae_iff]
  filter_upwards [ae_restrict_of_ae hne] with y hy
  rw [anchoredMomentContour_imaginary hq hy, Complex.I_mul_im, Complex.ofReal_re]

end BrownianAffine
