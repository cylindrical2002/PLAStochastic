import PLAStochastic.ForMathlib.Probability.Hellinger.ScaleRegularity
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Actual logarithmic densities and Hellinger scale regularity

For a density supported on the positive half-line, the logarithmic density is
`exp y * p (exp y)`. Change of variables preserves Hellinger distance. Its first
two derivative norms are precisely the natural weighted physical norms.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set

theorem integral_exp_mul_comp_exp (g : ℝ → ℝ) :
    (∫ y, Real.exp y * g (Real.exp y)) = ∫ x in Ioi (0 : ℝ), g x := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn g
  simpa only [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _), smul_eq_mul,
    Measure.restrict_univ] using h.symm

theorem integrable_exp_mul_comp_exp_iff (g : ℝ → ℝ) :
    Integrable (fun y => Real.exp y * g (Real.exp y)) volume ↔
      IntegrableOn g (Ioi (0 : ℝ)) volume := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun y _ => (Real.hasDerivAt_exp y).hasDerivWithinAt) Real.exp_injective.injOn g
  simpa only [image_univ, Real.range_exp, abs_of_pos (Real.exp_pos _), smul_eq_mul,
    integrableOn_univ] using h.symm

def logCoordinates (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) : HellingerDensity (volume : Measure ℝ) where
  density y := Real.exp y * p.density (Real.exp y)
  measurable := Real.measurable_exp.mul (p.measurable.comp Real.measurable_exp)
  nonneg y := mul_nonneg (Real.exp_pos y).le (p.nonneg _)
  integrable := (integrable_exp_mul_comp_exp_iff p.density).2 p.integrable.integrableOn
  integral_eq_one := by
    rw [integral_exp_mul_comp_exp,
      setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))
        (fun x hx => hp x (not_lt.mp hx))]
    exact p.integral_eq_one

theorem hellinger_logCoordinates (p q : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) (hq : ∀ x, x ≤ 0 → q.density x = 0) :
    (p.logCoordinates hp).hellinger (q.logCoordinates hq) = p.hellinger q := by
  have he : (p.logCoordinates hp).hellinger (q.logCoordinates hq) ^ 2 =
      p.hellinger q ^ 2 := by
    rw [hellinger_sq, hellinger_sq]
    calc
      (∫ y, (Real.sqrt ((p.logCoordinates hp).density y) -
          Real.sqrt ((q.logCoordinates hq).density y)) ^ 2) =
          ∫ y, Real.exp y * (Real.sqrt (p.density (Real.exp y)) -
            Real.sqrt (q.density (Real.exp y))) ^ 2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          change (Real.sqrt (Real.exp y * p.density (Real.exp y)) -
            Real.sqrt (Real.exp y * q.density (Real.exp y))) ^ 2 = _
          rw [Real.sqrt_mul (Real.exp_pos y).le, Real.sqrt_mul (Real.exp_pos y).le,
            ← mul_sub, mul_pow, Real.sq_sqrt (Real.exp_pos y).le]
      _ = ∫ x in Ioi (0 : ℝ), (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 :=
        integral_exp_mul_comp_exp
          (fun x => (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2)
      _ = _ := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        rw [hp x (not_lt.mp hx), hq x (not_lt.mp hx), Real.sqrt_zero, sub_self, zero_pow]
        norm_num
  nlinarith [(p.logCoordinates hp).hellinger_nonneg (q.logCoordinates hq), p.hellinger_nonneg q]

def dilate (p : HellingerDensity (volume : Measure ℝ)) (a : ℝ) (ha : 0 < a) :
    HellingerDensity (volume : Measure ℝ) where
  density x := p.density (x / a) / a
  measurable := (p.measurable.comp (measurable_id.div_const a)).div_const a
  nonneg x := div_nonneg (p.nonneg _) ha.le
  integrable := (p.integrable.comp_div ha.ne').div_const a
  integral_eq_one := by
    rw [integral_div, Measure.integral_comp_div, abs_of_pos ha, smul_eq_mul,
      p.integral_eq_one, mul_one]
    exact div_self ha.ne'

theorem dilate_eq_zero_of_nonpos (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : x ≤ 0) :
    (p.dilate a ha).density x = 0 := by
  change p.density (x / a) / a = 0
  rw [hp _ (div_nonpos_of_nonpos_of_nonneg hx ha.le), zero_div]

theorem logCoordinates_dilate_exp (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) (s : ℝ) :
    (p.dilate (Real.exp s) (Real.exp_pos s)).logCoordinates
      (fun _ hx => p.dilate_eq_zero_of_nonpos hp (Real.exp_pos s) hx) =
        (p.logCoordinates hp).translate s := by
  apply HellingerDensity.ext
  intro y
  change Real.exp y * (p.density (Real.exp y / Real.exp s) / Real.exp s) =
    Real.exp (y - s) * p.density (Real.exp (y - s))
  rw [Real.exp_sub]
  ring

theorem hellinger_dilate_exp_eq_translate (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) (s : ℝ) :
    (p.dilate (Real.exp s) (Real.exp_pos s)).hellinger p =
      ((p.logCoordinates hp).translate s).hellinger (p.logCoordinates hp) := by
  rw [← logCoordinates_dilate_exp p hp s, hellinger_logCoordinates]

def logCoordinateFirst (p : ℝ → ℝ) (p' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp y * (p (Real.exp y) + Real.exp y * p' (Real.exp y))

def logCoordinateSecond (p p' p'' : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp y * (p (Real.exp y) + 3 * Real.exp y * p' (Real.exp y) +
    Real.exp y ^ 2 * p'' (Real.exp y))

set_option backward.isDefEq.respectTransparency.types false in
theorem logCoordinates_hasDerivAt (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) {p' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt p.density (p' x) x) (y : ℝ) :
    HasDerivAt (p.logCoordinates hp).density (logCoordinateFirst p.density p' y) y := by
  have h := (Real.hasDerivAt_exp y).mul ((hd (Real.exp y)).comp y (Real.hasDerivAt_exp y))
  convert h using 1 <;> first | rfl |
    (dsimp only [logCoordinateFirst, Function.comp_apply]; ring)

set_option backward.isDefEq.respectTransparency.types false in
theorem logCoordinateFirst_hasDerivAt {p p' p'' : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p (p' x) x) (hp' : ∀ x, HasDerivAt p' (p'' x) x) (y : ℝ) :
    HasDerivAt (logCoordinateFirst p p') (logCoordinateSecond p p' p'' y) y := by
  have h := (Real.hasDerivAt_exp y).mul
    (((hp (Real.exp y)).comp y (Real.hasDerivAt_exp y)).add
      ((Real.hasDerivAt_exp y).mul ((hp' (Real.exp y)).comp y (Real.hasDerivAt_exp y))))
  convert h using 1 <;> first | rfl |
    (dsimp only [logCoordinateSecond, Function.comp_apply, Pi.add_apply, Pi.mul_apply]; ring)

theorem integral_abs_logCoordinateFirst (p p' : ℝ → ℝ) :
    (∫ y, |logCoordinateFirst p p' y|) = ∫ x in Ioi (0 : ℝ), |p x + x * p' x| := by
  unfold logCoordinateFirst
  simp_rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact integral_exp_mul_comp_exp (fun x => |p x + x * p' x|)

theorem integral_abs_logCoordinateSecond (p p' p'' : ℝ → ℝ) :
    (∫ y, |logCoordinateSecond p p' p'' y|) =
      ∫ x in Ioi (0 : ℝ), |p x + 3 * x * p' x + x ^ 2 * p'' x| := by
  unfold logCoordinateSecond
  simp_rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact integral_exp_mul_comp_exp (fun x => |p x + 3 * x * p' x + x ^ 2 * p'' x|)

theorem hellinger_dilate_exp_le_two_thirds
    (p : HellingerDensity (volume : Measure ℝ))
    (hp : ∀ x, x ≤ 0 → p.density x = 0) {p' p'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt p.density (p' x) x)
    (hd' : ∀ x, HasDerivAt p' (p'' x) x)
    (hm' : Measurable p') (hm'' : Measurable p'')
    (hi' : IntegrableOn (fun x => p.density x + x * p' x) (Ioi (0 : ℝ)) volume)
    (hi'' : IntegrableOn (fun x => p.density x + 3 * x * p' x + x ^ 2 * p'' x)
      (Ioi (0 : ℝ)) volume) (s : ℝ) :
    (p.dilate (Real.exp s) (Real.exp_pos s)).hellinger p ≤
      (2 * Real.sqrt (2 * ∫ x in Ioi (0 : ℝ), |p.density x + 3 * x * p' x + x ^ 2 * p'' x|) +
        Real.sqrt (∫ x in Ioi (0 : ℝ), |p.density x + x * p' x|) / 2) * |s| ^ (2 / 3 : ℝ) := by
  rw [hellinger_dilate_exp_eq_translate p hp s]
  have hi1 : Integrable (logCoordinateFirst p.density p') volume :=
    (integrable_exp_mul_comp_exp_iff _).2 hi'
  have hi2 : Integrable (logCoordinateSecond p.density p' p'') volume :=
    (integrable_exp_mul_comp_exp_iff _).2 hi''
  have hm1 : Measurable (logCoordinateFirst p.density p') :=
    Real.measurable_exp.mul ((p.measurable.comp Real.measurable_exp).add
      (Real.measurable_exp.mul (hm'.comp Real.measurable_exp)))
  have hm2 : Measurable (logCoordinateSecond p.density p' p'') :=
    Real.measurable_exp.mul (((p.measurable.comp Real.measurable_exp).add
      ((measurable_const.mul Real.measurable_exp).mul (hm'.comp Real.measurable_exp))).add
      ((Real.measurable_exp.pow_const 2).mul (hm''.comp Real.measurable_exp)))
  have h := (p.logCoordinates hp).hellinger_translate_le_two_thirds
    (logCoordinates_hasDerivAt p hp hd) (logCoordinateFirst_hasDerivAt hd hd')
    hm1 hm2 hi1 hi2 s
  rw [integral_abs_logCoordinateFirst, integral_abs_logCoordinateSecond] at h
  exact h

end

end ProbabilityTheory.HellingerDensity
