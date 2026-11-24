import PLAStochastic.ForMathlib.Probability.Hellinger.DerivativeInterpolation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Interpolation at a fixed exponential weight

Exponential tilting converts the weighted density into a probability density.
The first derivative created by the tilt is absorbed at a fixed short secant
scale. The resulting constant depends only on the exponent and the tilted mass,
not on the input second-derivative norm.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

theorem weighted_integral_abs_derivative_le_sqrt
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' : ℝ → ℝ} {theta Z : ℝ}
    (htheta : 0 ≤ theta) (hZ : 0 < Z)
    (hmass : (∫ x, Real.exp (theta * x) * p.density x) = Z)
    (hp : Continuous p.density) (hp' : Continuous p') (hp'' : Continuous p'')
    (hd : ∀ x, HasDerivAt p.density (p' x) x)
    (hdd : ∀ x, HasDerivAt p' (p'' x) x)
    (hi : Integrable (fun x => Real.exp (theta * x) * p.density x) volume)
    (hi' : Integrable (fun x => Real.exp (theta * x) * p' x) volume)
    (hi'' : Integrable (fun x => Real.exp (theta * x) * p'' x) volume) :
    (∫ x, Real.exp (theta * x) * |p' x|) ≤
      (2 * (1 + 4 * theta) * ((2 + theta + theta ^ 2) * Z + 1)) *
        Real.sqrt (1 + ∫ x, Real.exp (theta * x) * |p'' x|) := by
  let q : HellingerDensity (volume : Measure ℝ) := {
    density := fun x => Real.exp (theta * x) * p.density x / Z
    measurable := ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      p.measurable).div_const Z
    nonneg := fun x => div_nonneg (mul_nonneg (Real.exp_pos _).le (p.nonneg x)) hZ.le
    integrable := hi.div_const Z
    integral_eq_one := by rw [integral_div, hmass, div_self hZ.ne'] }
  let q' := fun x => Real.exp (theta * x) * (theta * p.density x + p' x) / Z
  let q'' := fun x => Real.exp (theta * x) *
    (theta ^ 2 * p.density x + 2 * theta * p' x + p'' x) / Z
  have he (x : ℝ) : HasDerivAt (fun t => Real.exp (theta * t))
      (Real.exp (theta * x) * theta) x := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      (Real.hasDerivAt_exp _).comp x ((hasDerivAt_id x).const_mul theta)
  have hdq (x : ℝ) : HasDerivAt q.density (q' x) x := by
    convert ((he x).mul (hd x)).div_const Z using 1 <;> first
    | rfl
    | (dsimp [q']; ring)
  have hddq (x : ℝ) : HasDerivAt q' (q'' x) x := by
    convert ((he x).mul (((hd x).const_mul theta).add (hdd x))).div_const Z using 1 <;> first
    | rfl
    | (dsimp [q'']; ring)
  have hq' : Continuous q' := by dsimp [q']; fun_prop
  have hq'' : Continuous q'' := by dsimp [q'']; fun_prop
  have hiq' : Integrable q' volume := by
    have heq : q' = fun x => (theta * (Real.exp (theta * x) * p.density x) +
        Real.exp (theta * x) * p' x) / Z := by funext x; dsimp [q']; ring
    rw [heq]
    exact ((hi.const_mul theta).add hi').div_const Z
  have hiq'' : Integrable q'' volume := by
    have heq : q'' = fun x => (theta ^ 2 * (Real.exp (theta * x) * p.density x) +
        (2 * theta) * (Real.exp (theta * x) * p' x) + Real.exp (theta * x) * p'' x) / Z := by
      funext x; dsimp [q'']; ring
    rw [heq]
    exact (((hi.const_mul (theta ^ 2)).add (hi'.const_mul (2 * theta))).add hi'').div_const Z
  have hiA : Integrable (fun x => Real.exp (theta * x) * |p' x|) volume := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hi'.abs
  have hiB : Integrable (fun x => Real.exp (theta * x) * |p'' x|) volume := by
    simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hi''.abs
  let A := ∫ x, Real.exp (theta * x) * |p' x|
  let B := ∫ x, Real.exp (theta * x) * |p'' x|
  have hA : 0 ≤ A := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ B := integral_nonneg fun _ => by positivity
  have hfirst : A ≤ Z * (∫ x, |q' x|) + theta * Z := by
    calc
      _ ≤ ∫ x, Z * |q' x| + theta * (Real.exp (theta * x) * p.density x) := by
        apply integral_mono hiA ((hiq'.abs.const_mul Z).add (hi.const_mul theta))
        intro x
        change Real.exp (theta * x) * |p' x| ≤ _
        dsimp [q']
        rw [abs_div, abs_of_pos hZ, mul_div_cancel₀ _ hZ.ne',
          abs_mul, abs_of_pos (Real.exp_pos _)]
        have h := abs_sub (theta * p.density x + p' x) (theta * p.density x)
        rw [add_sub_cancel_left, abs_of_nonneg (mul_nonneg htheta (p.nonneg x))] at h
        nlinarith only [mul_le_mul_of_nonneg_left h (Real.exp_pos (theta * x)).le]
      _ = _ := by rw [integral_add (hiq'.abs.const_mul Z) (hi.const_mul theta),
        integral_const_mul, integral_const_mul, hmass]
  have hsecond : Z * (∫ x, |q'' x|) ≤ theta ^ 2 * Z + 2 * theta * A + B := by
    calc
      _ = ∫ x, Z * |q'' x| := (integral_const_mul _ _).symm
      _ ≤ ∫ x, theta ^ 2 * (Real.exp (theta * x) * p.density x) +
          (2 * theta) * (Real.exp (theta * x) * |p' x|) + Real.exp (theta * x) * |p'' x| := by
        apply integral_mono (hiq''.abs.const_mul Z)
          (((hi.const_mul (theta ^ 2)).add (hiA.const_mul (2 * theta))).add hiB)
        intro x
        dsimp [q'']
        rw [abs_div, abs_of_pos hZ, mul_div_cancel₀ _ hZ.ne',
          abs_mul, abs_of_pos (Real.exp_pos _)]
        have ht := mul_nonneg (sq_nonneg theta) (p.nonneg x)
        have h := (abs_add_le (theta ^ 2 * p.density x + 2 * theta * p' x) (p'' x)).trans
          (add_le_add (abs_add_le (theta ^ 2 * p.density x) (2 * theta * p' x)) le_rfl)
        rw [abs_of_nonneg ht, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * theta)] at h
        nlinarith only [mul_le_mul_of_nonneg_left h (Real.exp_pos (theta * x)).le]
      _ = _ := by
        rw [integral_add
          (f := fun x => theta ^ 2 * (Real.exp (theta * x) * p.density x) +
            (2 * theta) * (Real.exp (theta * x) * |p' x|))
          (g := fun x => Real.exp (theta * x) * |p'' x|)
          ((hi.const_mul (theta ^ 2)).add (hiA.const_mul (2 * theta))) hiB,
          integral_add (hi.const_mul (theta ^ 2)) (hiA.const_mul (2 * theta)),
          integral_const_mul, integral_const_mul, hmass]
  let C := 1 + 4 * theta
  let S := Real.sqrt (1 + B)
  let h := 1 / (C * S)
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hCpos : 0 < C := by linarith
  have hS : 1 ≤ S := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hSpos : 0 < S := by linarith
  have hSq : S ^ 2 = 1 + B := Real.sq_sqrt (by linarith)
  have hh : 0 < h := by dsimp [h]; positivity
  have hh1 : h ≤ 1 := by
    dsimp [h]
    apply (div_le_iff₀ (mul_pos hCpos hSpos)).mpr
    nlinarith only [hC, hS]
  have hhC : h * C ≤ 1 := by
    have heq : h * C = 1 / S := by dsimp [h]; field_simp
    rw [heq]
    exact (div_le_iff₀ hSpos).mpr (by simpa using hS)
  have htheta_h : 2 * theta * h ≤ 1 / 2 := by dsimp [C] at hhC; nlinarith only [hhC, hh.le]
  have hBh : h ^ 2 * B ≤ 1 := by
    have hCS : S ≤ C * S := by nlinarith only [hC, hSpos]
    have hCSsq : S ^ 2 ≤ (C * S) ^ 2 := pow_le_pow_left₀ (by linarith) hCS 2
    have hhq : h ^ 2 * (C * S) ^ 2 = 1 := by dsimp [h]; field_simp
    nlinarith only [hSq, hCSsq, hhq, sq_nonneg h]
  have hsec := q.mul_integral_abs_derivative_le_secant hdq hddq hq'.measurable hq''.measurable
    hiq' hiq'' hh.le
  have h1 := mul_le_mul_of_nonneg_left hfirst hh.le
  have h2 := mul_le_mul_of_nonneg_left hsec hZ.le
  have h3 := mul_le_mul_of_nonneg_left hsecond (sq_nonneg h)
  have h4 := mul_le_mul_of_nonneg_right htheta_h (mul_nonneg hh.le hA)
  have h5 := mul_le_mul_of_nonneg_right hh1 (mul_nonneg htheta hZ.le)
  have hhSq : h ^ 2 ≤ 1 := by nlinarith only [hh.le, hh1]
  have h6 := mul_le_mul_of_nonneg_right hhSq (mul_nonneg (sq_nonneg theta) hZ.le)
  have hfinal : h * A ≤ 2 * ((2 + theta + theta ^ 2) * Z + 1) := by
    nlinarith only [h1, h2, h3, h4, h5, h6, hBh]
  have hcancel : h * (C * S) = 1 := by dsimp [h]; field_simp
  have hres := mul_le_mul_of_nonneg_right hfinal (mul_pos hCpos hSpos).le
  have heq : (h * A) * (C * S) = A := by
    calc
      _ = A * (h * (C * S)) := by ring
      _ = _ := by rw [hcancel]; ring
  rw [heq] at hres
  change A ≤ _
  convert hres using 1 <;> first | rfl | (dsimp [C, S]; ring)

end

end ProbabilityTheory.HellingerDensity
