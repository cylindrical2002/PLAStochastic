import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureDerivative
import PLAStochastic.ForMathlib.Probability.Hellinger.ScaleMeasure

/-!
# Normalising the actual twice differentiable Gamma mixture

If the raw density is normalised by a positive mean scale `m`, its first and
second derivative norms are bounded by `2 * m` and `4 * m ^ 2`. These are finite
layer bounds, not uniform reference-orbit estimates.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

def gammaScaledMixture (p : ℕ → ℝ) (m x : ℝ) : ℝ :=
  m * gammaMixtureDensity p 3 (m * x)

def gammaScaledFirst (p : ℕ → ℝ) (m x : ℝ) : ℝ :=
  m ^ 2 * gammaMixtureFirst p (m * x)

def gammaScaledSecond (p : ℕ → ℝ) (m x : ℝ) : ℝ :=
  m ^ 3 * gammaMixtureSecond p (m * x)

variable {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp : Summable p)

include hp0 hp

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_gammaScaledMixture (m x : ℝ) :
    HasDerivAt (gammaScaledMixture p m) (gammaScaledFirst p m x) x := by
  convert ((hasDerivAt_gammaMixtureDensity hp0 hp 1 (m * x)).comp x
    ((hasDerivAt_id x).const_mul m)).const_mul m using 1 <;>
    first | rfl | (dsimp [gammaScaledFirst, gammaMixtureFirst]; ring)

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_gammaScaledFirst (m x : ℝ) :
    HasDerivAt (gammaScaledFirst p m) (gammaScaledSecond p m x) x := by
  convert ((hasDerivAt_gammaMixtureFirst hp0 hp (m * x)).comp x
    ((hasDerivAt_id x).const_mul m)).const_mul (m ^ 2) using 1 <;>
    first | rfl | (dsimp [gammaScaledSecond]; ring)

theorem continuous_gammaScaledSecond (m : ℝ) : Continuous (gammaScaledSecond p m) :=
  ((continuous_gammaMixtureSecond hp0 hp).comp (continuous_const.mul continuous_id)).const_mul _

theorem integrable_gammaScaledFirst {m : ℝ} (hm : 0 < m) :
    Integrable (gammaScaledFirst p m) volume :=
  ((integrable_gammaMixtureFirst hp0 hp).comp_mul_left' hm.ne').const_mul _

theorem integrable_gammaScaledSecond {m : ℝ} (hm : 0 < m) :
    Integrable (gammaScaledSecond p m) volume :=
  ((integrable_gammaMixtureSecond hp0 hp).comp_mul_left' hm.ne').const_mul _

omit hp0 hp in
theorem integral_abs_gammaScaledFirst {m : ℝ} (hm : 0 < m) :
    (∫ x, |gammaScaledFirst p m x|) = m * (∫ x, |gammaMixtureFirst p x|) := by
  simp only [gammaScaledFirst, abs_mul, abs_pow, abs_of_pos hm]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => |gammaMixtureFirst p x|) m, smul_eq_mul,
    abs_inv, abs_of_pos hm]
  field_simp

omit hp0 hp in
theorem integral_abs_gammaScaledSecond {m : ℝ} (hm : 0 < m) :
    (∫ x, |gammaScaledSecond p m x|) = m ^ 2 * (∫ x, |gammaMixtureSecond p x|) := by
  simp only [gammaScaledSecond, abs_mul, abs_pow, abs_of_pos hm]
  rw [integral_const_mul, Measure.integral_comp_mul_left (fun x => |gammaMixtureSecond p x|) m, smul_eq_mul,
    abs_inv, abs_of_pos hm]
  field_simp

theorem integral_abs_gammaScaledFirst_le (hp1 : ∑' n, p n = 1) {m : ℝ} (hm : 0 < m) :
    (∫ x, |gammaScaledFirst p m x|) ≤ 2 * m := by
  rw [integral_abs_gammaScaledFirst hm]
  have h := integral_abs_gammaMixtureFirst_le hp0 hp
  rw [hp1, mul_one] at h
  nlinarith [mul_le_mul_of_nonneg_left h hm.le]

theorem integral_abs_gammaScaledSecond_le (hp1 : ∑' n, p n = 1) {m : ℝ} (hm : 0 < m) :
    (∫ x, |gammaScaledSecond p m x|) ≤ 4 * m ^ 2 := by
  rw [integral_abs_gammaScaledSecond hm]
  have h := integral_abs_gammaMixtureSecond_le hp0 hp
  rw [hp1, mul_one] at h
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg m)]

def gammaScaledHellinger (hp1 : ∑' n, p n = 1) {m : ℝ} (hm : 0 < m) :
    HellingerDensity (volume : Measure ℝ) :=
  (gammaMixtureHellinger hp0 hp hp1).dilate m⁻¹ (inv_pos.mpr hm)

theorem gammaScaledHellinger_density (hp1 : ∑' n, p n = 1) {m : ℝ} (hm : 0 < m) :
    (gammaScaledHellinger hp0 hp hp1 hm).density = gammaScaledMixture p m := by
  funext x
  change gammaMixtureDensity p 3 (x / m⁻¹) / m⁻¹ = m * gammaMixtureDensity p 3 (m * x)
  rw [div_inv_eq_mul, div_inv_eq_mul, mul_comm x m, mul_comm]

theorem gammaScaledHellinger_toMeasure (hp1 : ∑' n, p n = 1) {m : ℝ} (hm : 0 < m) :
    (gammaScaledHellinger hp0 hp hp1 hm).toMeasure =
      (gammaMixtureHellinger hp0 hp hp1).toMeasure.map (fun x => x / m) := by
  rw [gammaScaledHellinger,
    HellingerDensity.dilate_toMeasure (gammaMixtureHellinger hp0 hp hp1) (inv_pos.mpr hm)]
  congr 1
  funext x
  rw [div_eq_inv_mul]

end

end ProbabilityTheory
