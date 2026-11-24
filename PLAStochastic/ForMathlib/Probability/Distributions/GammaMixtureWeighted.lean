import PLAStochastic.ForMathlib.Probability.Distributions.GammaMixtureDerivative
import PLAStochastic.ForMathlib.Probability.Distributions.GammaExponential

/-!
# A fixed exponential weight on the Gamma-mixture derivatives

The first and second weighted derivative norms are paid by respectively two
and four times the same exponential moment of the original shape-four mixture.
The exponent is preserved.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

variable {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp : Summable p)
variable {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam < 1)

include hp0 hp hlam

omit hlam0 in
theorem lintegral_exp_mul_gammaMixtureDensity (k : ℕ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x) * gammaMixtureDensity p k x)) =
      ∑' n : ℕ, ENNReal.ofReal (p n) * ENNReal.ofReal (1 / (1 - lam) ^ (n + k + 1)) := by
  have hs (x : ℝ) : Summable (fun n => Real.exp (lam * x) *
      (p n * gammaNatDensity (n + k) x)) :=
    (summable_gammaMixtureDensity hp0 hp k x).mul_left _
  have he (x : ℝ) : Real.exp (lam * x) * gammaMixtureDensity p k x =
      ∑' n : ℕ, p n * (Real.exp (lam * x) * gammaNatDensity (n + k) x) := by
    rw [gammaMixtureDensity, ← tsum_mul_left]
    apply tsum_congr
    intro n
    ring
  have hen (x : ℝ) : ENNReal.ofReal (Real.exp (lam * x) * gammaMixtureDensity p k x) =
      ∑' n : ℕ, ENNReal.ofReal (p n) *
        ENNReal.ofReal (Real.exp (lam * x) * gammaNatDensity (n + k) x) := by
    rw [he x, ENNReal.ofReal_tsum_of_nonneg
      (fun n => mul_nonneg (hp0 n) (mul_nonneg (Real.exp_pos _).le (gammaNatDensity_nonneg _ _)))
      (by simpa only [mul_left_comm] using hs x)]
    simp_rw [ENNReal.ofReal_mul (hp0 _)]
  simp_rw [hen]
  have hm (n : ℕ) : Measurable (fun x => ENNReal.ofReal (p n) *
      ENNReal.ofReal (Real.exp (lam * x) * gammaNatDensity (n + k) x)) :=
    (((measurable_const.mul measurable_id).exp.mul
      (measurable_gammaPDFReal _ _)).ennreal_ofReal).const_mul _
  rw [lintegral_tsum (fun n => (hm n).aemeasurable)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_exp_mul_gammaNatDensity _ hlam]

include hlam0

theorem lintegral_exp_mul_gammaMixtureDensity_le {k : ℕ} (hk : k ≤ 3) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (lam * x) * gammaMixtureDensity p k x)) ≤
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x) * gammaMixtureDensity p 3 x) := by
  rw [lintegral_exp_mul_gammaMixtureDensity hp0 hp hlam,
    lintegral_exp_mul_gammaMixtureDensity hp0 hp hlam]
  apply ENNReal.tsum_le_tsum
  intro n
  have hr : 0 < 1 - lam := by linarith
  have hb : 1 / (1 - lam) ^ (n + k + 1) ≤ 1 / (1 - lam) ^ (n + 3 + 1) := by
    apply one_div_le_one_div_of_le (pow_pos hr _) ?_
    exact pow_le_pow_of_le_one hr.le (by linarith) (by omega : n + k + 1 ≤ n + 3 + 1)
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hb)

theorem integrable_exp_mul_gammaMixtureDensity_of_third
    (h3 : Integrable (fun x => Real.exp (lam * x) * gammaMixtureDensity p 3 x) volume)
    {k : ℕ} (hk : k ≤ 3) :
    Integrable (fun x => Real.exp (lam * x) * gammaMixtureDensity p k x) volume := by
  refine ⟨((measurable_const.mul measurable_id).exp.mul
    (measurable_gammaMixtureDensity k)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x =>
    mul_nonneg (Real.exp_pos _).le (gammaMixtureDensity_nonneg hp0 k x))]
  have hfin := h3.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x =>
    mul_nonneg (Real.exp_pos _).le (gammaMixtureDensity_nonneg hp0 3 x))] at hfin
  exact lt_of_le_of_lt (lintegral_exp_mul_gammaMixtureDensity_le hp0 hp hlam0 hlam hk) hfin

theorem integral_exp_mul_gammaMixtureDensity_le
    (h3 : Integrable (fun x => Real.exp (lam * x) * gammaMixtureDensity p 3 x) volume)
    {k : ℕ} (hk : k ≤ 3) :
    (∫ x, Real.exp (lam * x) * gammaMixtureDensity p k x) ≤
      ∫ x, Real.exp (lam * x) * gammaMixtureDensity p 3 x := by
  have hm (i : ℕ) : Measurable (fun x : ℝ => Real.exp (lam * x) * gammaMixtureDensity p i x) :=
    ((measurable_const.mul measurable_id).exp.mul (measurable_gammaMixtureDensity i))
  have hnn (i : ℕ) (x : ℝ) : 0 ≤ Real.exp (lam * x) * gammaMixtureDensity p i x :=
    mul_nonneg (Real.exp_pos _).le (gammaMixtureDensity_nonneg hp0 i x)
  have hfin := h3.hasFiniteIntegral
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (hnn 3))] at hfin
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn k)) (hm k).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn 3)) (hm 3).aestronglyMeasurable]
  apply ENNReal.toReal_mono hfin.ne
  exact lintegral_exp_mul_gammaMixtureDensity_le hp0 hp hlam0 hlam hk

set_option backward.isDefEq.respectTransparency.types false in
theorem gammaMixture_weighted_derivatives
    (h3 : Integrable (fun x => Real.exp (lam * x) * gammaMixtureDensity p 3 x) volume) :
    Integrable (fun x => Real.exp (lam * x) * gammaMixtureFirst p x) volume ∧
      Integrable (fun x => Real.exp (lam * x) * gammaMixtureSecond p x) volume ∧
      (∫ x, Real.exp (lam * x) * |gammaMixtureFirst p x|) ≤
        2 * (∫ x, Real.exp (lam * x) * gammaMixtureDensity p 3 x) ∧
      (∫ x, Real.exp (lam * x) * |gammaMixtureSecond p x|) ≤
        4 * (∫ x, Real.exp (lam * x) * gammaMixtureDensity p 3 x) := by
  have h1 := integrable_exp_mul_gammaMixtureDensity_of_third hp0 hp hlam0 hlam h3 (k := 1) (by norm_num)
  have h2 := integrable_exp_mul_gammaMixtureDensity_of_third hp0 hp hlam0 hlam h3 (k := 2) (by norm_num)
  have hfirst : Integrable (fun x => Real.exp (lam * x) * gammaMixtureFirst p x) volume := by
    convert h2.sub h3 using 1
    funext x
    dsimp [gammaMixtureFirst]
    ring
  have hsecond : Integrable (fun x => Real.exp (lam * x) * gammaMixtureSecond p x) volume := by
    convert (h1.sub (h2.const_mul 2)).add h3 using 1 <;>
      first | rfl | (funext x; dsimp [gammaMixtureSecond]; ring)
  have hM1 := integral_exp_mul_gammaMixtureDensity_le hp0 hp hlam0 hlam h3 (k := 1) (by norm_num)
  have hM2 := integral_exp_mul_gammaMixtureDensity_le hp0 hp hlam0 hlam h3 (k := 2) (by norm_num)
  refine ⟨hfirst, hsecond, ?_, ?_⟩
  · calc
      (∫ x, Real.exp (lam * x) * |gammaMixtureFirst p x|) ≤
          ∫ x, Real.exp (lam * x) * (gammaMixtureDensity p 2 x + gammaMixtureDensity p 3 x) := by
        apply integral_mono (by simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hfirst.abs)
          (by convert h2.add h3 using 1 <;>
            first | rfl | (funext x; dsimp only [Pi.add_apply]; ring))
        intro x
        apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        simpa only [gammaMixtureFirst, abs_of_nonneg (gammaMixtureDensity_nonneg hp0 _ _)] using
          abs_sub (gammaMixtureDensity p 2 x) (gammaMixtureDensity p 3 x)
      _ ≤ _ := by
        simp_rw [mul_add]
        rw [integral_add h2 h3]
        linarith
  · calc
      (∫ x, Real.exp (lam * x) * |gammaMixtureSecond p x|) ≤
          ∫ x, Real.exp (lam * x) * (gammaMixtureDensity p 1 x + 2 * gammaMixtureDensity p 2 x +
            gammaMixtureDensity p 3 x) := by
        apply integral_mono (by simpa only [abs_mul, abs_of_pos (Real.exp_pos _)] using hsecond.abs)
          (by
            convert (h1.add (h2.const_mul 2)).add h3 using 1 <;>
              first | rfl | (funext x; dsimp only [Pi.add_apply]; ring))
        intro x
        apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
        have ha := abs_add_le (gammaMixtureDensity p 1 x - 2 * gammaMixtureDensity p 2 x)
          (gammaMixtureDensity p 3 x)
        have hb := abs_sub (gammaMixtureDensity p 1 x) (2 * gammaMixtureDensity p 2 x)
        simp only [abs_mul, abs_of_nonneg (gammaMixtureDensity_nonneg hp0 _ _),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha hb
        dsimp [gammaMixtureSecond]
        linarith
      _ ≤ _ := by
        have he (x : ℝ) : Real.exp (lam * x) * (gammaMixtureDensity p 1 x + 2 * gammaMixtureDensity p 2 x +
            gammaMixtureDensity p 3 x) = Real.exp (lam * x) * gammaMixtureDensity p 1 x +
              2 * (Real.exp (lam * x) * gammaMixtureDensity p 2 x) +
                Real.exp (lam * x) * gammaMixtureDensity p 3 x := by ring
        simp_rw [he]
        rw [integral_add (f := fun x => Real.exp (lam * x) * gammaMixtureDensity p 1 x +
          2 * (Real.exp (lam * x) * gammaMixtureDensity p 2 x)) (g := fun x => Real.exp (lam * x) * gammaMixtureDensity p 3 x)
          (h1.add (h2.const_mul 2)) h3,
          integral_add (f := fun x => Real.exp (lam * x) * gammaMixtureDensity p 1 x)
            (g := fun x => 2 * (Real.exp (lam * x) * gammaMixtureDensity p 2 x)) h1 (h2.const_mul 2),
          integral_const_mul]
        linarith

end

end ProbabilityTheory
