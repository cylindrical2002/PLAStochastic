import PLAStochastic.ForMathlib.Probability.Distributions.GammaDerivative
import PLAStochastic.ForMathlib.Probability.Hellinger.Density
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Actual classical derivatives of integer Gamma mixtures

No regularity of the mixing weights is needed. Twice differentiable mixtures
start at shape four. The norm bounds here depend on the physical normalisation
scale and therefore do not assert a uniform bound along a reference orbit.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set Filter

def gammaMixtureDensity (p : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, p n * gammaNatDensity (n + k) x

theorem gammaMixtureDensity_succ_of_nonpos (p : ℕ → ℝ) (k : ℕ) {x : ℝ} (hx : x ≤ 0) :
    gammaMixtureDensity p (k + 1) x = 0 := by
  unfold gammaMixtureDensity
  simp_rw [← Nat.add_assoc, gammaNatDensity_succ_of_nonpos _ hx, mul_zero]
  exact tsum_zero

variable {p : ℕ → ℝ} (hp0 : ∀ n, 0 ≤ p n) (hp : Summable p)

include hp0 hp

theorem summable_gammaMixtureDensity (k : ℕ) (x : ℝ) :
    Summable (fun n => p n * gammaNatDensity (n + k) x) :=
  hp.of_norm_bounded fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 n) (gammaNatDensity_nonneg _ _))]
    exact (mul_le_mul_of_nonneg_left (gammaNatDensity_le_one _ _) (hp0 n)).trans_eq (mul_one _)

omit hp0 hp in
theorem measurable_gammaMixtureDensity (k : ℕ) : Measurable (gammaMixtureDensity p k) :=
  Measurable.tsum fun n => (measurable_gammaPDFReal _ _).const_mul (p n)

omit hp in
theorem gammaMixtureDensity_nonneg (k : ℕ) (x : ℝ) : 0 ≤ gammaMixtureDensity p k x :=
  tsum_nonneg fun n => mul_nonneg (hp0 n) (gammaNatDensity_nonneg _ _)

theorem lintegral_gammaMixtureDensity (k : ℕ) :
    (∫⁻ x, ENNReal.ofReal (gammaMixtureDensity p k x)) = ENNReal.ofReal (∑' n, p n) := by
  simp only [gammaMixtureDensity]
  simp_rw [ENNReal.ofReal_tsum_of_nonneg
    (fun n => mul_nonneg (hp0 n) (gammaNatDensity_nonneg _ _))
    (summable_gammaMixtureDensity hp0 hp k _), ENNReal.ofReal_mul (hp0 _)]
  unfold gammaNatDensity
  rw [lintegral_tsum (fun n =>
    (((measurable_gammaPDFReal ((n + k + 1 : ℕ) : ℝ) 1).ennreal_ofReal).const_mul
      (ENNReal.ofReal (p n))).aemeasurable)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change (∑' n, ENNReal.ofReal (p n) * (∫⁻ x, gammaPDF ((n + k + 1 : ℕ) : ℝ) 1 x)) = _
  have hnorm (n : ℕ) : (∫⁻ x, gammaPDF ((n + k + 1 : ℕ) : ℝ) 1 x) = 1 :=
    lintegral_gammaPDF_eq_one (by positivity) one_pos
  simp_rw [hnorm, mul_one]
  exact (ENNReal.ofReal_tsum_of_nonneg hp0 hp).symm

theorem integrable_gammaMixtureDensity (k : ℕ) : Integrable (gammaMixtureDensity p k) volume := by
  refine ⟨(measurable_gammaMixtureDensity k).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaMixtureDensity_nonneg hp0 k)),
    lintegral_gammaMixtureDensity hp0 hp k]
  exact ENNReal.ofReal_lt_top

theorem integral_gammaMixtureDensity (k : ℕ) :
    (∫ x, gammaMixtureDensity p k x) = ∑' n, p n := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (gammaMixtureDensity_nonneg hp0 k))
    (measurable_gammaMixtureDensity k).aestronglyMeasurable,
    lintegral_gammaMixtureDensity hp0 hp k, ENNReal.toReal_ofReal (tsum_nonneg hp0)]

theorem continuous_gammaMixtureDensity (k : ℕ) : Continuous (gammaMixtureDensity p (k + 1)) := by
  exact continuous_tsum (u := p) (fun n => by
    simpa only [Nat.add_assoc] using (continuous_gammaNatDensity (n + k)).const_mul (p n)
    ) hp (fun n x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hp0 n) (gammaNatDensity_nonneg _ _))]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (gammaNatDensity_le_one _ _) (hp0 n))

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_gammaMixtureDensity (k : ℕ) (x : ℝ) :
    HasDerivAt (gammaMixtureDensity p (k + 2))
      (gammaMixtureDensity p (k + 1) x - gammaMixtureDensity p (k + 2) x) x := by
  have hterm (n z) : HasDerivAt (fun t => p n * gammaNatDensity (n + (k + 2)) t)
      (p n * (gammaNatDensity (n + (k + 1)) z - gammaNatDensity (n + (k + 2)) z)) z := by
    simpa only [Nat.add_assoc] using (hasDerivAt_gammaNatDensity (n + k) z).const_mul (p n)
  have hbound (n z) :
      ‖p n * (gammaNatDensity (n + (k + 1)) z - gammaNatDensity (n + (k + 2)) z)‖ ≤ 2 * p n := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hp0 n)]
    have h := abs_sub (gammaNatDensity (n + (k + 1)) z) (gammaNatDensity (n + (k + 2)) z)
    simp only [abs_of_nonneg (gammaNatDensity_nonneg _ _)] at h
    have hb : |gammaNatDensity (n + (k + 1)) z - gammaNatDensity (n + (k + 2)) z| ≤ 2 :=
      h.trans (by linarith [gammaNatDensity_le_one (n + (k + 1)) z,
        gammaNatDensity_le_one (n + (k + 2)) z])
    nlinarith [mul_le_mul_of_nonneg_left hb (hp0 n)]
  have h := hasDerivAt_tsum (hp.mul_left 2) hterm hbound
    (summable_gammaMixtureDensity hp0 hp (k + 2) 0) x
  have he : (∑' n, p n * (gammaNatDensity (n + (k + 1)) x - gammaNatDensity (n + (k + 2)) x)) =
      gammaMixtureDensity p (k + 1) x - gammaMixtureDensity p (k + 2) x := by
    simp only [mul_sub, gammaMixtureDensity]
    exact (summable_gammaMixtureDensity hp0 hp (k + 1) x).tsum_sub
      (summable_gammaMixtureDensity hp0 hp (k + 2) x)
  rw [he] at h
  exact h

def gammaMixtureFirst (p : ℕ → ℝ) (x : ℝ) : ℝ :=
  gammaMixtureDensity p 2 x - gammaMixtureDensity p 3 x

def gammaMixtureSecond (p : ℕ → ℝ) (x : ℝ) : ℝ :=
  gammaMixtureDensity p 1 x - 2 * gammaMixtureDensity p 2 x + gammaMixtureDensity p 3 x

theorem hasDerivAt_gammaMixtureFirst (x : ℝ) :
    HasDerivAt (gammaMixtureFirst p) (gammaMixtureSecond p x) x := by
  convert (hasDerivAt_gammaMixtureDensity hp0 hp 0 x).sub
    (hasDerivAt_gammaMixtureDensity hp0 hp 1 x) using 1 <;>
    first | rfl | (dsimp [gammaMixtureSecond]; ring)

theorem continuous_gammaMixtureSecond : Continuous (gammaMixtureSecond p) :=
  ((continuous_gammaMixtureDensity hp0 hp 0).sub
    ((continuous_gammaMixtureDensity hp0 hp 1).const_mul 2)).add
      (continuous_gammaMixtureDensity hp0 hp 2)

theorem integrable_gammaMixtureFirst : Integrable (gammaMixtureFirst p) volume :=
  (integrable_gammaMixtureDensity hp0 hp 2).sub (integrable_gammaMixtureDensity hp0 hp 3)

theorem integrable_gammaMixtureSecond : Integrable (gammaMixtureSecond p) volume :=
  ((integrable_gammaMixtureDensity hp0 hp 1).sub
    ((integrable_gammaMixtureDensity hp0 hp 2).const_mul 2)).add
      (integrable_gammaMixtureDensity hp0 hp 3)

set_option backward.isDefEq.respectTransparency.types false in
theorem integral_abs_gammaMixtureFirst_le :
    (∫ x, |gammaMixtureFirst p x|) ≤ 2 * ∑' n, p n := by
  calc
    (∫ x, |gammaMixtureFirst p x|) ≤
        ∫ x, gammaMixtureDensity p 2 x + gammaMixtureDensity p 3 x := by
      apply integral_mono (integrable_gammaMixtureFirst hp0 hp).abs
        ((integrable_gammaMixtureDensity hp0 hp 2).add (integrable_gammaMixtureDensity hp0 hp 3))
      intro x
      change |gammaMixtureDensity p 2 x - gammaMixtureDensity p 3 x| ≤
        gammaMixtureDensity p 2 x + gammaMixtureDensity p 3 x
      exact (abs_sub (gammaMixtureDensity p 2 x) (gammaMixtureDensity p 3 x)).trans_eq (by
        rw [abs_of_nonneg (gammaMixtureDensity_nonneg hp0 _ _),
          abs_of_nonneg (gammaMixtureDensity_nonneg hp0 _ _)])
    _ = _ := by
      rw [integral_add (integrable_gammaMixtureDensity hp0 hp 2)
        (integrable_gammaMixtureDensity hp0 hp 3), integral_gammaMixtureDensity hp0 hp,
        integral_gammaMixtureDensity hp0 hp]
      ring

theorem integral_abs_gammaMixtureSecond_le :
    (∫ x, |gammaMixtureSecond p x|) ≤ 4 * ∑' n, p n := by
  have h1 := integrable_gammaMixtureDensity hp0 hp 1
  have h2 := integrable_gammaMixtureDensity hp0 hp 2
  have h3 := integrable_gammaMixtureDensity hp0 hp 3
  calc
    (∫ x, |gammaMixtureSecond p x|) ≤
        ∫ x, gammaMixtureDensity p 1 x + 2 * gammaMixtureDensity p 2 x + gammaMixtureDensity p 3 x := by
      apply integral_mono (integrable_gammaMixtureSecond hp0 hp).abs ((h1.add (h2.const_mul 2)).add h3)
      intro x
      have ha := abs_add_le (gammaMixtureDensity p 1 x - 2 * gammaMixtureDensity p 2 x)
        (gammaMixtureDensity p 3 x)
      have hb := abs_sub (gammaMixtureDensity p 1 x) (2 * gammaMixtureDensity p 2 x)
      simp only [abs_mul, abs_of_nonneg (gammaMixtureDensity_nonneg hp0 _ _),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha hb
      dsimp [gammaMixtureSecond]
      linarith
    _ = _ := by
      rw [integral_add (f := fun x => gammaMixtureDensity p 1 x + 2 * gammaMixtureDensity p 2 x)
        (g := gammaMixtureDensity p 3) (h1.add (h2.const_mul 2)) h3,
        integral_add (f := gammaMixtureDensity p 1) (g := fun x => 2 * gammaMixtureDensity p 2 x)
          h1 (h2.const_mul 2), integral_const_mul]
      simp only [integral_gammaMixtureDensity hp0 hp]
      ring

def gammaMixtureHellinger (hp1 : ∑' n, p n = 1) : HellingerDensity (volume : Measure ℝ) where
  density := gammaMixtureDensity p 3
  measurable := measurable_gammaMixtureDensity 3
  nonneg := gammaMixtureDensity_nonneg hp0 3
  integrable := integrable_gammaMixtureDensity hp0 hp 3
  integral_eq_one := (integral_gammaMixtureDensity hp0 hp 3).trans hp1

end

end ProbabilityTheory
