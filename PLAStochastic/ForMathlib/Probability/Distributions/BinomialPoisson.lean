import PLAStochastic.ForMathlib.Probability.Distributions.BinomialEntropy
import PLAStochastic.ForMathlib.Probability.Hellinger.Discrete
import PLAStochastic.ForMathlib.Probability.Hellinger.Entropy
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# The actual binomial--Poisson likelihood ratio

The common reference measure is counting measure. The finite entropy expression
is identified with the logarithm of the actual singleton probabilities, including
the sample-count factor in the Poisson rate.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Finset
open scoped NNReal

def binomialPoissonRate (n : ℕ) (p : unitInterval) : ℝ≥0 :=
  ⟨(n : ℝ) * p, mul_nonneg (Nat.cast_nonneg n) p.property.1⟩

def binomialCountDensity (n : ℕ) (p : unitInterval) :
    HellingerDensity (Measure.count : Measure ℕ) := HellingerDensity.ofNatProbability (binomial n p)

def poissonCountDensity (n : ℕ) (p : unitInterval) :
    HellingerDensity (Measure.count : Measure ℕ) :=
  HellingerDensity.ofNatProbability (poissonMeasure (binomialPoissonRate n p))

theorem binomialLogFalling_eq_log_descFactorial {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    binomialLogFalling n k = Real.log (n.descFactorial k : ℝ) - k * Real.log n := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hpos (j : ℕ) (hj : j ∈ range k) : 0 < 1 - (j : ℝ) / n := by
    have hjn : j < n := lt_of_lt_of_le (mem_range.mp hj) hk
    have hdiv : (j : ℝ) / n < 1 := (div_lt_one hnreal).2 (Nat.cast_lt.mpr hjn)
    linarith
  have hprod : (∏ j ∈ range k, (1 - (j : ℝ) / n)) = (n.descFactorial k : ℝ) / n ^ k := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have hd : (n : ℝ) ^ k = ∏ _j ∈ range k, (n : ℝ) := by simp
    rw [hd, ← prod_div_distrib]
    apply prod_congr rfl
    intro j hj
    rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le (mem_range.mp hj) hk))]
    field_simp
  rw [binomialLogFalling, ← Real.log_prod (fun j hj => (hpos j hj).ne'), hprod,
    Real.log_div (by exact (Nat.cast_ne_zero.mpr
      (Nat.descFactorial_pos.mpr hk).ne')) (pow_ne_zero k hnreal.ne'), Real.log_pow]

theorem log_binomial_div_poisson {n k : ℕ} (hn : 0 < n) (hk : k ≤ n)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    Real.log ((binomialCountDensity n p).density k / (poissonCountDensity n p).density k) =
      binomialLogFalling n k + ((n : ℝ) - k) * Real.log (1 - (p : ℝ)) + n * p := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hchoose : 0 < (n.choose k : ℝ) := Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hfact : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hup : 0 < 1 - (p : ℝ) := by linarith
  have hrate : 0 < (binomialPoissonRate n p : ℝ) := mul_pos hnreal hp0
  change Real.log ((binomial n p).real {k} /
    (poissonMeasure (binomialPoissonRate n p)).real {k}) = _
  rw [binomial_real_singleton, poissonMeasure_real_singleton,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (mul_pos hchoose (pow_pos hp0 k)).ne' (pow_pos hup (n - k)).ne',
    Real.log_mul hchoose.ne' (pow_pos hp0 k).ne',
    Real.log_div (mul_pos (Real.exp_pos _) (pow_pos hrate k)).ne' hfact.ne',
    Real.log_mul (Real.exp_pos _).ne' (pow_pos hrate k).ne', Real.log_exp,
    Real.log_pow, Real.log_pow, Real.log_pow,
    binomialLogFalling_eq_log_descFactorial hn hk,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    Real.log_mul hfact.ne' hchoose.ne']
  change Real.log (n.choose k : ℝ) + k * Real.log (p : ℝ) +
    (n - k : ℕ) * Real.log (1 - (p : ℝ)) -
    (-(n * (p : ℝ)) + k * Real.log ((n : ℝ) * p) - Real.log (k.factorial : ℝ)) = _
  rw [Real.log_mul hnreal.ne' hp0.ne', Nat.cast_sub hk]
  ring

def binomialPoissonEntropy (n : ℕ) (p : unitInterval) : ℝ :=
  ∫ k, (binomialCountDensity n p).density k * Real.log
    ((binomialCountDensity n p).density k / (poissonCountDensity n p).density k)
    ∂Measure.count

theorem binomialPoisson_entropy_integrable (n : ℕ) (p : unitInterval) :
    Integrable (fun k => (binomialCountDensity n p).density k * Real.log
      ((binomialCountDensity n p).density k / (poissonCountDensity n p).density k))
      Measure.count := by
  let b := binomialCountDensity n p
  let φ := fun k => Real.log (b.density k / (poissonCountDensity n p).density k)
  have hi : Integrable φ b.toMeasure := by
    rw [show b.toMeasure = binomial n p from HellingerDensity.ofNatProbability_toMeasure _]
    exact integrable_binomial φ
  rw [HellingerDensity.toMeasure] at hi
  have hf := (integrable_withDensity_iff b.measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).1 hi
  simpa only [ENNReal.toReal_ofReal (b.nonneg _), mul_comm] using hf

theorem binomialPoissonEntropy_eq_remainder {n : ℕ} (hn : 0 < n)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    binomialPoissonEntropy n p = binomialEntropyRemainder n p := by
  rw [binomialPoissonEntropy, ← HellingerDensity.integral_toMeasure,
    show (binomialCountDensity n p).toMeasure = binomial n p from
      HellingerDensity.ofNatProbability_toMeasure _]
  have he : (∫ k, Real.log ((binomialCountDensity n p).density k /
      (poissonCountDensity n p).density k) ∂binomial n p) =
      ∫ k, binomialLogFalling n k + ((n : ℝ) - k) * Real.log (1 - (p : ℝ)) + n * p
        ∂binomial n p := by
    apply integral_congr_ae
    filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))] with k hk
    exact log_binomial_div_poisson hn hk p hp0 hp1
  rw [he, integral_add (integrable_binomial _) (integrable_const _),
    integral_add (integrable_binomial _) (integrable_binomial _),
    integral_binomial_eq_average, integral_mul_const]
  have hsub := integral_sub (integrable_const (μ := binomial n p) (n : ℝ))
    (integrable_binomial (p := p) (fun k : ℕ => (k : ℝ)))
  rw [hsub, integral_binomial_natCast]
  simp only [integral_const, probReal_univ, one_smul]
  rw [binomialEntropyRemainder]
  ring

/-- Uniform squared Hellinger bound for the actual count distributions. -/
theorem hellinger_sq_binomial_poisson_le {n : ℕ} (hn : 0 < n)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    (binomialCountDensity n p).hellinger (poissonCountDensity n p) ^ 2 ≤
      -(p : ℝ) - Real.log (1 - (p : ℝ)) := by
  have hpos (k : ℕ) : 0 < (poissonCountDensity n p).density k :=
    poissonMeasure_real_singleton_pos k
      (show 0 < binomialPoissonRate n p from mul_pos (Nat.cast_pos.mpr hn) hp0)
  have hH := HellingerDensity.hellinger_sq_le_entropy
    (binomialCountDensity n p) (poissonCountDensity n p) hpos
    (binomialPoisson_entropy_integrable n p)
  change (binomialCountDensity n p).hellinger (poissonCountDensity n p) ^ 2 ≤
    binomialPoissonEntropy n p at hH
  rw [binomialPoissonEntropy_eq_remainder hn p hp0 hp1] at hH
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact hH.trans (binomialEntropyRemainder_le m p.property.1 hp1)

/-- Count Hellinger error is linear in window mass, uniformly in the sample size. -/
theorem hellinger_binomial_poisson_le {n : ℕ} (hn : 0 < n)
    (p : unitInterval) (hp0 : 0 < (p : ℝ)) (hp : (p : ℝ) ≤ 1 / 2) :
    (binomialCountDensity n p).hellinger (poissonCountDensity n p) ≤ (p : ℝ) := by
  have hp1 : (p : ℝ) < 1 := by linarith
  have hH := hellinger_sq_binomial_poisson_le hn p hp0 hp1
  have hlog := binomial_entropy_log_bound p.property.1 hp1
  have hd : (p : ℝ) ^ 2 / (2 * (1 - (p : ℝ))) ≤ (p : ℝ) ^ 2 :=
    div_le_self (sq_nonneg _) (by linarith)
  have hsq := hH.trans (hlog.trans hd)
  nlinarith [(binomialCountDensity n p).hellinger_nonneg (poissonCountDensity n p)]

theorem hellinger_binomial_poisson_zero_count (p : unitInterval) :
    (binomialCountDensity 0 p).hellinger (poissonCountDensity 0 p) = 0 := by
  apply (HellingerDensity.hellinger_eq_zero_iff _ _).mpr
  exact ae_of_all _ fun k => by
    change (binomial 0 p).real {k} = (poissonMeasure (binomialPoissonRate 0 p)).real {k}
    rw [binomial_real_singleton, poissonMeasure_real_singleton]
    have hrate : (binomialPoissonRate 0 p : ℝ) = 0 := by
      change ((0 : ℕ) : ℝ) * (p : ℝ) = 0
      simp
    rw [hrate]
    by_cases hk : k = 0
    · subst k
      simp
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      simp [Nat.choose_eq_zero_of_lt hkpos, zero_pow hk]

theorem hellinger_binomial_poisson_zero_mass (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) = 0) :
    (binomialCountDensity n p).hellinger (poissonCountDensity n p) = 0 := by
  apply (HellingerDensity.hellinger_eq_zero_iff _ _).mpr
  exact ae_of_all _ fun k => by
    change (binomial n p).real {k} = (poissonMeasure (binomialPoissonRate n p)).real {k}
    rw [binomial_real_singleton, poissonMeasure_real_singleton]
    have hrate : (binomialPoissonRate n p : ℝ) = 0 := by
      change (n : ℝ) * (p : ℝ) = 0
      rw [hp, mul_zero]
    rw [hrate]
    by_cases hk : k = 0
    · subst k
      simp [hp]
    · simp [hp, zero_pow hk]

/-- Uniform count bound including both zero-sample and zero-window cases. -/
theorem hellinger_binomial_poisson_le_all (n : ℕ) (p : unitInterval)
    (hp : (p : ℝ) ≤ 1 / 2) :
    (binomialCountDensity n p).hellinger (poissonCountDensity n p) ≤ (p : ℝ) := by
  by_cases hn : n = 0
  · subst n
    rw [hellinger_binomial_poisson_zero_count]
    exact p.property.1
  by_cases hpzero : (p : ℝ) = 0
  · rw [hellinger_binomial_poisson_zero_mass n p hpzero, hpzero]
  · exact hellinger_binomial_poisson_le (Nat.pos_of_ne_zero hn) p
      (lt_of_le_of_ne p.property.1 (Ne.symm hpzero)) hp

end

end ProbabilityTheory
