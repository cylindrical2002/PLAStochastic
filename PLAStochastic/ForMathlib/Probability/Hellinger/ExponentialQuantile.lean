import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureObservables
import PLAStochastic.ForMathlib.Probability.Moments.ExponentialPolynomial
import PLAStochastic.ForMathlib.Probability.Moments.PaleyZygmund

/-!
# Positive lower quantiles from a mean and fixed exponential moment

Paley-Zygmund gives a fixed positive mass above one half for a nonnegative
mean-one law with a fixed exponential moment. A sufficiently small Hellinger
distance transfers a quarter of any reference event mass to the other law.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

theorem mean_one_exponential_lower_quantile (Q : Measure ℝ) [IsProbabilityMeasure Q]
    {theta B : ℝ} (htheta : 0 < theta) (hB : 0 < B)
    (hpos : ∀ᵐ z ∂Q, 0 ≤ z) (hmean : ∫ z, z ∂Q = 1)
    (hi : Integrable (fun z => Real.exp (theta * z)) Q)
    (hb : ∫ z, Real.exp (theta * z) ∂Q ≤ B) :
    theta ^ 2 / (8 * B) ≤ Q.real {z | (1 / 2 : ℝ) < z} := by
  have h2 := polynomial_moment_of_exponential (X := fun z : ℝ => z)
    measurable_id htheta hpos hi hb 2
  have h2b : ∫ z, z ^ 2 ∂Q ≤ 2 * B / theta ^ 2 := by
    simpa only [Nat.factorial, Nat.cast_ofNat] using h2.2.trans_eq (by ring)
  let W := fun z : ℝ => max z 0
  have hW : W =ᵐ[Q] (fun z : ℝ => z) := hpos.mono fun z hz => max_eq_left hz
  have hWm : Measurable W := by fun_prop
  have hW2 : MemLp W 2 Q := (memLp_two_iff_integrable_sq hWm.aestronglyMeasurable).mpr
    (h2.1.congr (hpos.mono fun z hz => by
      change z ^ 2 = (max z 0) ^ 2
      rw [max_eq_left hz]))
  have hWmean : ∫ z, W z ∂Q = 1 := (integral_congr_ae hW).trans hmean
  have hpz := PGM.paley_zygmund hWm (fun z => le_max_right z 0) hW2
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  rw [hWmean, integral_congr_ae (hW.mono fun z hz => congrArg (fun r : ℝ => r ^ 2) hz)] at hpz
  have he : {z : ℝ | (1 / 2 : ℝ) * 1 < W z} =ᵐ[Q] {z : ℝ | (1 / 2 : ℝ) < z} :=
    hW.mono fun z hz => by
      change ((1 / 2 : ℝ) * 1 < W z) = ((1 / 2 : ℝ) < z)
      rw [hz, mul_one]
  have heReal : Q.real {z : ℝ | (1 / 2 : ℝ) * 1 < W z} =
      Q.real {z : ℝ | (1 / 2 : ℝ) < z} := congrArg ENNReal.toReal (measure_congr he)
  rw [heReal] at hpz
  have hmass : 0 ≤ Q.real {z : ℝ | (1 / 2 : ℝ) < z} := measureReal_nonneg
  have hb' := mul_le_mul_of_nonneg_right h2b hmass
  rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 8) hB)]
  have ht2 : 0 < theta ^ 2 := sq_pos_of_pos htheta
  have hc : (2 * B / theta ^ 2) * Q.real {z : ℝ | (1 / 2 : ℝ) < z} * theta ^ 2 =
      2 * B * Q.real {z : ℝ | (1 / 2 : ℝ) < z} := by field_simp
  have hh := mul_le_mul_of_nonneg_right (hpz.trans hb') ht2.le
  rw [hc] at hh
  nlinarith

end

end ProbabilityTheory

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem measureHellinger_lower_event {alpha : Type*} [MeasurableSpace alpha]
    (P Q : Measure alpha) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {A : Set alpha} (hA : MeasurableSet A) {beta : ℝ} (hbeta : 0 ≤ beta)
    (hQ : beta ≤ Q.real A) (hH : measureHellinger P Q ≤ Real.sqrt beta / 2) :
    beta / 4 ≤ P.real A := by
  have hmetric := measureHellinger_sqrt_event P Q hA
  have hroot := Real.sqrt_le_sqrt hQ
  have hP := Real.sq_sqrt (measureReal_nonneg : 0 ≤ P.real A)
  have hbetaSq := Real.sq_sqrt hbeta
  have hnonneg := Real.sqrt_nonneg (P.real A)
  have hbetaRoot := Real.sqrt_nonneg beta
  have hhalf : Real.sqrt beta / 2 ≤ Real.sqrt (P.real A) := by
    have hdiff := (abs_le.mp hmetric).1
    linarith
  nlinarith

end

end PGM
