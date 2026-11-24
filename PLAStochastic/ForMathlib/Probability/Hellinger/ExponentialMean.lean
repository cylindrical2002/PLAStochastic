import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureObservables
import PLAStochastic.ForMathlib.Probability.Moments.ExponentialPolynomial

/-!
# A mean budget from Hellinger distance and fixed exponential moments

The second moments on both sides are paid by their true exponential moments.
This supplies a uniform conditional mean for a perturbed nonnegative law.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

theorem measureHellinger_mean_le_of_exponential
    (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {theta B m : ℝ} (htheta : 0 < theta)
    (hPpos : ∀ᵐ x ∂P, 0 ≤ x) (hQpos : ∀ᵐ x ∂Q, 0 ≤ x)
    (hPi : Integrable (fun x => Real.exp (theta * x)) P)
    (hQi : Integrable (fun x => Real.exp (theta * x)) Q)
    (hPb : ∫ x, Real.exp (theta * x) ∂P ≤ B)
    (hQb : ∫ x, Real.exp (theta * x) ∂Q ≤ B)
    (hmean : ∫ x, x ∂Q ≤ m) :
    Integrable (fun x => x) P ∧ ∫ x, x ∂P ≤
      m + measureHellinger P Q * Real.sqrt (8 * B / theta ^ 2) := by
  have hP1 := polynomial_moment_of_exponential measurable_id htheta hPpos hPi hPb 1
  have hP2 := polynomial_moment_of_exponential measurable_id htheta hPpos hPi hPb 2
  have hQ2 := polynomial_moment_of_exponential measurable_id htheta hQpos hQi hQb 2
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hP2 hQ2
  have h := measureHellinger_observable P Q measurable_id hP2.1 hQ2.1
  simp only [id_eq] at hP1 hP2 hQ2 h
  have hb : Real.sqrt (2 * ((∫ x, x ^ 2 ∂P) + ∫ x, x ^ 2 ∂Q)) ≤
      Real.sqrt (8 * B / theta ^ 2) := by
    apply Real.sqrt_le_sqrt
    calc
      _ ≤ 2 * (2 / theta ^ 2 * B + 2 / theta ^ 2 * B) := by
        linarith [hP2.2, hQ2.2]
      _ = _ := by ring
  refine ⟨by simpa only [pow_one] using hP1.1, ?_⟩
  have hdiff := (abs_le.mp h).2
  have hmul := mul_le_mul_of_nonneg_left hb (measureHellinger_nonneg P Q)
  linarith

end

end ProbabilityTheory
