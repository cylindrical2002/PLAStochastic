import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Polynomial Gaussian image sums

Comparing the `n + 1` term with the integral over `[n,n+1]` avoids a
monotonicity assumption on the polynomial times the Gaussian. Scaling the
integral will supply the uniform powers of time needed by image derivatives.
-/

noncomputable section

open MeasureTheory Filter Set Finset

namespace Real

theorem integrable_shifted_pow_mul_exp_neg_mul_sq (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : ℝ => (x + 1) ^ k * exp (-a * x ^ 2)) := by
  have he (x : ℝ) : (x + 1) ^ k * exp (-a * x ^ 2) =
      ∑ j ∈ range (k + 1), (k.choose j : ℝ) * (x ^ j * exp (-a * x ^ 2)) := by
    rw [add_pow, sum_mul]
    apply sum_congr rfl
    intro j _
    simp only [one_pow, mul_one]
    ring
  simp_rw [he]
  apply integrable_finsetSum
  intro j _
  have hi := integrable_rpow_mul_exp_neg_mul_sq ha (s := (j : ℝ))
    (by linarith [Nat.cast_nonneg (α := ℝ) j])
  simpa only [rpow_natCast] using hi.const_mul (k.choose j : ℝ)

theorem sum_gaussian_succ_pow_le_integral (k N : ℕ) {a : ℝ} (ha : 0 < a) :
    (∑ n ∈ range N, ((n : ℝ) + 1) ^ k * exp (-a * ((n : ℝ) + 1) ^ 2)) ≤
      ∫ x in Ioi (0 : ℝ), (x + 1) ^ k * exp (-a * x ^ 2) := by
  let g : ℝ → ℝ := fun x => (x + 1) ^ k * exp (-a * x ^ 2)
  have hi : Integrable g := integrable_shifted_pow_mul_exp_neg_mul_sq k ha
  have hs : (∑ n ∈ range N, ((n : ℝ) + 1) ^ k * exp (-a * ((n : ℝ) + 1) ^ 2)) ≤
      ∫ x in (0 : ℝ)..(N : ℝ), g x := by
    have h := sum_Ico_le_integral_of_le (f := fun y : ℝ => (y + 1) ^ k * exp (-a * (y + 1) ^ 2))
      (g := g) (a := 0) (b := N) (Nat.zero_le N) ?_ hi.integrableOn
    · simpa only [Nat.Ico_zero_eq_range, Nat.cast_zero] using h
    · intro n _ x hx
      have hx0 : 0 ≤ x := (Nat.cast_nonneg (α := ℝ) n).trans hx.1
      have hpow : ((n : ℝ) + 1) ^ k ≤ (x + 1) ^ k := by
        apply pow_le_pow_left₀ (by positivity)
        linarith [hx.1]
      have hexp : exp (-a * ((n : ℝ) + 1) ^ 2) ≤ exp (-a * x ^ 2) := by
        apply exp_le_exp.mpr
        have hnx : x ≤ (n : ℝ) + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using hx.2.le
        have hsq : x ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hx0 hnx 2
        nlinarith
      exact mul_le_mul hpow hexp (exp_nonneg _) (pow_nonneg (by linarith) _)
  refine hs.trans ?_
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
  exact setIntegral_mono_set hi.integrableOn
    (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => by
      change 0 < x at hx
      exact mul_nonneg (pow_nonneg (by linarith) k) (exp_nonneg _))
    (Eventually.of_forall fun _ hx => hx.1)

theorem summable_gaussian_succ_pow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * exp (-a * ((n : ℝ) + 1) ^ 2)) :=
  summable_of_sum_range_le (fun _ => by positivity)
    (fun N => sum_gaussian_succ_pow_le_integral k N ha)

theorem tsum_gaussian_succ_pow_le_integral (k : ℕ) {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, ((n : ℝ) + 1) ^ k * exp (-a * ((n : ℝ) + 1) ^ 2)) ≤
      ∫ x in Ioi (0 : ℝ), (x + 1) ^ k * exp (-a * x ^ 2) :=
  tsum_le_of_sum_range_le (fun _ => by positivity)
    (fun N => sum_gaussian_succ_pow_le_integral k N ha)

/-- The coefficient depends only on the fixed power and Gaussian rate. -/
theorem tsum_gaussian_succ_pow_scaled_bound (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      (∑' n : ℕ, ((n : ℝ) + 1) ^ k * exp (-a * ((n : ℝ) + 1) ^ 2 / t)) ≤
        C * sqrt t ^ (k + 1) := by
  let C : ℝ := ∫ x in Ioi (0 : ℝ), (x + 1) ^ k * exp (-a * x ^ 2)
  have hC : 0 ≤ C := setIntegral_nonneg measurableSet_Ioi fun x hx => by
    change 0 < x at hx
    exact mul_nonneg (pow_nonneg (by linarith) k) (exp_nonneg _)
  refine ⟨C, hC, fun t ht => ?_⟩
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hs : 0 < sqrt t := sqrt_pos.mpr ht0
  have hs1 : 1 ≤ sqrt t := by simpa only [sqrt_one] using sqrt_le_sqrt ht
  let g : ℝ → ℝ := fun x => (x + 1) ^ k * exp (-(a / t) * x ^ 2)
  have hig : Integrable g := integrable_shifted_pow_mul_exp_neg_mul_sq k (div_pos ha ht0)
  have he (x : ℝ) : g (sqrt t * x) = (sqrt t * x + 1) ^ k * exp (-a * x ^ 2) := by
    dsimp [g]
    rw [mul_pow, sq_sqrt ht0.le]
    congr 2
    field_simp
  have hb : (∫ x in Ioi (0 : ℝ), g (sqrt t * x)) ≤ sqrt t ^ k * C := by
    rw [show sqrt t ^ k * C =
      ∫ x in Ioi (0 : ℝ), sqrt t ^ k * ((x + 1) ^ k * exp (-a * x ^ 2)) from
        (integral_const_mul _ _).symm]
    apply setIntegral_mono_on ((hig.comp_mul_left' hs.ne').integrableOn)
      ((integrable_shifted_pow_mul_exp_neg_mul_sq k ha).const_mul _).integrableOn measurableSet_Ioi
    intro x hx
    change 0 < x at hx
    rw [he, ← mul_assoc, ← mul_pow]
    apply mul_le_mul_of_nonneg_right _ (exp_nonneg _)
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) k
  have hscale : (∫ x in Ioi (0 : ℝ), g x) = sqrt t * ∫ x in Ioi (0 : ℝ), g (sqrt t * x) := by
    simpa only [smul_eq_mul, mul_zero] using (integral_comp_mul_left_Ioi' g 0 hs).symm
  calc
    _ = ∑' n : ℕ, ((n : ℝ) + 1) ^ k * exp (-(a / t) * ((n : ℝ) + 1) ^ 2) := by
      congr 1
      funext n
      congr 2
      ring
    _ ≤ ∫ x in Ioi (0 : ℝ), g x := tsum_gaussian_succ_pow_le_integral k (div_pos ha ht0)
    _ = sqrt t * ∫ x in Ioi (0 : ℝ), g (sqrt t * x) := hscale
    _ ≤ sqrt t * (sqrt t ^ k * C) := mul_le_mul_of_nonneg_left hb hs.le
    _ = C * sqrt t ^ (k + 1) := by ring

end Real
