import PLAStochastic.ForMathlib.Probability.Distributions.BinomialDerivative
import PLAStochastic.ForMathlib.Probability.Moments.Logarithm
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The finite binomial entropy remainder

The function below is the finite-support expression used when comparing
`Bin(n,p)` to `Pois(np)`. Its derivative is a binomial logarithmic expectation.
Connecting this expression to the actual likelihood ratio is a separate step.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Finset

def binomialLogFalling (n k : ℕ) : ℝ :=
  ∑ j ∈ range k, Real.log (1 - (j : ℝ) / n)

theorem binomialLogFalling_succ (n k : ℕ) :
    binomialLogFalling n (k + 1) - binomialLogFalling n k =
      Real.log (1 - (k : ℝ) / n) := by
  simp only [binomialLogFalling, sum_range_succ, add_sub_cancel_left]

def binomialEntropyRemainder (n : ℕ) (p : ℝ) : ℝ :=
  binomialAverage n (binomialLogFalling n) p +
    (n : ℝ) * (1 - p) * Real.log (1 - p) + n * p

theorem binomialEntropyRemainder_zero (n : ℕ) : binomialEntropyRemainder n 0 = 0 := by
  simp [binomialEntropyRemainder, binomialAverage_zero, binomialLogFalling]

theorem hasDerivAt_binomialEntropyRemainder_succ (n : ℕ) {p : ℝ} (hp : p < 1) :
    HasDerivAt (binomialEntropyRemainder (n + 1))
      ((n + 1 : ℝ) * (binomialAverage n
        (fun k => Real.log (1 - (k : ℝ) / (n + 1 : ℝ))) p - Real.log (1 - p))) p := by
  have hne : 1 - p ≠ 0 := by linarith
  have hd := hasDerivAt_binomialAverage_succ n (binomialLogFalling (n + 1)) p
  simp only [binomialLogFalling_succ] at hd
  have hu := (hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id p)
  have hl := hu.log hne
  have hc := (hasDerivAt_const p (n + 1 : ℝ)).mul hu
  have hprod := hc.mul hl
  have hlin := (hasDerivAt_id p).const_mul (n + 1 : ℝ)
  have hfull := (hd.add hprod).add hlin
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq,
    zero_sub, zero_mul, zero_add, Nat.cast_add, Nat.cast_one] at hfull
  have he : (n + 1 : ℝ) * (binomialAverage n
      (fun k => Real.log (1 - (k : ℝ) / (n + 1 : ℝ))) p - Real.log (1 - p)) =
      (n + 1 : ℝ) * binomialAverage n
        (fun k => Real.log (1 - (k : ℝ) / (n + 1 : ℝ))) p +
      (-(n + 1 : ℝ) * Real.log (1 - p) +
        (n + 1 : ℝ) * (1 - p) * (-1 / (1 - p))) + (n + 1 : ℝ) := by
    field_simp
    ring
  have hf : binomialEntropyRemainder (n + 1) = fun x =>
      binomialAverage (n + 1) (binomialLogFalling (n + 1)) x +
        (n + 1 : ℝ) * (1 - x) * Real.log (1 - x) + (n + 1 : ℝ) * x := by
    funext x
    simp only [binomialEntropyRemainder, Nat.cast_add, Nat.cast_one]
  rw [hf]
  apply hfull.congr_deriv
  rw [he]
  ring

theorem binomialAverage_log_le (n : ℕ) (p : unitInterval) :
    binomialAverage n (fun k => Real.log (1 - (k : ℝ) / (n + 1 : ℝ))) p ≤
      Real.log (1 - (n : ℝ) * p / (n + 1 : ℝ)) := by
  let X : ℕ → ℝ := fun k => 1 - (k : ℝ) / (n + 1 : ℝ)
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hpos : ∀ᵐ k ∂binomial n p, 0 < X k := by
    filter_upwards [ae_le_of_hasLaw_binomial (HasLaw.id (μ := binomial n p))] with k hk
    change 0 < 1 - (k : ℝ) / (n + 1 : ℝ)
    have hkreal : (k : ℝ) ≤ n := Nat.cast_le.mpr hk
    have hdiv : (k : ℝ) / (n + 1 : ℝ) < 1 := (div_lt_one hn).2 (by linarith)
    linarith
  have hm : (∫ k, X k ∂binomial n p) = 1 - (n : ℝ) * p / (n + 1 : ℝ) := by
    change (∫ k, 1 - (k : ℝ) / (n + 1 : ℝ) ∂binomial n p) = _
    have hsub := integral_sub
      (integrable_const (μ := binomial n p) (1 : ℝ))
      ((integrable_binomial (p := p) (fun k : ℕ => (k : ℝ))).div_const (n + 1 : ℝ))
    rw [hsub, integral_div, integral_binomial_natCast]
    simp only [integral_const, probReal_univ, one_smul]
  have hmpos : 0 < ∫ k, X k ∂binomial n p := by
    rw [hm]
    have hpn : (n : ℝ) * p ≤ n := by
      exact mul_le_of_le_one_right (Nat.cast_nonneg n) p.property.2
    have hdiv : (n : ℝ) * p / (n + 1 : ℝ) < 1 := (div_lt_one hn).2 (by linarith)
    linarith
  have h := integral_log_le_log_integral hpos (integrable_binomial X)
    (integrable_binomial (fun k => Real.log (X k))) hmpos
  rw [hm, integral_binomial_eq_average] at h
  exact h

/-- The derivative bound is uniform in the binomial sample count. -/
theorem binomialEntropyRemainder_derivative_le (n : ℕ) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (n + 1 : ℝ) * (binomialAverage n
      (fun k => Real.log (1 - (k : ℝ) / (n + 1 : ℝ))) p - Real.log (1 - p)) ≤
      p / (1 - p) := by
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hu : 0 < 1 - p := by linarith
  have hmean : 0 < 1 - (n : ℝ) * p / (n + 1 : ℝ) := by
    have hnp : (n : ℝ) * p ≤ n := mul_le_of_le_one_right (Nat.cast_nonneg n) hp1.le
    have hh := (div_lt_one hn).2 (show (n : ℝ) * p < n + 1 from by linarith)
    linarith
  have hJ := binomialAverage_log_le n (⟨p, hp0, hp1.le⟩ : unitInterval)
  have hlog := Real.log_le_sub_one_of_pos (div_pos hmean hu)
  rw [Real.log_div hmean.ne' hu.ne'] at hlog
  have he : (n + 1 : ℝ) *
      ((1 - (n : ℝ) * p / (n + 1 : ℝ)) / (1 - p) - 1) = p / (1 - p) := by
    field_simp
    ring
  have hmul := mul_le_mul_of_nonneg_left hlog hn.le
  rw [he] at hmul
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_right hJ _) hn.le).trans hmul

/-- The finite entropy expression is at most `-p-log(1-p)`, uniformly in `n`. -/
theorem binomialEntropyRemainder_le (n : ℕ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    binomialEntropyRemainder (n + 1) p ≤ -p - Real.log (1 - p) := by
  let F : ℝ → ℝ := fun t => binomialEntropyRemainder (n + 1) t + t + Real.log (1 - t)
  let dF : ℝ → ℝ := fun t => (n + 1 : ℝ) * (binomialAverage n
    (fun k => Real.log (1 - (k : ℝ) / (n + 1 : ℝ))) t - Real.log (1 - t)) +
      1 - 1 / (1 - t)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 p) : HasDerivAt F (dF t) t := by
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hp1
    have hl := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log
      (show 1 - t ≠ 0 from by linarith)
    have hfull := ((hasDerivAt_binomialEntropyRemainder_succ n ht1).add
      (hasDerivAt_id t)).add hl
    dsimp [F, dF]
    apply hfull.congr_deriv
    dsimp
    ring
  have hnon (t : ℝ) (ht : t ∈ Set.Icc 0 p) : dF t ≤ 0 := by
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hp1
    have h := binomialEntropyRemainder_derivative_le n ht.1 ht1
    have hu : 0 < 1 - t := by linarith
    have he : t / (1 - t) + 1 - 1 / (1 - t) = 0 := by field_simp; ring
    dsimp [dF]
    linarith only [h, he]
  have hanti : AntitoneOn F (Set.Icc 0 p) := antitoneOn_of_deriv_nonpos
    (convex_Icc 0 p) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; exact hnon t (interior_subset ht))
  have h := hanti (show 0 ∈ Set.Icc 0 p from ⟨le_rfl, hp0⟩)
    (show p ∈ Set.Icc 0 p from ⟨hp0, le_rfl⟩) hp0
  simp only [F, binomialEntropyRemainder_zero, sub_zero, Real.log_one,
    add_zero] at h
  linarith only [h]

theorem binomial_entropy_log_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p < 1) :
    -p - Real.log (1 - p) ≤ p ^ 2 / (2 * (1 - p)) := by
  let F : ℝ → ℝ := fun t => t ^ 2 / (2 * (1 - t)) + t + Real.log (1 - t)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 0 p) :
      HasDerivAt F (t ^ 2 / (2 * (1 - t) ^ 2)) t := by
    have hne : 1 - t ≠ 0 := by linarith [ht.2]
    have hu := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have hq := ((hasDerivAt_id t).pow 2).div (hu.const_mul 2)
      (show 2 * (1 - t) ≠ 0 from mul_ne_zero (by norm_num) hne)
    have hl := hu.log hne
    have hfull := (hq.add (hasDerivAt_id t)).add hl
    change HasDerivAt (fun t => t ^ 2 / (2 * (1 - t)) + t + Real.log (1 - t)) _ t
    apply hfull.congr_deriv
    dsimp
    field_simp
    ring
  have hmono : MonotoneOn F (Set.Icc 0 p) := monotoneOn_of_deriv_nonneg
    (convex_Icc 0 p) (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hd t (interior_subset ht)).deriv]; positivity)
  have h := hmono (show 0 ∈ Set.Icc 0 p from ⟨le_rfl, hp0⟩)
    (show p ∈ Set.Icc 0 p from ⟨hp0, le_rfl⟩) hp0
  have hz : F 0 = 0 := by simp [F]
  rw [hz] at h
  dsimp [F] at h
  linarith only [h]

end

end ProbabilityTheory
