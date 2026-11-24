import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ReciprocalSinhMoments
import Mathlib.Data.Nat.Choose.Sum

/-! # The anchored moment polynomial and its finite odd-zeta integral -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def anchoredMomentPolynomial (q : ℕ) (y : ℝ) : ℝ :=
  (((y : ℂ) + Complex.I) * ((y : ℂ) ^ 2 + 2 * (y : ℂ) * Complex.I) ^ q).im

private def momentBinomialTerm (q k : ℕ) (y : ℝ) : ℝ :=
  (((y : ℂ) + Complex.I) * (2 * (y : ℂ) * Complex.I) ^ k *
    ((y : ℂ) ^ 2) ^ (q - k) * (q.choose k : ℂ)).im

private theorem sum_range_pairs (f : ℕ → ℝ) (m : ℕ) :
    (∑ k ∈ range (2 * m), f k) = ∑ l ∈ range m, (f (2 * l) + f (2 * l + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

private theorem momentBinomialTerm_even (q l : ℕ) (y : ℝ) (hl : 2 * l ≤ q) :
    momentBinomialTerm q (2 * l) y =
      (-1 : ℝ) ^ l * 4 ^ l * (q.choose (2 * l) : ℝ) * y ^ (2 * (q - l)) := by
  have hi : Complex.I ^ (2 * l) = ((-1 : ℝ) ^ l : ℂ) := by
    push_cast
    rw [pow_mul, Complex.I_sq]
  have he : 2 * l + 2 * (q - 2 * l) = 2 * (q - l) := by omega
  have hy : y ^ (2 * l) * (y ^ 2) ^ (q - 2 * l) = y ^ (2 * (q - l)) := by
    rw [← pow_mul, ← pow_add, he]
  have ht : (2 : ℝ) ^ (2 * l) = 4 ^ l := by rw [pow_mul]; norm_num
  unfold momentBinomialTerm
  rw [mul_pow, mul_pow, hi]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
    Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    add_zero, zero_add, mul_zero, zero_mul, one_mul, sub_zero]
  rw [ht, ← hy]
  ring

private theorem momentBinomialTerm_eq_zero {q k : ℕ} (hk : q < k) (y : ℝ) :
    momentBinomialTerm q k y = 0 := by
  simp [momentBinomialTerm, Nat.choose_eq_zero_of_lt hk]

private theorem momentBinomialTerm_odd (q l : ℕ) (y : ℝ) :
    momentBinomialTerm q (2 * l + 1) y =
      (-1 : ℝ) ^ l * 4 ^ l * (2 * (q.choose (2 * l + 1) : ℝ)) * y ^ (2 * (q - l)) := by
  by_cases hl : 2 * l + 1 ≤ q
  · have hi : Complex.I ^ (2 * l + 1) = ((-1 : ℝ) ^ l : ℂ) * Complex.I := by
      push_cast
      rw [pow_succ, pow_mul, Complex.I_sq]
    have hy : y * y ^ (2 * l + 1) * (y ^ 2) ^ (q - (2 * l + 1)) =
        y ^ (2 * (q - l)) := by
      rw [← pow_succ', ← pow_mul, ← pow_add]
      congr 1
      omega
    have ht : (2 : ℝ) ^ (2 * l + 1) = 4 ^ l * 2 := by rw [pow_succ, pow_mul]; norm_num
    unfold momentBinomialTerm
    rw [mul_pow, mul_pow, hi]
    simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_natCast,
      Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      add_zero, zero_add, mul_zero, zero_mul, one_mul, mul_one, sub_zero, zero_sub]
    rw [ht, ← hy]
    ring
  · have hlt : q < 2 * l + 1 := by omega
    rw [momentBinomialTerm_eq_zero hlt, Nat.choose_eq_zero_of_lt hlt]
    simp

/-- The binomial expansion in the manuscript, with its exact finite index range. -/
theorem anchoredMomentPolynomial_eq_sum (q : ℕ) (y : ℝ) :
    anchoredMomentPolynomial q y = ∑ l ∈ range (q / 2 + 1),
      (-1 : ℝ) ^ l * 4 ^ l *
        ((q.choose (2 * l) : ℝ) + 2 * (q.choose (2 * l + 1) : ℝ)) * y ^ (2 * (q - l)) := by
  have he : anchoredMomentPolynomial q y = ∑ k ∈ range (q + 1), momentBinomialTerm q k y := by
    unfold anchoredMomentPolynomial
    rw [add_comm ((y : ℂ) ^ 2), add_pow, mul_sum, Complex.im_sum]
    apply sum_congr rfl
    intro k _
    unfold momentBinomialTerm
    congr 1
    ring
  rw [he]
  calc
    _ = ∑ k ∈ range (2 * (q / 2 + 1)), momentBinomialTerm q k y := by
      apply sum_subset (range_mono (by omega))
      intro k _ hk
      exact momentBinomialTerm_eq_zero (by
        have hk' : q + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
        omega) y
    _ = _ := by
      rw [sum_range_pairs]
      apply sum_congr rfl
      intro l hl
      have hle : 2 * l ≤ q := by have := mem_range.mp hl; omega
      rw [momentBinomialTerm_even q l y hle, momentBinomialTerm_odd]
      ring

/-- Every monomial has positive even degree when the moment order is positive. -/
theorem anchoredMomentPolynomial_integrable {q : ℕ} (hq : 0 < q) :
    IntegrableOn (fun y => anchoredMomentPolynomial q y / Real.sinh (Real.pi * y / 2))
      (Ioi 0) := by
  have he (y : ℝ) : anchoredMomentPolynomial q y / Real.sinh (Real.pi * y / 2) =
      ∑ l ∈ range (q / 2 + 1),
        ((-1 : ℝ) ^ l * 4 ^ l *
          ((q.choose (2 * l) : ℝ) + 2 * (q.choose (2 * l + 1) : ℝ))) *
        (y ^ (2 * (q - l)) / Real.sinh (Real.pi * y / 2)) := by
    rw [anchoredMomentPolynomial_eq_sum, sum_div]
    apply sum_congr rfl
    intro l _
    ring
  simp only [he]
  apply integrable_finsetSum
  intro l hl
  exact (integrableOn_even_pow_div_sinh_pi (by have := Finset.mem_range.mp hl; omega)).const_mul _

/-- Termwise integration of the finite polynomial gives exactly the odd-zeta sum. -/
theorem integral_anchoredMomentPolynomial {q : ℕ} (hq : 0 < q) :
    (∫ y in Ioi 0, anchoredMomentPolynomial q y / Real.sinh (Real.pi * y / 2)) =
      ∑ l ∈ range (q / 2 + 1),
        ((-1 : ℝ) ^ l * 4 ^ l *
          ((q.choose (2 * l) : ℝ) + 2 * (q.choose (2 * l + 1) : ℝ))) *
        (2 * ((2 * (q - l)).factorial : ℝ) * ((2 : ℝ) ^ (2 * (q - l) + 1) - 1) /
          Real.pi ^ (2 * (q - l) + 1) * (riemannZeta ((2 * (q - l) + 1 : ℕ) : ℂ)).re) := by
  have he (y : ℝ) : anchoredMomentPolynomial q y / Real.sinh (Real.pi * y / 2) =
      ∑ l ∈ range (q / 2 + 1),
        ((-1 : ℝ) ^ l * 4 ^ l *
          ((q.choose (2 * l) : ℝ) + 2 * (q.choose (2 * l + 1) : ℝ))) *
        (y ^ (2 * (q - l)) / Real.sinh (Real.pi * y / 2)) := by
    rw [anchoredMomentPolynomial_eq_sum, sum_div]
    apply sum_congr rfl
    intro l _
    ring
  simp only [he]
  rw [integral_finsetSum _ (fun l hl =>
    (integrableOn_even_pow_div_sinh_pi (by have := Finset.mem_range.mp hl; omega)).const_mul _)]
  apply sum_congr rfl
  intro l hl
  rw [integral_const_mul, integral_even_pow_div_sinh_pi
    (by have := Finset.mem_range.mp hl; omega)]

/-- The analytic moment integral, before it is connected to the actual lifetime by contour shift. -/
def anchoredMomentIntegral (q : ℕ) : ℝ :=
  Real.pi / ((2 : ℝ) ^ (q + 1) * Real.Gamma q) *
    ∫ y in Ioi 0, anchoredMomentPolynomial q y / Real.sinh (Real.pi * y / 2)

theorem anchoredMomentPolynomial_one (y : ℝ) : anchoredMomentPolynomial 1 y = 3 * y ^ 2 := by
  rw [anchoredMomentPolynomial_eq_sum]
  norm_num [sum_range_succ, Nat.choose]

theorem anchoredMomentPolynomial_two (y : ℝ) :
    anchoredMomentPolynomial 2 y = 5 * y ^ 4 - 4 * y ^ 2 := by
  rw [anchoredMomentPolynomial_eq_sum]
  norm_num [sum_range_succ, Nat.choose]
  ring

theorem anchoredMomentPolynomial_three (y : ℝ) :
    anchoredMomentPolynomial 3 y = 7 * y ^ 6 - 20 * y ^ 4 := by
  rw [anchoredMomentPolynomial_eq_sum]
  norm_num [sum_range_succ, Nat.choose]
  ring

theorem anchoredMomentPolynomial_four (y : ℝ) :
    anchoredMomentPolynomial 4 y = 9 * y ^ 8 - 56 * y ^ 6 + 16 * y ^ 4 := by
  rw [anchoredMomentPolynomial_eq_sum]
  norm_num [sum_range_succ, Nat.choose]
  ring

theorem anchoredMomentIntegral_one :
    anchoredMomentIntegral 1 = 21 * (riemannZeta 3).re / Real.pi ^ 2 := by
  unfold anchoredMomentIntegral
  rw [integral_anchoredMomentPolynomial (by norm_num : 0 < 1)]
  norm_num [sum_range_succ, Nat.choose, Nat.factorial]
  field_simp
  ring

theorem anchoredMomentIntegral_two :
    anchoredMomentIntegral 2 = 930 * (riemannZeta 5).re / Real.pi ^ 4 -
      14 * (riemannZeta 3).re / Real.pi ^ 2 := by
  unfold anchoredMomentIntegral
  rw [integral_anchoredMomentPolynomial (by norm_num : 0 < 2)]
  have hg : Real.Gamma 2 = 1 := by norm_num [Nat.factorial]
  norm_num [sum_range_succ, Nat.choose, Nat.factorial, hg]
  field_simp
  ring

theorem anchoredMomentIntegral_three :
    anchoredMomentIntegral 3 = 40005 * (riemannZeta 7).re / Real.pi ^ 6 -
      930 * (riemannZeta 5).re / Real.pi ^ 4 := by
  unfold anchoredMomentIntegral
  rw [integral_anchoredMomentPolynomial (by norm_num : 0 < 3)]
  have hg : Real.Gamma 3 = 2 := by norm_num [Nat.factorial]
  norm_num [sum_range_succ, Nat.choose, Nat.factorial, hg]
  field_simp
  ring

theorem anchoredMomentIntegral_four :
    anchoredMomentIntegral 4 = 1931580 * (riemannZeta 9).re / Real.pi ^ 8 -
      53340 * (riemannZeta 7).re / Real.pi ^ 6 + 124 * (riemannZeta 5).re / Real.pi ^ 4 := by
  unfold anchoredMomentIntegral
  rw [integral_anchoredMomentPolynomial (by norm_num : 0 < 4)]
  have hg : Real.Gamma 4 = 6 := by norm_num [Nat.factorial]
  norm_num [sum_range_succ, Nat.choose, Nat.factorial, hg]
  field_simp
  ring

end BrownianAffine
