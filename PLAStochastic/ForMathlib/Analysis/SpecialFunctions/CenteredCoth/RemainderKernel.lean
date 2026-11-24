import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.PartialFractions

/-! # Continuous positive remainder kernels for the actual centered cotangent -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A positive rational summand after subtracting successive odd Taylor terms. -/
def cothRemainderTerm (p n : ℕ) (x : ℝ) : ℝ :=
  2/(cothPole n^(2*p)*(x^2+cothPole n^2))

def cothRemainder (p : ℕ) (x : ℝ) : ℝ := ∑' n, cothRemainderTerm p n x

theorem summable_cothPole_inv_pow {k : ℕ} (hk : 1 < k) :
    Summable (fun n : ℕ => 1/cothPole n^k) := by
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr hk)
  convert! h.mul_left (1/Real.pi^k) using 1
  funext n
  simp only [cothPole, Nat.cast_add, Nat.cast_one, mul_pow, div_eq_mul_inv, mul_inv_rev,
    one_mul]
  ring

theorem cothRemainderTerm_nonneg (p n : ℕ) (x : ℝ) : 0 ≤ cothRemainderTerm p n x := by
  have ha := cothPole_pos n
  unfold cothRemainderTerm
  positivity

theorem cothRemainderTerm_bound (p n : ℕ) (x : ℝ) :
    ‖cothRemainderTerm p n x‖ ≤ 2/cothPole n^(2*p+2) := by
  have ha := cothPole_pos n
  rw [Real.norm_eq_abs, abs_of_nonneg (cothRemainderTerm_nonneg p n x)]
  unfold cothRemainderTerm
  rw [pow_add]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  gcongr
  exact le_add_of_nonneg_left (sq_nonneg x)

theorem summable_cothRemainderTerm (p : ℕ) (x : ℝ) :
    Summable (fun n => cothRemainderTerm p n x) := by
  have h := (summable_cothPole_inv_pow (by omega : 1 < 2*p+2)).mul_left 2
  simp only [mul_one_div] at h
  exact h.of_norm_bounded (cothRemainderTerm_bound p · x)

theorem continuous_cothRemainder (p : ℕ) : Continuous (cothRemainder p) := by
  have h := (summable_cothPole_inv_pow (by omega : 1 < 2*p+2)).mul_left 2
  simp only [mul_one_div] at h
  apply continuous_tsum _ h (cothRemainderTerm_bound p)
  intro n
  have ha := cothPole_pos n
  unfold cothRemainderTerm
  apply Continuous.div continuous_const (by fun_prop)
  intro x
  positivity

theorem cothRemainder_nonneg (p : ℕ) (x : ℝ) : 0 ≤ cothRemainder p x :=
  tsum_nonneg (fun n => cothRemainderTerm_nonneg p n x)

theorem cothRemainder_zero (p : ℕ) :
    cothRemainder p 0 = ∑' n, 2/cothPole n^(2*p+2) := by
  apply tsum_congr
  intro n
  simp only [cothRemainderTerm, zero_pow (by decide : 2 ≠ 0), zero_add, pow_add]

theorem cothRemainder_recurrence (p : ℕ) (x : ℝ) :
    cothRemainder p x = cothRemainder p 0-x^2*cothRemainder (p+1) x := by
  rw [cothRemainder_zero]
  unfold cothRemainder
  rw [← tsum_mul_left]
  have hs := (summable_cothPole_inv_pow (by omega : 1 < 2*p+2)).mul_left 2
  simp only [mul_one_div] at hs
  rw [← hs.tsum_sub ((summable_cothRemainderTerm (p+1) x).mul_left (x^2))]
  apply tsum_congr
  intro n
  have ha := cothPole_pos n
  unfold cothRemainderTerm
  rw [show 2*(p+1) = 2*p+2 by omega, pow_add]
  field_simp
  ring

theorem centeredCoth_eq_mul_remainder {x : ℝ} (hx : 0 < x) :
    centeredCoth x = x*cothRemainder 0 x := by
  rw [← (hasSum_centeredCoth hx).tsum_eq, cothRemainder, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [cothRemainderTerm, Nat.mul_zero, pow_zero, one_mul]
  ring

end BrownianAffine
