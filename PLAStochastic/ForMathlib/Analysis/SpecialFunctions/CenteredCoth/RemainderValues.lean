import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.CenteredCoth.RemainderIntegral
import Mathlib.NumberTheory.ZetaValues

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

private theorem bernoulli_six_value : bernoulli 6 = 1/42 := by
  have hb5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, hb5]

private theorem bernoulli_eight_value : bernoulli 8 = -1/30 := by
  have hb5 : bernoulli' 5 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have hb7 : bernoulli' 7 = 0 := bernoulli'_eq_zero_of_odd (by decide) (by decide)
  have hb6 : bernoulli' 6 = 1/42 := by
    rw [← bernoulli_eq_bernoulli'_of_ne_one (by decide)]
    exact bernoulli_six_value
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide),bernoulli'_def]
  norm_num [Finset.sum_range_succ, Nat.choose, hb5,hb6,hb7]

theorem cothRemainder_zero_eq_zeta (p : ℕ) :
    cothRemainder p 0 = 2*(riemannZeta ((2*p+2 : ℕ) : ℂ)).re/Real.pi^(2*p+2) := by
  rw [cothRemainder_zero]
  simp_rw [div_eq_mul_one_div (2 : ℝ)]
  rw [tsum_mul_left,tsum_cothPole_inv_pow (by omega : 1 < 2*p+2)]
  ring

theorem cothRemainder_zero_zero : cothRemainder 0 0 = 1/3 := by
  rw [cothRemainder_zero_eq_zeta]
  norm_num only
  have hz := tsum_reciprocal_pow_eq_zeta (by decide : 1 < 2)
  norm_num only [Nat.cast_ofNat] at hz
  rw [← hz, hasSum_zeta_two.tsum_eq]
  field_simp
  ring

theorem cothRemainder_one_zero : cothRemainder 1 0 = 1/45 := by
  rw [cothRemainder_zero_eq_zeta]
  norm_num only
  have hz := tsum_reciprocal_pow_eq_zeta (by decide : 1 < 4)
  norm_num only [Nat.cast_ofNat] at hz
  rw [← hz, hasSum_zeta_four.tsum_eq]
  field_simp
  ring

theorem cothRemainder_two_zero : cothRemainder 2 0 = 2/945 := by
  rw [cothRemainder_zero_eq_zeta]
  norm_num only
  have h := (hasSum_zeta_nat (by decide : 3 ≠ 0)).tsum_eq
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [bernoulli_six_value] at h
  have hz := tsum_reciprocal_pow_eq_zeta (by decide : 1 < 6)
  norm_num only [Nat.cast_ofNat] at hz
  rw [← hz, h]
  norm_num [Nat.factorial]
  field_simp
  ring

theorem cothRemainder_three_zero : cothRemainder 3 0 = 1/4725 := by
  rw [cothRemainder_zero_eq_zeta]
  norm_num only
  have h := (hasSum_zeta_nat (by decide : 4 ≠ 0)).tsum_eq
  norm_num only [Nat.reduceMul,Nat.reduceAdd,Nat.reduceSub] at h
  rw [bernoulli_eight_value] at h
  have hz := tsum_reciprocal_pow_eq_zeta (by decide : 1 < 8)
  norm_num only [Nat.cast_ofNat] at hz
  rw [← hz, h]
  norm_num [Nat.factorial]
  field_simp
  ring

end BrownianAffine
