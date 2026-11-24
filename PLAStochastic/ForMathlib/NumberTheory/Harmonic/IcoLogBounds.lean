import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # Harmonic sums over a range compare with a logarithm of the ratio

The interior summation in the conditional mean asymptotic replaces a sum of
`E/n` over a dyadic-type range by `E` times a logarithm. The additive error is
absolute, hence negligible against `E log E`. -/
noncomputable section
open Finset
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem sum_inv_Ico_one (b : ℕ) (hb : 1 ≤ b) :
    ∑ j ∈ Finset.Ico 1 b, (j : ℝ)⁻¹ = (harmonic (b-1) : ℝ) := by
  have hset : Finset.Ico 1 b = Finset.Icc 1 (b-1) := by
    ext j
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hset]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem sum_inv_Ico_eq (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Finset.Ico a b, (j : ℝ)⁻¹ = (harmonic (b-1) : ℝ)-(harmonic (a-1) : ℝ) := by
  have hb : 1 ≤ b := le_trans ha hab
  have hsplit := Finset.sum_Ico_consecutive (fun j : ℕ => (j : ℝ)⁻¹) ha hab
  rw [sum_inv_Ico_one a ha, sum_inv_Ico_one b hb] at hsplit
  linarith

/-- The range sum is the logarithm of the ratio up to an absolute error. -/
theorem abs_sum_inv_Ico_sub_log_le_one (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∑ j ∈ Finset.Ico a b, (j : ℝ)⁻¹)-(Real.log b-Real.log a)| ≤ 1 := by
  have hb : 1 ≤ b := le_trans ha hab
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have ha1 : ((a-1 : ℕ)+1 : ℕ) = a := by omega
  have hb1 : ((b-1 : ℕ)+1 : ℕ) = b := by omega
  -- lower bounds on each harmonic number
  have hlow_b : Real.log (b : ℝ) ≤ (harmonic (b-1) : ℝ) := by
    have := log_add_one_le_harmonic (b-1)
    rwa [hb1] at this
  have hlow_a : Real.log (a : ℝ) ≤ (harmonic (a-1) : ℝ) := by
    have := log_add_one_le_harmonic (a-1)
    rwa [ha1] at this
  -- upper bounds
  have hup_b : (harmonic (b-1) : ℝ) ≤ 1+Real.log ((b-1 : ℕ) : ℝ) := harmonic_le_one_add_log (b-1)
  have hup_a : (harmonic (a-1) : ℝ) ≤ 1+Real.log ((a-1 : ℕ) : ℝ) := harmonic_le_one_add_log (a-1)
  have hlb : Real.log ((b-1 : ℕ) : ℝ) ≤ Real.log (b : ℝ) := by
    rcases Nat.eq_zero_or_pos (b-1) with h0 | hpos
    · rw [h0]
      simpa using Real.log_nonneg (by exact_mod_cast hb)
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast (by omega : b-1 ≤ b))
  have hla : Real.log ((a-1 : ℕ) : ℝ) ≤ Real.log (a : ℝ) := by
    rcases Nat.eq_zero_or_pos (a-1) with h0 | hpos
    · rw [h0]
      simpa using Real.log_nonneg (by exact_mod_cast ha)
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast (by omega : a-1 ≤ a))
  rw [sum_inv_Ico_eq a b ha hab, abs_le]
  constructor <;> linarith

end SwingRepair
