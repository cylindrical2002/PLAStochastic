import PLAStochastic.Swing.FrozenCarry.DurationTail.HarmonicTail

/-! Deterministic estimates for summing the bridge and fresh-block duration tails. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem frozen_cutoff_pos {E : ℝ} (hE : 1 ≤ E) : 0 < ⌈E^2⌉₊ := by
  have h : 0 < E^2 := by positivity
  exact Nat.ceil_pos.mpr h

theorem frozen_cutoff_le {E : ℝ} (hE : 1 ≤ E) : (⌈E^2⌉₊ : ℝ) ≤ E^2+1 := by
  exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ E^2)).le

theorem frozen_cutoff_log_le {E : ℝ} (hE : 1 ≤ E) :
    1+Real.log (⌈E^2⌉₊ : ℝ) ≤ 2*Real.log (Real.exp 1*E) := by
  have hEp : 0 < E := by linarith
  have hE2 : 1 ≤ E^2 := by nlinarith
  have hn : (0 : ℝ) < ⌈E^2⌉₊ := by exact_mod_cast frozen_cutoff_pos hE
  have hlog : Real.log (⌈E^2⌉₊ : ℝ) ≤ Real.log (2*E^2) :=
    Real.log_le_log hn (by linarith [frozen_cutoff_le hE])
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero _ hEp.ne'), Real.log_pow] at hlog
  rw [Real.log_mul (Real.exp_pos _).ne' hEp.ne', Real.log_exp]
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  norm_num at hlog
  linarith

theorem frozen_block_cutoff_ratio_le {E : ℝ} (hE : 1 ≤ E) :
    2*(⌈8*E^2⌉₊ : ℝ)/(⌈E^2⌉₊ : ℝ) ≤ 18 := by
  have hn : (0 : ℝ) < ⌈E^2⌉₊ := by exact_mod_cast frozen_cutoff_pos hE
  apply (div_le_iff₀ hn).mpr
  have hnlo := Nat.le_ceil (E^2)
  have hrhi := (Nat.ceil_lt_add_one (by positivity : 0 ≤ 8*E^2)).le
  have hE2 : 1 ≤ E^2 := by nlinarith
  nlinarith

theorem frozen_log_scale_ge_one {E : ℝ} (hE : 1 ≤ E) :
    1 ≤ Real.log (Real.exp 1*E) := by
  rw [Real.log_mul (Real.exp_pos _).ne' (by linarith : E ≠ 0), Real.log_exp]
  linarith [Real.log_nonneg hE]

end SwingRepair
