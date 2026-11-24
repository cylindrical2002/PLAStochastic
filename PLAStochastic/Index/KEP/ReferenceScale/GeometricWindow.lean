import PLAStochastic.Index.KEP.ReferenceScale.FiniteWindowTail
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# A common quadratic reference window and geometric stopping blocks

The proved actual-reference stopping tail supplies one window of length
ceiling of a fixed multiple of epsilon squared. Its first survival mass is
at most one sixteenth, and all multiples have a common geometric bound.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepReference_quadratic_geometric_window :
    ∃ D E : ℝ, 1 ≤ D ∧ kepReferenceClassicalThreshold ≤ E ∧ 1 ≤ E ∧
      ∀ eps, E ≤ eps → ∀ j : ℕ,
        let M := ⌈D * eps ^ 2⌉₊
        1 ≤ M ∧ (M : ℝ) ≤ 2 * D * eps ^ 2 ∧
        (iidLaw (kepReferenceLaw eps j)).real {g | (M : ℕ∞) < gapSegLen eps g} ≤ 1 / 16 ∧
        ∀ k : ℕ, (iidLaw (kepReferenceLaw eps j)).real
          {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ (1 / 2 : ℝ) ^ k := by
  obtain ⟨c, e0, hc, he0, htail⟩ := kepReference_finite_window_tail
  let a : ℝ := Real.log (16 * (72 / 71 : ℝ))
  let D := max 1 (a / c)
  refine ⟨D, max e0 1, le_max_left _ _, he0.trans (le_max_left _ _), le_max_right _ _, ?_⟩
  intro eps he j
  let M := ⌈D * eps ^ 2⌉₊
  have he1 : 1 ≤ eps := (le_max_right _ _).trans he
  have heps : 0 < eps := lt_of_lt_of_le zero_lt_one he1
  have hsquare : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hD : 1 ≤ D := le_max_left _ _
  have hDM : 1 ≤ D * eps ^ 2 := by nlinarith
  have hMlo : D * eps ^ 2 ≤ (M : ℝ) := Nat.le_ceil _
  have hM : 1 ≤ M := by exact_mod_cast hDM.trans hMlo
  have hMhi : (M : ℝ) ≤ 2 * D * eps ^ 2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ D * eps ^ 2 by positivity)
    change (M : ℝ) < D * eps ^ 2 + 1 at h
    nlinarith
  have hbound (w : ℕ) : (iidLaw (kepReferenceLaw eps j)).real
      {g | (w : ℕ∞) < gapSegLen eps g} ≤ 72 / 71 * Real.exp (-c * w / eps ^ 2) := by
    have h := htail eps ((le_max_left _ _).trans he) j w 0 w (by omega)
    rw [kep_pi_finite_window_eq_stopping_tail _ eps (by omega)] at h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hca : a ≤ c * D := by
    have h : a / c ≤ D := le_max_right _ _
    exact (div_le_iff₀ hc).mp h |>.trans_eq (mul_comm _ _)
  have hneg : -c * (M : ℝ) / eps ^ 2 ≤ -a := by
    rw [div_le_iff₀ hsquare]
    have h := mul_le_mul_of_nonneg_left hMlo hc.le
    have h' := mul_le_mul_of_nonneg_right hca hsquare.le
    nlinarith
  have hq : 72 / 71 * Real.exp (-c * (M : ℝ) / eps ^ 2) ≤ 1 / 16 := by
    calc
      _ ≤ 72 / 71 * Real.exp (-a) := by gcongr
      _ = 1 / 16 := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 16 * (72 / 71))]
        norm_num
  have heq : Real.exp (-c * (M : ℝ) / eps ^ 2) ≤ 1 / 16 := by
    have h := le_mul_of_one_le_left (Real.exp_nonneg (-c * (M : ℝ) / eps ^ 2))
      (by norm_num : (1 : ℝ) ≤ 72 / 71)
    exact h.trans hq
  refine ⟨hM, hMhi, (hbound M).trans hq, ?_⟩
  intro k
  rcases k with _ | k
  · simpa only [zero_mul, pow_zero, Nat.cast_zero] using
      (measureReal_le_one : (iidLaw (kepReferenceLaw eps j)).real
        {g | (0 : ℕ∞) < gapSegLen eps g} ≤ 1)
  · apply (hbound ((k + 1) * M)).trans
    have hex : -c * (((k + 1) * M : ℕ) : ℝ) / eps ^ 2 =
        (k + 1 : ℕ) * (-c * (M : ℝ) / eps ^ 2) := by push_cast; ring
    rw [hex, Real.exp_nat_mul, pow_succ, ← mul_assoc]
    calc
      _ ≤ (1 / 16 : ℝ) * (1 / 16 : ℝ) ^ k := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul hq (pow_le_pow_left₀ (Real.exp_nonneg _) heq k)
            (pow_nonneg (Real.exp_nonneg _) k) (by norm_num)
      _ = (1 / 16 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) (by norm_num) _

end

end PGM
