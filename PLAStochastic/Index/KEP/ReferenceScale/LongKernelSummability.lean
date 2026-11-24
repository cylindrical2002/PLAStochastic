import PLAStochastic.Index.KEP.ReferenceScale.LongKernelSlope
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Polynomially weighted summability of the long-kernel slope budgets

The killed exponential decay pays any fixed polynomial in the bridge length
at one fixed admissible time weight. This proves convergence of the actual
slope-averaged long-kernel series, before the separate full graph expansion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Removing the integer block division costs only a class constant. -/
theorem kepLongUniformEnergy_le_full_exp {D vlo vhi w : ℝ} (k : ℕ)
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hw : 1 ≤ w) :
    kepLongUniformEnergy D vlo vhi w k ≤
      (Real.sqrt (2 * D / killCnu D vlo vhi) * Real.exp (krKappa D vlo vhi / 2)) *
        Real.exp (-(krKappa D vlo vhi / (8 * w ^ 2)) * k) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw2 : 0 < w ^ 2 := by positivity
  by_cases hk : 4 ≤ k
  · apply (kepLongUniformEnergy_le_exp hD hvlo hvhi hk).trans
    rw [mul_assoc, ← Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    apply Real.exp_le_exp.mpr
    have hfloor : (k : ℝ) ≤ 4 * (k / 4 : ℕ) + 3 := by
      exact_mod_cast (by omega : k ≤ 4 * (k / 4) + 3)
    have hdiv : krKappa D vlo vhi / (2 * w ^ 2) ≤ krKappa D vlo vhi / 2 := by
      apply div_le_div_of_nonneg_left hκ.le (by norm_num : (0 : ℝ) < 2)
      nlinarith
    have hfloor' : krKappa D vlo vhi * ((k : ℝ) / 4 - 1) / (2 * w ^ 2) ≤
        krKappa D vlo vhi * (k / 4 : ℕ) / (2 * w ^ 2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hκ.le
      linarith
    have he : krKappa D vlo vhi * ((k : ℝ) / 4 - 1) / (2 * w ^ 2) =
        krKappa D vlo vhi / (8 * w ^ 2) * k - krKappa D vlo vhi / (2 * w ^ 2) := by
      ring
    rw [he] at hfloor'
    linarith
  · have hk0 : k / 4 = 0 := by omega
    simp only [kepLongUniformEnergy, hk0, Nat.cast_zero, mul_zero, zero_div,
      neg_zero, Real.exp_zero, div_zero, Real.sqrt_zero]
    positivity

theorem summable_polynomial_weighted_kepLongUniformEnergy
    {D vlo vhi w eta : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (hw : 1 ≤ w) (heta : eta < krKappa D vlo vhi / (8 * w ^ 2)) (p : ℕ) :
    Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
      kepLongUniformEnergy D vlo vhi w k) := by
  let r := krKappa D vlo vhi / (8 * w ^ 2) - eta
  let B := Real.sqrt (2 * D / killCnu D vlo vhi) * Real.exp (krKappa D vlo vhi / 2)
  have hr : 0 < r := by dsimp [r]; linarith
  have hs := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hr)
  have hs' : Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (-r * k)) := by
    have hh := hs.mul_left (Real.exp r)
    convert hh using 1 <;> first
    | rfl
    | (funext k
       rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
       congr 2
       ring)
  have hmajor := hs'.mul_left B
  apply hmajor.of_nonneg_of_le
  · intro k
    unfold kepLongUniformEnergy
    positivity
  · intro k
    calc
      _ ≤ (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
          (B * Real.exp (-(krKappa D vlo vhi / (8 * w ^ 2)) * k)) := by
        exact mul_le_mul_of_nonneg_left (kepLongUniformEnergy_le_full_exp k hD hvlo hvhi hw)
          (by positivity)
      _ = B * ((k + 1 : ℝ) ^ p * Real.exp (-r * k)) := by
        dsimp only [r]
        rw [show -(krKappa D vlo vhi / (8 * w ^ 2) - eta) * (k : ℝ) =
          eta * k + (-(krKappa D vlo vhi / (8 * w ^ 2))) * k by ring, Real.exp_add]
        ring

theorem summable_polynomial_weighted_kepLongSecondSlopeBudget
    {D vlo vhi w eta J1 J2 : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (hw : 1 ≤ w) (heta : eta < krKappa D vlo vhi / (8 * w ^ 2)) (p : ℕ) :
    Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
      kepLongSecondSlopeBudget D vlo vhi w k J1 J2) := by
  let C := 8 * Real.pi * Real.sqrt w +
    8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))
  have hs := summable_polynomial_weighted_kepLongUniformEnergy hD hvlo hvhi hw heta p
  have hρ : Real.sqrt (1 - killCnu D vlo vhi) ≤ 1 :=
    (kBVHighStepL2_regLaw_factor_lt_one hD hvlo hvhi).le
  have hsR : Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
      kepLongUniformRemainder D vlo vhi w k) := by
    apply hs.of_nonneg_of_le
    · intro k
      unfold kepLongUniformRemainder kepLongUniformEnergy
      positivity
    · intro k
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      unfold kepLongUniformRemainder
      have hE : 0 ≤ kepLongUniformEnergy D vlo vhi w k := Real.sqrt_nonneg _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ (Real.sqrt_nonneg _) hρ) hE
  have hsum := (hs.mul_left (2 * D * C * (3 + 2 * w) * J1)).add
    (hsR.mul_left (6 * Real.sqrt (2 * D) * J2))
  convert hsum using 1 <;> first
  | rfl
  | (funext k
     dsimp [kepLongSecondSlopeBudget, kepLongUniformVariation, C]
     ring)

end

end PGM
