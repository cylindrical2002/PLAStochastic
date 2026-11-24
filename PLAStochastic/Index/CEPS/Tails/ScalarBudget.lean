import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Scalar budgets for the cubic time cutoff

These estimates assemble a finite Cramér union budget and two late-time
geometric tails. They do not assume any probability or occupation identity.
The cutoff is the natural ceiling of the actual real width cubed.
-/

namespace PGM

noncomputable section

/-- A geometric denominator costs at most an inverse rate plus one. -/
theorem cepsTail_inv_one_sub_exp_le {x : ℝ} (hx : 0 < x) :
    (1 - Real.exp (-x))⁻¹ ≤ 1 + x⁻¹ := by
  have hp : 0 < 1 + x := by linarith
  have he : Real.exp (-x) ≤ 1 / (1 + x) := by
    have h := one_div_le_one_div_of_le hp (show 1 + x ≤ Real.exp x by
      linarith [Real.add_one_le_exp x])
    simpa only [one_div, Real.exp_neg] using h
  have hl : x / (1 + x) ≤ 1 - Real.exp (-x) := by
    apply (div_le_iff₀ hp).2
    have he' := (le_div_iff₀ hp).mp he
    nlinarith
  have hi := one_div_le_one_div_of_le (div_pos hx hp) hl
  simp only [one_div, inv_div] at hi
  calc
    _ ≤ (1 + x) / x := hi
    _ = 1 + x⁻¹ := by field_simp; ring

/-- Three scalar time-cutoff budgets have one explicit polynomial/exponential envelope. -/
theorem cepsTail_cubic_budget {a b c : ℝ} (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    {w : ℝ} (hw : 1 ≤ w) :
    let N : ℕ := ⌈w ^ 3⌉₊
    ((N : ℝ) + 1) ^ 3 * Real.exp (-a * w) +
      (72 / 71 : ℝ) * Real.exp (-(4 * b * N / w ^ 2)) /
        (1 - Real.exp (-(4 * b / w ^ 2))) +
      Real.exp (-c * N) / (1 - Real.exp (-c)) ≤
    (27 + (72 / 71 : ℝ) * (1 + 1 / (4 * b)) +
      (1 - Real.exp (-c))⁻¹) * w ^ 9 *
        Real.exp (-(min a (min (4 * b) c)) * w) := by
  dsimp only
  let N : ℕ := ⌈w ^ 3⌉₊
  let C : ℝ := min a (min (4 * b) c)
  have hw0 : 0 < w := by linarith
  have hw2 : 1 ≤ w ^ 2 := one_le_pow₀ hw
  have hw3 : 1 ≤ w ^ 3 := one_le_pow₀ hw
  have hw9 : 1 ≤ w ^ 9 := one_le_pow₀ hw
  have hw23 : w ^ 2 ≤ w ^ 9 := pow_le_pow_right₀ hw (by norm_num)
  have hw13 : w ≤ w ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hw (by norm_num : 1 ≤ 3)
  have hN : w ^ 3 ≤ (N : ℝ) := Nat.le_ceil _
  have hNup : (N : ℝ) + 1 ≤ 3 * w ^ 3 := by
    have hn := (Nat.ceil_lt_add_one (show 0 ≤ w ^ 3 by positivity)).le
    change (N : ℝ) ≤ w ^ 3 + 1 at hn
    linarith
  have hpow : ((N : ℝ) + 1) ^ 3 ≤ 27 * w ^ 9 := by
    calc
      _ ≤ (3 * w ^ 3) ^ 3 := by gcongr
      _ = _ := by ring
  have hCa : C ≤ a := min_le_left _ _
  have hCb : C ≤ 4 * b := (min_le_right _ _).trans (min_le_left _ _)
  have hCc : C ≤ c := (min_le_right _ _).trans (min_le_right _ _)
  have hfinite : ((N : ℝ) + 1) ^ 3 * Real.exp (-a * w) ≤
      27 * w ^ 9 * Real.exp (-C * w) := by
    gcongr
  have hrate : 4 * b * w ≤ 4 * b * (N : ℝ) / w ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hw0)).2
    calc
      _ = 4 * b * w ^ 3 := by ring
      _ ≤ _ := by gcongr
  have hgeom : (1 - Real.exp (-(4 * b / w ^ 2)))⁻¹ ≤
      (1 + 1 / (4 * b)) * w ^ 2 := by
    calc
      _ ≤ 1 + (4 * b / w ^ 2)⁻¹ :=
        cepsTail_inv_one_sub_exp_le (by positivity)
      _ = 1 + w ^ 2 / (4 * b) := by rw [inv_div]
      _ ≤ (1 + 1 / (4 * b)) * w ^ 2 := by
        rw [div_eq_mul_inv, one_div]
        nlinarith
  have hneg : (72 / 71 : ℝ) * Real.exp (-(4 * b * N / w ^ 2)) /
        (1 - Real.exp (-(4 * b / w ^ 2))) ≤
      ((72 / 71 : ℝ) * (1 + 1 / (4 * b))) * w ^ 9 * Real.exp (-C * w) := by
    rw [div_eq_mul_inv]
    calc
      _ = (72 / 71 : ℝ) * (1 - Real.exp (-(4 * b / w ^ 2)))⁻¹ *
          Real.exp (-(4 * b * N / w ^ 2)) := by ring
      _ ≤ (72 / 71 : ℝ) * ((1 + 1 / (4 * b)) * w ^ 2) *
          Real.exp (-(4 * b * N / w ^ 2)) := by gcongr
      _ ≤ (72 / 71 : ℝ) * ((1 + 1 / (4 * b)) * w ^ 9) * Real.exp (-C * w) := by
        gcongr
        simpa only [neg_mul] using
          neg_le_neg ((mul_le_mul_of_nonneg_right hCb hw0.le).trans hrate)
      _ = _ := by ring
  have hden : 0 < 1 - Real.exp (-c) := by
    have he : Real.exp (-c) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    simpa only [Real.exp_zero, sub_pos] using he
  have hpos : Real.exp (-c * N) / (1 - Real.exp (-c)) ≤
      (1 - Real.exp (-c))⁻¹ * w ^ 9 * Real.exp (-C * w) := by
    have he : Real.exp (-c * N) ≤ Real.exp (-C * w) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg
        ((mul_le_mul_of_nonneg_right hCc hw0.le).trans
          (mul_le_mul_of_nonneg_left (hw13.trans hN) hc.le))
    rw [div_eq_mul_inv]
    calc
      _ = (1 - Real.exp (-c))⁻¹ * 1 * Real.exp (-c * N) := by ring
      _ ≤ (1 - Real.exp (-c))⁻¹ * w ^ 9 * Real.exp (-c * N) := by gcongr
      _ ≤ (1 - Real.exp (-c))⁻¹ * w ^ 9 * Real.exp (-C * w) :=
        mul_le_mul_of_nonneg_left he (by positivity)
  change _ ≤ (27 + (72 / 71 : ℝ) * (1 + 1 / (4 * b)) +
    (1 - Real.exp (-c))⁻¹) * w ^ 9 * Real.exp (-C * w)
  linarith

/-- The cubic cutoff is beyond the positive-drift endpoint-tail threshold. -/
theorem cepsTail_cubic_cutoff_large {δ w : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hw : max 1 (8 / δ) ≤ w) :
    2 * w * (1 + δ) ≤ δ * (⌈w ^ 3⌉₊ : ℝ) / 2 := by
  have hw1 : 1 ≤ w := (le_max_left _ _).trans hw
  have hw0 : 0 < w := by linarith
  have hδw : 8 ≤ δ * w := by
    have h := (div_le_iff₀ hδ).mp ((le_max_right _ _).trans hw)
    nlinarith
  have hw12 : w ≤ w ^ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ hw1 (by norm_num : 1 ≤ 2)
  have hN : w ^ 3 ≤ (⌈w ^ 3⌉₊ : ℝ) := Nat.le_ceil _
  have hlarge : 8 * w ^ 2 ≤ δ * w ^ 3 := by
    have h := mul_le_mul_of_nonneg_right hδw (sq_nonneg w)
    nlinarith
  have hNδ := mul_le_mul_of_nonneg_left hN hδ.le
  nlinarith [mul_nonneg (show 0 ≤ 1 - δ by linarith) hw0.le]

/-- Existential form consumed by the class-uniform outer-tail assembly. -/
theorem cepsTail_exists_cubic_budget {a b c δ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K C w₀ : ℝ, 0 < K ∧ 0 < C ∧ 0 < w₀ ∧ ∀ w : ℝ, w₀ ≤ w →
      (let N : ℕ := ⌈w ^ 3⌉₊;
        ((N : ℝ) + 1) ^ 3 * Real.exp (-a * w) +
          (72 / 71 : ℝ) * Real.exp (-(4 * b * N / w ^ 2)) /
            (1 - Real.exp (-(4 * b / w ^ 2))) +
          Real.exp (-c * N) / (1 - Real.exp (-c)) ≤
        K * w ^ 9 * Real.exp (-C * w)) ∧
      2 * w * (1 + δ) ≤ δ * (⌈w ^ 3⌉₊ : ℝ) / 2 := by
  refine ⟨27 + (72 / 71 : ℝ) * (1 + 1 / (4 * b)) +
    (1 - Real.exp (-c))⁻¹, min a (min (4 * b) c), max 1 (8 / δ), ?_, ?_, ?_, ?_⟩
  · have hden : 0 < 1 - Real.exp (-c) := by
      have he : Real.exp (-c) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
      simpa only [Real.exp_zero, sub_pos] using he
    positivity
  · exact lt_min ha (lt_min (by positivity) hc)
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro w hw
    exact ⟨cepsTail_cubic_budget ha hb hc ((le_max_left _ _).trans hw),
      cepsTail_cubic_cutoff_large hδ hδ1 hw⟩

end

end PGM
