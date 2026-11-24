import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A sum over two time scales

`∑_{n ≥ 1} n^{-r/2} e^{-a n/ε²} e^{-b ε²/n} ≤ (1 + r!/b^r)(1 + 1/a) ε^{2-r}` for `ε ≥ 1`
(`research/2026-09-29-ceps-full-expansion/output-closure.md` (O13)). The short-time factor
pays for `n^{-r/2}`: with `y = ε²/n`, `n^{-r/2} e^{-by} = y^{r/2} e^{-by} ε^{-r}` is at most
`(1 + r!/b^r) ε^{-r}` (`sqrt_pow_inv_mul_exp_le`); the long-time factor is geometric with
ratio `e^{-a/ε²}` and sum at most `1 + ε²/a` (`tsum_twoScale_le`).
-/

noncomputable section

open Real

namespace PGM

theorem sqrt_pow_inv_mul_exp_le {r : ℕ} {b ε : ℝ} (hb : 0 < b) (hε : 0 < ε) {x : ℝ}
    (hx : 0 < x) :
    (Real.sqrt x ^ r)⁻¹ * Real.exp (-(b * ε ^ 2 / x)) ≤ (1 + r.factorial / b ^ r) / ε ^ r := by
  set y := ε ^ 2 / x with hy
  have hy0 : 0 < y := by positivity
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hprod : Real.sqrt y * Real.sqrt x = ε := by
    rw [← Real.sqrt_mul hy0.le, hy, div_mul_cancel₀ _ hx.ne', Real.sqrt_sq hε.le]
  have hinv : (Real.sqrt x ^ r)⁻¹ = Real.sqrt y ^ r / ε ^ r := by
    rw [← hprod, mul_pow, div_eq_mul_inv, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (pow_pos (Real.sqrt_pos.mpr hy0) r).ne', one_mul]
  have h1 : Real.sqrt y ^ r ≤ 1 + y ^ r := by
    rcases le_total y 1 with hy1 | hy1
    · have : Real.sqrt y ^ r ≤ 1 := pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr hy1)
      linarith [pow_nonneg hy0.le r]
    · have : Real.sqrt y ≤ y := Real.sqrt_le_self_iff.mpr (Or.inr hy1)
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) this r
      linarith
  have h2 : y ^ r * Real.exp (-(b * y)) ≤ r.factorial / b ^ r := by
    have := Real.pow_div_factorial_le_exp (x := b * y) (mul_pos hb hy0).le r
    rw [div_le_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (pow_pos hb r), Real.exp_neg, mul_pow] at *
    have he := Real.exp_pos (b * y)
    calc y ^ r * (Real.exp (b * y))⁻¹ * b ^ r = b ^ r * y ^ r * (Real.exp (b * y))⁻¹ := by ring
      _ ≤ Real.exp (b * y) * r.factorial *
          (Real.exp (b * y))⁻¹ := mul_le_mul_of_nonneg_right this (inv_nonneg.mpr he.le)
      _ = r.factorial := by field_simp
  have h3 : Real.exp (-(b * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hby : b * ε ^ 2 / x = b * y := by rw [hy]; ring
  rw [hinv, hby, div_mul_eq_mul_div, div_le_div_iff_of_pos_right (pow_pos hε r)]
  calc Real.sqrt y ^ r * Real.exp (-(b * y)) ≤ (1 + y ^ r) * Real.exp (-(b * y)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (-(b * y)) + y ^ r * Real.exp (-(b * y)) := by ring
    _ ≤ 1 + r.factorial / b ^ r := by linarith

/-- **The two-scale sum** (`output-closure.md` (O13)). -/
theorem tsum_twoScale_le {r : ℕ} {a b ε M : ℝ} (ha : 0 < a) (hb : 0 < b) (hε : 1 ≤ ε)
    (hM : 0 ≤ M) {g : ℕ → ℝ} (hg0 : ∀ n, 0 ≤ g n) (hgz : g 0 = 0)
    (hg : ∀ n : ℕ, 1 ≤ n → g n ≤ M * ((Real.sqrt n ^ r)⁻¹ * Real.exp (-(a * n / ε ^ 2)) *
      Real.exp (-(b * ε ^ 2 / n)))) :
    Summable g ∧
      ∑' n, g n ≤ M * ((1 + r.factorial / b ^ r) * (1 + 1 / a)) * (ε ^ 2 / ε ^ r) := by
  have hε0 : 0 < ε := by linarith
  set q : ℝ := Real.exp (-(a / ε ^ 2)) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr
    (by have h := (show 0 < a / ε ^ 2 by positivity); linarith)
  set c : ℝ := M * ((1 + r.factorial / b ^ r) / ε ^ r) with hc
  have hc0 : 0 ≤ c := by positivity
  have hle : ∀ n, g n ≤ c * q ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hgz]; positivity
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    refine (hg n hn).trans ?_
    have hgeo : Real.exp (-(a * n / ε ^ 2)) = q ^ n := by
      rw [hq, ← Real.exp_nat_mul]; congr 1; ring
    rw [hgeo]
    calc M * ((Real.sqrt n ^ r)⁻¹ * q ^ n * Real.exp (-(b * ε ^ 2 / n)))
        = M * ((Real.sqrt n ^ r)⁻¹ * Real.exp (-(b * ε ^ 2 / n))) * q ^ n := by ring
      _ ≤ c * q ^ n := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (sqrt_pow_inv_mul_exp_le hb hε0 hn') hM) (pow_nonneg hq0 n)
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left c
  have hsum : Summable g := Summable.of_nonneg_of_le hg0 hle hgeo.summable
  refine ⟨hsum, ?_⟩
  have h1 : ∑' n, g n ≤ c * (1 - q)⁻¹ := (hsum.tsum_le_tsum hle hgeo.summable).trans_eq
    hgeo.tsum_eq
  have ht : 0 < a / ε ^ 2 := by positivity
  have h2 : (1 - q)⁻¹ ≤ 1 + ε ^ 2 / a := by
    have hexp : Real.exp (a / ε ^ 2) * q = 1 := by rw [hq, ← Real.exp_add]; simp
    have hge : 1 + a / ε ^ 2 ≤ Real.exp (a / ε ^ 2) := by
      linarith [Real.add_one_le_exp (a / ε ^ 2)]
    have hq' : q ≤ 1 / (1 + a / ε ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [Real.exp_pos (a / ε ^ 2)]
    have h1q : a / ε ^ 2 / (1 + a / ε ^ 2) ≤ 1 - q := by
      have : 1 - 1 / (1 + a / ε ^ 2) = a / ε ^ 2 / (1 + a / ε ^ 2) := by
        field_simp
        ring
      linarith
    have hpos : 0 < a / ε ^ 2 / (1 + a / ε ^ 2) := by positivity
    calc (1 - q)⁻¹ ≤ (a / ε ^ 2 / (1 + a / ε ^ 2))⁻¹ := inv_anti₀ hpos h1q
      _ = 1 + ε ^ 2 / a := by field_simp; ring
  have h3 : 1 + ε ^ 2 / a ≤ (1 + 1 / a) * ε ^ 2 := by
    have : 1 ≤ ε ^ 2 := by nlinarith
    have : ε ^ 2 / a = (1 / a) * ε ^ 2 := by ring
    nlinarith [one_div_pos.mpr ha]
  calc ∑' n, g n ≤ c * (1 - q)⁻¹ := h1
    _ ≤ c * ((1 + 1 / a) * ε ^ 2) := mul_le_mul_of_nonneg_left (h2.trans h3) hc0
    _ = M * ((1 + r.factorial / b ^ r) * (1 + 1 / a)) * (ε ^ 2 / ε ^ r) := by
        rw [hc]; ring

end PGM
