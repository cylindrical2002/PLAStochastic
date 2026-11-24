import PLAStochastic.Index.CEPS.Glue.Defs

/-!
# WP11a: stretched-exponential bounds of the composed coefficients

If the derivatives of the axis coefficients `y ↦ Ĝ_j(iy; p)` of order `≤ k` are bounded by
`B_g (1+|y|)^d e^{-c√|y|}`, and `c_lo ≤ c₀(p)`, `|c_i(p)| ≤ B`, then the composed coefficient
`Φ_k(u; p) = cepsLowCoeff Gk sc k u p` is bounded by `K (1+|u|)^{d+k} e^{-c'√|u|}` with
`c' = c √(4/B)` (`norm_cepsLowCoeff_le_stretched`). This is the coefficient bound form of T3.
-/

namespace PGM

noncomputable section

open Finset

/-- **Stretched-exponential bound of `Φ_k`.** -/
theorem norm_cepsLowCoeff_le_stretched (k d : ℕ) {c_lo B Bg c : ℝ} (hclo : 0 < c_lo)
    (hc : 0 < c) :
    ∃ K c' : ℝ, 0 ≤ K ∧ 0 < c' ∧ ∀ (Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ) (sc : ℕ → (ℕ → ℝ) → ℝ)
      (p : ℕ → ℝ) (u : ℝ), c_lo ≤ sc 0 p → (∀ i ≤ k, |sc i p| ≤ B) →
      (∀ j ≤ k, ∀ m ≤ k, ∀ y : ℝ, ‖iteratedDeriv m (Gk j p) y‖ ≤
        Bg * (1 + |y|) ^ d * Real.exp (-c * Real.sqrt |y|)) →
      ‖cepsLowCoeff Gk sc k u p‖ ≤ K * cepsStretchedWeight c' (d + k) u := by
  obtain ⟨κ, hκ0, hκ⟩ := norm_lowCompCoeff_le k (B := B) hclo
  set B' : ℝ := max B c_lo with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le hclo (le_max_right _ _)
  refine ⟨κ * |Bg| * (1 + 4 / c_lo) ^ d * 4 ^ k, c * Real.sqrt (4 / B'), by positivity,
    mul_pos hc (Real.sqrt_pos.2 (by positivity)), fun Gk sc p u hc0 hcB hd => ?_⟩
  have hc0pos : 0 < sc 0 p := lt_of_lt_of_le hclo hc0
  have hc0B : sc 0 p ≤ B' := ((le_abs_self _).trans (hcB 0 (Nat.zero_le _))).trans
    (le_max_left _ _)
  set ω : ℝ := -4 * u with hω
  set x₀ : ℝ := ω / sc 0 p with hx₀
  have hx₀abs : |x₀| = 4 * |u| / sc 0 p := by
    rw [hx₀, hω, abs_div, abs_of_pos hc0pos, abs_mul, abs_neg,
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  set X : ℝ := (1 + |x₀|) ^ d * Real.exp (-c * Real.sqrt |x₀|) with hX
  have hX0 : 0 ≤ X := by positivity
  have hA : ∀ j ≤ k, ∀ m ≤ k,
      ‖iteratedDeriv m (fun y => (2⁻¹ : ℂ) ^ j * Gk j p y) (ω / sc 0 p)‖ ≤ |Bg| * X := by
    intro j hj m hm
    rw [iteratedDeriv_const_mul_field, norm_mul, norm_pow, norm_inv, Complex.norm_two]
    have h1 := hd j hj m hm x₀
    calc (2⁻¹ : ℝ) ^ j * ‖iteratedDeriv m (Gk j p) (ω / sc 0 p)‖
        ≤ 1 * ‖iteratedDeriv m (Gk j p) (ω / sc 0 p)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (norm_nonneg _)
      _ ≤ |Bg| * X := by
          rw [one_mul]
          refine h1.trans ?_
          rw [hX, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Bg)
            (by positivity)) (by positivity)
  have h1 := hκ (fun i => sc i p) (fun j y => (2⁻¹ : ℂ) ^ j * Gk j p y) ω (|Bg| * X) hc0 hcB hA
  have hcl : cepsLowCoeff Gk sc k u p =
      lowCompCoeff (fun j y => (2⁻¹ : ℂ) ^ j * Gk j p y) (fun i => sc i p) ω k := rfl
  rw [hcl]
  refine h1.trans ?_
  -- polynomial and exponential parts
  have hpoly : (1 + |x₀|) ^ d ≤ (1 + 4 / c_lo) ^ d * (1 + |u|) ^ d := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ d
    have h2 : |x₀| ≤ 4 / c_lo * |u| := by
      rw [hx₀abs, div_mul_eq_mul_div, div_le_div_iff₀ hc0pos hclo]
      have : 4 * |u| * c_lo ≤ 4 * |u| * sc 0 p := mul_le_mul_of_nonneg_left hc0 (by positivity)
      linarith
    have h3 : 0 ≤ 4 / c_lo := by positivity
    have e : (1 + 4 / c_lo) * (1 + |u|) = 1 + |u| + 4 / c_lo + 4 / c_lo * |u| := by ring
    linarith [abs_nonneg u]
  have hexp : Real.exp (-c * Real.sqrt |x₀|) ≤ Real.exp (-(c * Real.sqrt (4 / B')) * Real.sqrt |u|) := by
    rw [Real.exp_le_exp]
    have hsq : Real.sqrt (4 / B') * Real.sqrt |u| ≤ Real.sqrt |x₀| := by
      rw [← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      rw [hx₀abs, div_mul_eq_mul_div, div_le_div_iff₀ hB'pos hc0pos]
      have : 4 * |u| * sc 0 p ≤ 4 * |u| * B' := mul_le_mul_of_nonneg_left hc0B (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left hsq hc.le
    linarith
  have hω' : (1 + |ω|) ^ k ≤ 4 ^ k * (1 + |u|) ^ k := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ k
    rw [hω, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith [abs_nonneg u]
  have hXb : X ≤ (1 + 4 / c_lo) ^ d * (1 + |u|) ^ d *
      Real.exp (-(c * Real.sqrt (4 / B')) * Real.sqrt |u|) :=
    mul_le_mul hpoly hexp (by positivity) (by positivity)
  calc κ * (|Bg| * X) * (1 + |ω|) ^ k
      ≤ κ * (|Bg| * ((1 + 4 / c_lo) ^ d * (1 + |u|) ^ d *
          Real.exp (-(c * Real.sqrt (4 / B')) * Real.sqrt |u|))) * (4 ^ k * (1 + |u|) ^ k) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hXb (abs_nonneg _)) hκ0) hω' (by positivity) (by positivity)
    _ = κ * |Bg| * (1 + 4 / c_lo) ^ d * 4 ^ k *
          cepsStretchedWeight (c * Real.sqrt (4 / B')) (d + k) u := by
        rw [cepsStretchedWeight, pow_add]
        ring

end

end PGM
