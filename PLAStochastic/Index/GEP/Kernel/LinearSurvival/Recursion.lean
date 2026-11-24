import PLAStochastic.Index.GEP.Kernel.LinearSurvival.LaplaceExtraction

/-! # Sharp inverse-square-root bounds from the killed-walk recursion -/

namespace PGM

noncomputable section

open Finset

/-- The reciprocal square-root sum has the exact diffusive scale. -/
theorem linearSurvival_sum_inv_sqrt (n : ℕ) :
    ∑ j ∈ range n, (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹ ≤ 2 * Real.sqrt n := by
  have hterm (j : ℕ) : (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹ ≤
      2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt j) := by
    have hp : 0 < Real.sqrt ((j + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    rw [inv_eq_one_div, div_le_iff₀ hp]
    have hsq1 := Real.sq_sqrt (show (0 : ℝ) ≤ (j + 1 : ℕ) by positivity)
    have hsq0 := Real.sq_sqrt (show (0 : ℝ) ≤ j by positivity)
    have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by simp
    nlinarith [sq_nonneg (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt j)]
  calc
    _ ≤ ∑ j ∈ range n, 2 * (Real.sqrt ((j + 1 : ℕ) : ℝ) - Real.sqrt j) :=
      sum_le_sum fun j _ => hterm j
    _ = 2 * Real.sqrt n := by
      rw [← mul_sum]
      have he := Finset.sum_range_sub (fun j : ℕ => Real.sqrt (j : ℝ)) n
      rw [he]
      simp

/-- The drift occupation term is absorbed on a class-uniform diffusive window. -/
theorem linearSurvival_recursion_short {q : ℕ → ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hq : ∀ n, q n ≤ 1) {H c B ρ : ℝ} (hc : 0 < c) (hρ : 0 ≤ ρ)
    (hB : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ B) (hHB : 4 * H ≤ c * B)
    (hrec : ∀ n : ℕ, N ≤ n →
      q n ≤ q (n / 2) / 8 +
        (H + ρ * ∑ j ∈ range n, q j) / (c * Real.sqrt ((n + 1 : ℕ) : ℝ))) :
    ∀ n : ℕ, ρ * Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ c / 8 →
      q n ≤ B / Real.sqrt ((n + 1 : ℕ) : ℝ) := by
  have hB0 : 0 < B := (Real.sqrt_pos.2 (by positivity)).trans_le hB
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hscale
    have hr : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
    by_cases hn : n < N
    · have hroot : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ B :=
        (Real.sqrt_le_sqrt (by exact_mod_cast (show n + 1 ≤ N + 1 by omega))).trans hB
      apply (hq n).trans
      rw [le_div_iff₀ hr]
      simpa using hroot
    · have hNn : N ≤ n := by omega
      have hn1 : 1 ≤ n := hN.trans hNn
      have hm : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hrootle (j : ℕ) (hj : j ≤ n) :
          Real.sqrt ((j + 1 : ℕ) : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast (Nat.add_le_add_right hj 1))
      have hqsmall (j : ℕ) (hj : j < n) : q j ≤ B / Real.sqrt ((j + 1 : ℕ) : ℝ) :=
        ih j hj ((mul_le_mul_of_nonneg_left (hrootle j hj.le) hρ).trans hscale)
      have hsum : ∑ j ∈ range n, q j ≤ 2 * B * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
        calc
          _ ≤ ∑ j ∈ range n, B * (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹ :=
            sum_le_sum fun j hj => by simpa only [div_eq_mul_inv] using hqsmall j (mem_range.1 hj)
          _ = B * ∑ j ∈ range n, (Real.sqrt ((j + 1 : ℕ) : ℝ))⁻¹ := (mul_sum _ _ _).symm
          _ ≤ B * (2 * Real.sqrt n) := mul_le_mul_of_nonneg_left (linearSurvival_sum_inv_sqrt n) hB0.le
          _ ≤ 2 * B * Real.sqrt ((n + 1 : ℕ) : ℝ) := by
            have hs := Real.sqrt_le_sqrt (show (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) by norm_num)
            nlinarith
      have hmroot : Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt ((n / 2 + 1 : ℕ) : ℝ) := by
        apply Real.sqrt_le_iff.2
        refine ⟨by positivity, ?_⟩
        have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) by positivity)
        have hnle : n + 1 ≤ 4 * (n / 2 + 1) := by omega
        have hreal : ((n + 1 : ℕ) : ℝ) ≤ 4 * ((n / 2 + 1 : ℕ) : ℝ) := by exact_mod_cast hnle
        nlinarith
      have hqm : q (n / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ 2 * B := by
        have hh := mul_le_mul_of_nonneg_right (hqsmall (n / 2) hm) hr.le
        have hmr : 0 < Real.sqrt ((n / 2 + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
        have hratio : Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt ((n / 2 + 1 : ℕ) : ℝ) ≤ 2 := by
          rw [div_le_iff₀ hmr]
          exact hmroot
        calc
          _ ≤ B / Real.sqrt ((n / 2 + 1 : ℕ) : ℝ) * Real.sqrt ((n + 1 : ℕ) : ℝ) := hh
          _ = B * (Real.sqrt ((n + 1 : ℕ) : ℝ) / Real.sqrt ((n / 2 + 1 : ℕ) : ℝ)) := by ring
          _ ≤ 2 * B := by nlinarith
      have hocc : ρ * (∑ j ∈ range n, q j) ≤ c * B / 4 := by
        have hh := mul_le_mul_of_nonneg_left hsum hρ
        nlinarith [mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * B by positivity)]
      have hforce : (H + ρ * ∑ j ∈ range n, q j) / c ≤ B / 2 := by
        rw [div_le_iff₀ hc]
        linarith
      rw [le_div_iff₀ hr]
      have hh := mul_le_mul_of_nonneg_right (hrec n hNn) hr.le
      have he : (q (n / 2) / 8 + (H + ρ * ∑ j ∈ range n, q j) /
          (c * Real.sqrt ((n + 1 : ℕ) : ℝ))) * Real.sqrt ((n + 1 : ℕ) : ℝ) =
          q (n / 2) * Real.sqrt ((n + 1 : ℕ) : ℝ) / 8 +
            (H + ρ * ∑ j ∈ range n, q j) / c := by field_simp
      rw [he] at hh
      linarith

end

end PGM
