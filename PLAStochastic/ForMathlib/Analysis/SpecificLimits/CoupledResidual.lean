import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A posteriori bounds for coupled residuals

Two nonnegative residuals satisfy `V (n+1) ≤ r D n` and
`D (n+1) ≤ r D n + K V n`. Their distance tail is controlled by the
initial pair whenever `(K+1)*r < 1`. The proof uses finite sums only.
-/

namespace PGM

open Filter Topology Finset

/-- The coupled recurrence bounds every finite distance tail. -/
theorem coupled_residual_sum_le {D V : ℕ → ℝ} {K r : ℝ}
    (hD : ∀ n, 0 ≤ D n) (hV : ∀ n, 0 ≤ V n) (hK : 0 ≤ K)
    (hq : (K + 1) * r < 1)
    (hDr : ∀ n, D (n + 1) ≤ r * D n + K * V n)
    (hVr : ∀ n, V (n + 1) ≤ r * D n) (j n : ℕ) :
    ∑ k ∈ range n, D (j + k) ≤ (D j + K * V j) / (1 - (K + 1) * r) := by
  have hbudget : ∀ n, (1 - (K + 1) * r) * (∑ k ∈ range n, D (j + k)) +
      D (j + n) + K * V (j + n) ≤ D j + K * V j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      have hd := hDr (j + n)
      have hv := mul_le_mul_of_nonneg_left (hVr (j + n)) hK
      simp only [Nat.add_assoc] at hd hv
      nlinarith
  have hn := hbudget n
  have hv := mul_nonneg hK (hV (j + n))
  apply (le_div_iff₀ (by linarith : 0 < 1 - (K + 1) * r)).2
  nlinarith [hD (j + n)]

/-- Telescope a scalar sequence against a nonnegative error budget. -/
theorem abs_sub_le_sum_increments {f D : ℕ → ℝ} {r : ℝ}
    (h : ∀ n, |f (n + 1) - f n| ≤ r * D n) (j n : ℕ) :
    |f (j + n) - f j| ≤ r * ∑ k ∈ range n, D (j + k) := by
  calc
    |f (j + n) - f j| = |∑ k ∈ range n, (f (j + (k + 1)) - f (j + k))| := by
      rw [sum_range_sub (fun k => f (j + k))]
      simp
    _ ≤ ∑ k ∈ range n, |f (j + (k + 1)) - f (j + k)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ range n, r * D (j + k) := by
      apply sum_le_sum
      intro k _
      simpa only [Nat.add_assoc] using h (j + k)
    _ = r * ∑ k ∈ range n, D (j + k) := (mul_sum _ _ _).symm

/-- A limit of `c` is approximated by the variance-corrected scalar at depth `j`.
The `u` increment starts one layer later, as required by the proxy denominator. -/
theorem coupled_residual_limit_error {D V c u : ℕ → ℝ} {K r s L : ℝ}
    (hD : ∀ n, 0 ≤ D n) (hV : ∀ n, 0 ≤ V n) (hK : 0 ≤ K)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hq : (K + 1) * r < 1)
    (hDr : ∀ n, D (n + 1) ≤ r * D n + K * V n)
    (hVr : ∀ n, V (n + 1) ≤ r * D n)
    (hA : ∀ n, |(u (n + 1) + c (n + 1)) - (u n + c n)| ≤ r * D n)
    (hu : ∀ n, |u (n + 2) - u (n + 1)| ≤ s * D n)
    (hc : Tendsto c atTop (𝓝 L)) (j : ℕ) :
    |L - (u j + c j - u (j + 1))| ≤
      (r + s) * (D j + K * V j) / (1 - (K + 1) * r) := by
  set B := (D j + K * V j) / (1 - (K + 1) * r)
  have hb (n : ℕ) : ∑ k ∈ range n, D (j + k) ≤ B :=
    coupled_residual_sum_le hD hV hK hq hDr hVr j n
  have hfinite (n : ℕ) : |c (j + n + 1) - (u j + c j - u (j + 1))| ≤ (r + s) * B := by
    have ha := abs_sub_le_sum_increments (f := fun k => u k + c k) hA j (n + 1)
    have hv := abs_sub_le_sum_increments (f := fun k => u (k + 1)) hu j n
    have haB := mul_le_mul_of_nonneg_left (hb (n + 1)) hr
    have hvB := mul_le_mul_of_nonneg_left (hb n) hs
    have he : c (j + n + 1) - (u j + c j - u (j + 1)) =
        ((u (j + n + 1) + c (j + n + 1)) - (u j + c j)) -
          (u (j + n + 1) - u (j + 1)) := by ring
    rw [he]
    calc
      |((u (j + n + 1) + c (j + n + 1)) - (u j + c j)) -
          (u (j + n + 1) - u (j + 1))| ≤
          |(u (j + n + 1) + c (j + n + 1)) - (u j + c j)| +
            |u (j + n + 1) - u (j + 1)| := abs_sub _ _
      _ ≤ (r + s) * B := by
        simp only [Nat.add_assoc] at ha hv ⊢
        nlinarith
  have hshift : Tendsto (fun n : ℕ => j + n + 1) atTop atTop := by
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using tendsto_add_atTop_nat (j + 1)
  have hlim := ((hc.comp hshift).sub_const (u j + c j - u (j + 1))).abs
  have h := le_of_tendsto hlim (Filter.Eventually.of_forall hfinite)
  simpa only [B, mul_div_assoc] using h

end PGM
