import PLAStochastic.Index.GEP.Shadow.TreeSwitch.Deterministic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WP3 tree switch: uniform summation of the layer defects (summable-defects)

Source: `research/2026-09-28-gep-closure/memory-route.md` §7, in the form of
`research/2026-09-29-lean-gep-shadow-defects/README.md` (line B): every layer defect is at most
a constant `K₁` and at most `A eps¹¹ σ_ℓ`, where `σ_ℓ = (d₀² (c/eps²)^ℓ)^{1/48}` is an upper
parameter with `σ_ℓ⁴⁸ ≥ d_ℓ²` (`trSig`).  For `c ≤ eps` and `c/eps² ≤ 2⁻⁴⁸`, the bound
`eps¹¹ σ_ℓ ≤ d₀^{2/48} 2^{-(ℓ - 576)}` holds for `ℓ ≥ 576` (`trSig_geom`), so the first `576`
defects are bounded by `K₁` and the rest form a geometric series of ratio `1/2`
(`sum_Ico_le_of_eventually_geom`).  The resulting bound is uniform in `eps`.
-/

namespace PGM

open Finset

/-- Finite sums of a sequence bounded by `K₁`, and by `C 2^{-(j - n₀)}` from `n₀` on. -/
theorem sum_Ico_le_of_eventually_geom {a : ℕ → ℝ} {K₁ C : ℝ} {n₀ : ℕ}
    (ha0 : ∀ j, 0 ≤ a j) (hK : ∀ j, a j ≤ K₁) (hC : 0 ≤ C)
    (hg : ∀ j, n₀ ≤ j → a j ≤ C * (1 / 2) ^ (j - n₀)) (L : ℕ) :
    ∑ j ∈ Ico 1 L, a j ≤ n₀ * K₁ + 2 * C := by
  have h1 : ∑ j ∈ Ico 1 L, a j ≤ ∑ j ∈ range (n₀ + L), a j :=
    sum_le_sum_of_subset_of_nonneg (fun j hj => by
      simp only [mem_Ico] at hj
      simp only [mem_range]
      omega) (fun j _ _ => ha0 j)
  refine h1.trans ?_
  rw [sum_range_add]
  have h3 : ∑ j ∈ range n₀, a j ≤ n₀ * K₁ := by
    calc ∑ j ∈ range n₀, a j ≤ ∑ _j ∈ range n₀, K₁ := sum_le_sum fun j _ => hK j
      _ = n₀ * K₁ := by rw [sum_const, card_range, nsmul_eq_mul]
  have h4 : ∑ i ∈ range L, a (n₀ + i) ≤ 2 * C := by
    calc ∑ i ∈ range L, a (n₀ + i) ≤ ∑ i ∈ range L, C * (1 / 2 : ℝ) ^ i :=
          sum_le_sum fun i _ => by
            have := hg (n₀ + i) (by omega)
            rwa [Nat.add_sub_cancel_left] at this
      _ = C * ∑ i ∈ range L, (1 / 2 : ℝ) ^ i := by rw [mul_sum]
      _ ≤ C * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le L) hC
      _ = 2 * C := by ring
  linarith

/-- The upper parameter `σ_ℓ = (d₀² (c/eps²)^ℓ)^{1/48}` of layer `ℓ`. -/
noncomputable def trSig (d0sq c eps : ℝ) (ℓ : ℕ) : ℝ :=
  (d0sq * (c / eps ^ 2) ^ ℓ) ^ (((48 : ℕ) : ℝ)⁻¹)

theorem trSig_nonneg {d0sq c eps : ℝ} (hd : 0 ≤ d0sq) (hc : 0 ≤ c) (ℓ : ℕ) :
    0 ≤ trSig d0sq c eps ℓ :=
  Real.rpow_nonneg (by positivity) _

theorem trSig_pos {d0sq c eps : ℝ} (hd : 0 < d0sq) (hc : 0 < c) (heps : 0 < eps) (ℓ : ℕ) :
    0 < trSig d0sq c eps ℓ :=
  Real.rpow_pos_of_pos (by positivity) _

theorem trSig_pow {d0sq c eps : ℝ} (hd : 0 ≤ d0sq) (hc : 0 ≤ c) (ℓ : ℕ) :
    trSig d0sq c eps ℓ ^ 48 = d0sq * (c / eps ^ 2) ^ ℓ :=
  Real.rpow_inv_natCast_pow (by positivity) (by norm_num)

/-- `σ_ℓ ≤ 1/2` for `ℓ ≥ 1` once `d₀² c / eps² ≤ 2⁻⁴⁸` and `c ≤ eps²`. -/
theorem trSig_le_half {d0sq c eps : ℝ} (hd : 0 ≤ d0sq) (hc : 0 ≤ c) (heps : 0 < eps)
    (hc1 : c ≤ eps ^ 2) (hsmall : d0sq * (c / eps ^ 2) ≤ (1 / 2) ^ 48) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    trSig d0sq c eps ℓ ≤ 1 / 2 := by
  have hx0 : 0 ≤ c / eps ^ 2 := by positivity
  have hx1 : c / eps ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hc1
  refine (pow_le_pow_iff_left₀ (trSig_nonneg hd hc ℓ) (by norm_num) (by norm_num : 48 ≠ 0)).mp ?_
  rw [trSig_pow hd hc]
  refine le_trans ?_ hsmall
  exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hx0 hx1 (by omega)) hd

/-- **Geometric decay** of `eps¹¹ σ_ℓ` from `ℓ = 576` on, uniformly in `eps`. -/
theorem trSig_geom {d0sq c eps : ℝ} (hd : 0 ≤ d0sq) (hc : 0 ≤ c) (heps : 1 ≤ eps)
    (hce : c ≤ eps) (hc48 : c / eps ^ 2 ≤ (1 / 2) ^ 48) {ℓ : ℕ} (hℓ : 576 ≤ ℓ) :
    eps ^ 11 * trSig d0sq c eps ℓ ≤ d0sq ^ (((48 : ℕ) : ℝ)⁻¹) * (1 / 2) ^ (ℓ - 576) := by
  have hepspos : 0 < eps := by linarith
  set x := c / eps ^ 2 with hx
  have hx0 : 0 ≤ x := by positivity
  have hxe : x ≤ 1 / eps := by
    rw [hx, div_le_div_iff₀ (by positivity) hepspos]
    nlinarith
  have hA : 0 ≤ eps ^ 11 * trSig d0sq c eps ℓ := by
    have := trSig_nonneg hd hc (eps := eps) ℓ
    positivity
  have hs0 : 0 ≤ d0sq ^ (((48 : ℕ) : ℝ)⁻¹) := Real.rpow_nonneg hd _
  refine (pow_le_pow_iff_left₀ hA (by positivity) (by norm_num : 48 ≠ 0)).mp ?_
  have hl : ℓ = 576 + (ℓ - 576) := by omega
  have e1 : (eps ^ 11 * trSig d0sq c eps ℓ) ^ 48 =
      d0sq * ((eps ^ 528 * x ^ 576) * x ^ (ℓ - 576)) := by
    rw [mul_pow, trSig_pow hd hc, ← hx]
    conv_lhs => rw [hl]
    ring
  have e2 : (d0sq ^ (((48 : ℕ) : ℝ)⁻¹) * (1 / 2) ^ (ℓ - 576)) ^ 48 =
      d0sq * ((1 / 2) ^ 48) ^ (ℓ - 576) := by
    rw [mul_pow, Real.rpow_inv_natCast_pow hd (by norm_num), ← pow_mul, ← pow_mul, mul_comm 48]
  rw [e1, e2]
  refine mul_le_mul_of_nonneg_left ?_ hd
  have h1 : eps ^ 528 * x ^ 576 ≤ 1 := by
    have h2 : x ^ 576 ≤ (1 / eps) ^ 576 := pow_le_pow_left₀ hx0 hxe 576
    have h3 : eps ^ 528 * (1 / eps) ^ 576 ≤ 1 := by
      rw [one_div_pow, mul_one_div, div_le_one (by positivity)]
      exact pow_le_pow_right₀ heps (by norm_num)
    have h4 : eps ^ 528 * x ^ 576 ≤ eps ^ 528 * (1 / eps) ^ 576 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith
  have h5 : x ^ (ℓ - 576) ≤ ((1 / 2) ^ 48) ^ (ℓ - 576) := pow_le_pow_left₀ hx0 hc48 _
  have h6 : 0 ≤ x ^ (ℓ - 576) := pow_nonneg hx0 _
  calc eps ^ 528 * x ^ 576 * x ^ (ℓ - 576) ≤ 1 * x ^ (ℓ - 576) :=
        mul_le_mul_of_nonneg_right h1 h6
    _ ≤ ((1 / 2) ^ 48) ^ (ℓ - 576) := by rw [one_mul]; exact h5

end PGM
