import PLAStochastic.Index.GEP.SurvivalBound.ShortSegments
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# WP4 `SurvivalBound`: constants and elementary estimates for the assembly

Source: `task-survival.md` (P4), `progress-surv.md` (总装).

* **Row bounds from the class** (`surv_rowBound`, `surv_rowBound_free`): the class row bound
  `3 √(2Dw) e^{-c₁(n-1)/(2w²)} + ‖z‖ⁿ` on `J = [0, 2ε]` (`w = 2ε`) is dominated by
  `RB n = K₁ ε qⁿ`, `q = e^{-8γ'}`, when `8γ' ≤ c₁/(8ε²)` and `‖z‖ ≤ 1/3`; on `J' = [-ε, 9ε]`
  (`w = 10ε`) the row at `(β, a) = (0, -1)` is at most `K₂ ε`.
* **The good-slope bound of one certificate** (`surv_goodB_le`):
  `goodB ≤ K₁² (3eDK₁ + 1) e^{1/2} (k+1)² ε³ e^{-6γ'k}` for `4γ'ε ≤ 1/2`.
* **Series** (`surv_tsum_exp_neg`, `surv_tsum_poly`): `∑ e^{-βk} ≤ 1 + 1/β` and
  `∑ (k+1)⁴ e^{-αk} ≤ 1152 e^{1/2} (α⁻¹)⁵` for `0 < α ≤ 1`.
* **`k = 0`** (`surv_cSurv_zero_le`): `‖cSurv ε ν σ z 0 G‖ ≤ |G 0|`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-! ## Elementary facts -/

theorem surv_exp_one_le_three : Real.exp 1 ≤ 3 :=
  Real.exp_one_lt_d9.le.trans (by norm_num)

theorem surv_third_le_exp_neg {x : ℝ} (hx : x ≤ 1) : (1 / 3 : ℝ) ≤ Real.exp (-x) := by
  have h1 : Real.exp (-x) ≥ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  have h3 : (1 / 3 : ℝ) ≤ (Real.exp 1)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (Real.exp_pos 1) surv_exp_one_le_three
  linarith

theorem surv_norm_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) : ‖1 - z‖ ≤ 2 := by
  have := norm_sub_le (1 : ℂ) z
  rw [norm_one] at this
  linarith

theorem surv_b_le {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) : ‖1 - z‖ + ‖z‖ ≤ 1 + 2 * r := by
  have := norm_sub_le (1 : ℂ) z
  rw [norm_one] at this
  linarith

/-- `(‖1-z‖ + ‖z‖)^k ≤ e^{2rk}` for `‖z‖ ≤ r`. -/
theorem surv_b_pow_le {z : ℂ} {r : ℝ} (hz : ‖z‖ ≤ r) (k : ℕ) :
    (‖1 - z‖ + ‖z‖) ^ k ≤ Real.exp (2 * r * k) := by
  have h1 : ‖1 - z‖ + ‖z‖ ≤ Real.exp (2 * r) := by
    have := Real.add_one_le_exp (2 * r)
    linarith [surv_b_le hz]
  calc (‖1 - z‖ + ‖z‖) ^ k ≤ Real.exp (2 * r) ^ k :=
        pow_le_pow_left₀ (by positivity) h1 k
    _ = Real.exp (2 * r * k) := by rw [← Real.exp_nat_mul]; ring_nf

/-! ## Row bounds from the class -/

/-- `√(2 D (2ε)) ≤ √(4D + 1) ε` for `ε ≥ 1`. -/
theorem surv_sqrt_le {D eps : ℝ} (hD : 0 ≤ D) (heps : 1 ≤ eps) :
    Real.sqrt (2 * D * (2 * eps)) ≤ Real.sqrt (4 * D + 1) * eps := by
  have heps0 : 0 ≤ eps := by linarith
  have hDe : 0 ≤ D * eps * (eps - 1) := mul_nonneg (mul_nonneg hD heps0) (by linarith)
  calc Real.sqrt (2 * D * (2 * eps)) ≤ Real.sqrt ((4 * D + 1) * eps ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg eps])
    _ = Real.sqrt (4 * D + 1) * eps := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq heps0]

/-- `√(2 D (10ε)) ≤ √(20D + 1) ε` for `ε ≥ 1`. -/
theorem surv_sqrt_le' {D eps : ℝ} (hD : 0 ≤ D) (heps : 1 ≤ eps) :
    Real.sqrt (2 * D * (10 * eps)) ≤ Real.sqrt (20 * D + 1) * eps := by
  have heps0 : 0 ≤ eps := by linarith
  have hDe : 0 ≤ D * eps * (eps - 1) := mul_nonneg (mul_nonneg hD heps0) (by linarith)
  calc Real.sqrt (2 * D * (10 * eps)) ≤ Real.sqrt ((20 * D + 1) * eps ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg eps])
    _ = Real.sqrt (20 * D + 1) * eps := by
        rw [Real.sqrt_mul (by linarith), Real.sqrt_sq heps0]

theorem surv_kRow_zero {J : Set ℝ} (ν σ : Measure ℝ) (z : ℂ) (β a : ℝ) {φ : ℝ → ℂ}
    (hφ : ∀ y, ‖φ y‖ ≤ 1) (y : ℝ) : ‖kRow J ν σ z β a 0 φ y‖ ≤ 1 := by
  show ‖J.indicator φ y‖ ≤ 1
  exact (norm_indicator_le_norm_self _ _).trans (hφ y)

/-- **Row bounds on `J = [0, 2ε]` from the class bound**: `‖kRow J ν σ z β a n φ y‖ ≤ K₁ ε qⁿ`,
`q = e^{-8γ'}`, `K₁ = 3 √(4D+1) e^{c₁/8} + 1`. -/
theorem surv_rowBound {D c₁ eps γ' : ℝ} (hD : 0 < D) (hc₁ : 0 < c₁) (heps : 1 ≤ eps)
    (hγ0 : 0 < γ') (hγ1 : 8 * γ' ≤ 1) (hq : 8 * γ' ≤ c₁ / (8 * eps ^ 2)) (ν σ : ProbabilityMeasure ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1 / 3)
    (hcls : ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ |a| → ∀ φ : ℝ → ℂ, Measurable φ →
      (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
          3 * Real.sqrt (2 * D * w) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * w ^ 2))) + ‖z‖ ^ n) :
    ∀ β a' : ℝ, 1 / 2 ≤ |a'| → ∀ n : ℕ, ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ∀ y, ‖kRow (surv_J eps) ν σ z β a' n φ y‖ ≤
        (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) * eps * Real.exp (-(8 * γ')) ^ n := by
  intro β a' ha' n φ hφ hφ1 y
  have heps0 : 0 < eps := by linarith
  have hK1 : 1 ≤ 3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1 := by
    have : 0 ≤ 3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) := by positivity
    linarith
  have hq0 : 0 < Real.exp (-(8 * γ')) := Real.exp_pos _
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [pow_zero, mul_one]
    calc ‖kRow (surv_J eps) ν σ z β a' 0 φ y‖ ≤ 1 := surv_kRow_zero _ _ z β a' hφ1 y
      _ ≤ (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) * eps := by nlinarith
  have h := hcls 0 (2 * eps) β a' (by linarith) ha' φ hφ hφ1 n hn y
  rw [zero_add] at h
  refine h.trans ?_
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  -- the exponential factor
  have hexp : Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * (2 * eps) ^ 2))) ≤
      Real.exp (c₁ / 8) * Real.exp (-(8 * γ')) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have e : c₁ * ((n : ℝ) - 1) / (2 * (2 * eps) ^ 2) = c₁ / (8 * eps ^ 2) * ((n : ℝ) - 1) := by
      field_simp
      ring
    rw [e]
    have hu : c₁ / (8 * eps ^ 2) ≤ c₁ / 8 := by
      apply div_le_div_of_nonneg_left hc₁.le (by norm_num)
      nlinarith
    have hun := mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg n)
    nlinarith
  -- the `‖z‖ⁿ` factor
  have hz' : ‖z‖ ^ n ≤ Real.exp (-(8 * γ')) ^ n :=
    pow_le_pow_left₀ (norm_nonneg _) (hz.trans (surv_third_le_exp_neg hγ1)) n
  have hsq := surv_sqrt_le hD.le heps
  have hqn : 0 ≤ Real.exp (-(8 * γ')) ^ n := pow_nonneg hq0.le n
  calc 3 * Real.sqrt (2 * D * (2 * eps)) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * (2 * eps) ^ 2))) +
        ‖z‖ ^ n
      ≤ 3 * (Real.sqrt (4 * D + 1) * eps) * (Real.exp (c₁ / 8) * Real.exp (-(8 * γ')) ^ n) +
        Real.exp (-(8 * γ')) ^ n := by
        gcongr
    _ ≤ 3 * (Real.sqrt (4 * D + 1) * eps) * (Real.exp (c₁ / 8) * Real.exp (-(8 * γ')) ^ n) +
        eps * Real.exp (-(8 * γ')) ^ n := by
        gcongr
        exact le_mul_of_one_le_left hqn heps
    _ = (3 * Real.sqrt (4 * D + 1) * Real.exp (c₁ / 8) + 1) * eps * Real.exp (-(8 * γ')) ^ n := by
        ring

/-- **The free row bound** on `J' = [-ε, 9ε]` at `(β, a) = (0, -1)`: `≤ (3 √(20D+1) + 1) ε`. -/
theorem surv_rowBound_free {D c₁ eps : ℝ} (hD : 0 < D) (heps : 1 ≤ eps)
    (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1 / 3)
    (hcls : ∀ α w β a : ℝ, 1 ≤ w → 1 / 2 ≤ |a| → ∀ φ : ℝ → ℂ, Measurable φ →
      (∀ y, ‖φ y‖ ≤ 1) → ∀ n : ℕ, 1 ≤ n → ∀ y : ℝ,
        ‖kRow (Icc α (α + w)) ν σ z β a n φ y‖ ≤
          3 * Real.sqrt (2 * D * w) * Real.exp (-(c₁ * ((n : ℝ) - 1) / (2 * w ^ 2))) + ‖z‖ ^ n)
    (hc₁ : 0 ≤ c₁) {k : ℕ} (hk : 1 ≤ k) :
    ∀ φ : ℝ → ℂ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      ‖kRow (Icc (-eps) (9 * eps)) ν σ z 0 (-1) k φ 0‖ ≤ (3 * Real.sqrt (20 * D + 1) + 1) * eps := by
  intro φ hφ hφ1
  have heps0 : 0 < eps := by linarith
  have h := hcls (-eps) (10 * eps) 0 (-1) (by linarith) (by rw [abs_neg, abs_one]; norm_num) φ hφ hφ1
    k hk 0
  rw [show -eps + 10 * eps = 9 * eps by ring] at h
  refine h.trans ?_
  have hnr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hexp : Real.exp (-(c₁ * ((k : ℝ) - 1) / (2 * (10 * eps) ^ 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c₁ * ((k : ℝ) - 1) / (2 * (10 * eps) ^ 2) := by
      apply div_nonneg
      · exact mul_nonneg hc₁ (by linarith)
      · positivity
    linarith
  have hz' : ‖z‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (by linarith)
  have hsq := surv_sqrt_le' hD.le heps
  calc 3 * Real.sqrt (2 * D * (10 * eps)) * Real.exp (-(c₁ * ((k : ℝ) - 1) / (2 * (10 * eps) ^ 2))) +
        ‖z‖ ^ k
      ≤ 3 * (Real.sqrt (20 * D + 1) * eps) * 1 + 1 := by gcongr
    _ ≤ (3 * Real.sqrt (20 * D + 1) + 1) * eps := by nlinarith

/-! ## The good-slope bound of one certificate -/

/-- The inner middle sum: `∑_{m<L} ‖1-z‖ ‖z‖^{L-1-m} (3(L-2ε)/2) D K₁ ε q^m + ‖z‖^L ≤
(3eDK₁ + 1)(k+1)² ε q^L`. -/
theorem surv_inner_le {eps γ' D K₁ : ℝ} (heps : 1 ≤ eps) (hγ0 : 0 < γ') (hγ1 : 8 * γ' ≤ 1)
    (hD : 0 < D) (hK₁ : 1 ≤ K₁) {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) {k L : ℕ} (hLk : L ≤ k)
    (hL : 2 * eps < L) :
    ∑ m ∈ Finset.range L, ‖1 - z‖ * ‖z‖ ^ (L - 1 - m) *
        (3 * ((L : ℝ) - 2 * eps) / 2 * (D * (K₁ * eps * Real.exp (-(8 * γ')) ^ m))) +
      ‖z‖ ^ L ≤
      (3 * Real.exp 1 * D * K₁ + 1) * ((k : ℝ) + 1) ^ 2 * eps * Real.exp (-(8 * γ')) ^ L := by
  set q := Real.exp (-(8 * γ')) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hzq : ‖z‖ ≤ q := hz.trans (surv_third_le_exp_neg hγ1)
  have heq : 1 ≤ Real.exp 1 * q := by
    rw [hqdef, ← Real.exp_add]
    exact Real.one_le_exp (by linarith)
  have heps0 : 0 < eps := by linarith
  have hL1 : 1 ≤ L := by
    have : (0 : ℝ) < L := by linarith
    exact_mod_cast this
  have hLr : (L : ℝ) ≤ k := by exact_mod_cast hLk
  have hkr : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  -- each term
  have hterm : ∀ m ∈ Finset.range L, ‖1 - z‖ * ‖z‖ ^ (L - 1 - m) *
      (3 * ((L : ℝ) - 2 * eps) / 2 * (D * (K₁ * eps * q ^ m))) ≤
        3 * Real.exp 1 * D * K₁ * k * eps * q ^ L := by
    intro m hm
    have hm' := Finset.mem_range.1 hm
    have h1 : ‖1 - z‖ ≤ 2 := surv_norm_one_sub_le hz
    have h2 : ‖z‖ ^ (L - 1 - m) ≤ q ^ (L - 1 - m) := pow_le_pow_left₀ (norm_nonneg _) hzq _
    have h3 : 3 * ((L : ℝ) - 2 * eps) / 2 ≤ 3 * k / 2 := by linarith
    have h3' : 0 ≤ 3 * ((L : ℝ) - 2 * eps) / 2 := by linarith
    have hqm : q ^ (L - 1 - m) * q ^ m = q ^ (L - 1) := by
      rw [← pow_add, show L - 1 - m + m = L - 1 by omega]
    have hqL : q ^ (L - 1) ≤ Real.exp 1 * q ^ L := by
      have e : q ^ L = q ^ (L - 1) * q := by
        rw [← pow_succ, show L - 1 + 1 = L by omega]
      rw [e]
      calc q ^ (L - 1) = q ^ (L - 1) * 1 := (mul_one _).symm
        _ ≤ q ^ (L - 1) * (Real.exp 1 * q) :=
          mul_le_mul_of_nonneg_left heq (pow_nonneg hq0.le _)
        _ = Real.exp 1 * (q ^ (L - 1) * q) := by ring
    calc ‖1 - z‖ * ‖z‖ ^ (L - 1 - m) * (3 * ((L : ℝ) - 2 * eps) / 2 * (D * (K₁ * eps * q ^ m)))
        ≤ 2 * q ^ (L - 1 - m) * (3 * k / 2 * (D * (K₁ * eps * q ^ m))) := by
          gcongr
      _ = 3 * D * K₁ * k * eps * (q ^ (L - 1 - m) * q ^ m) := by ring
      _ = 3 * D * K₁ * k * eps * q ^ (L - 1) := by rw [hqm]
      _ ≤ 3 * D * K₁ * k * eps * (Real.exp 1 * q ^ L) := by
          gcongr
      _ = 3 * Real.exp 1 * D * K₁ * k * eps * q ^ L := by ring
  have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hzL : ‖z‖ ^ L ≤ q ^ L := pow_le_pow_left₀ (norm_nonneg _) hzq L
  have hqL0 : 0 ≤ q ^ L := pow_nonneg hq0.le L
  have hk2 : (k : ℝ) * k ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
  have hone : 1 ≤ ((k : ℝ) + 1) ^ 2 * eps := by nlinarith
  calc _ ≤ (L : ℝ) * (3 * Real.exp 1 * D * K₁ * k * eps * q ^ L) + q ^ L := add_le_add hsum hzL
    _ ≤ (k : ℝ) * (3 * Real.exp 1 * D * K₁ * k * eps * q ^ L) + q ^ L := by gcongr
    _ = 3 * Real.exp 1 * D * K₁ * ((k : ℝ) * k) * eps * q ^ L + q ^ L := by ring
    _ ≤ 3 * Real.exp 1 * D * K₁ * ((k : ℝ) + 1) ^ 2 * eps * q ^ L +
        ((k : ℝ) + 1) ^ 2 * eps * q ^ L := by
        gcongr
        exact le_mul_of_one_le_left hqL0 hone
    _ = (3 * Real.exp 1 * D * K₁ + 1) * ((k : ℝ) + 1) ^ 2 * eps * q ^ L := by ring

/-- `E q^k ≤ e^{1/2} e^{-6γ'k}` with `E = e^{2γ'(k+2ε)}`, `q = e^{-8γ'}`, `4γ'ε ≤ 1/2`. -/
theorem surv_Eq_le {eps γ' : ℝ} (hγε : 4 * γ' * eps ≤ 1 / 2) (k : ℕ) :
    Real.exp (γ' * (2 * (k + 2 * eps))) * Real.exp (-(8 * γ')) ^ k ≤
      Real.exp (1 / 2) * Real.exp (-(6 * γ' * k)) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

/-- **The good-slope bound of one certificate** in the class constants. -/
theorem surv_goodB_le {eps γ' D K₁ : ℝ} (heps : 1 ≤ eps) (hγ0 : 0 < γ') (hγε : 4 * γ' * eps ≤ 1 / 2)
    (hD : 0 < D) (hK₁ : 1 ≤ K₁) {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) {k i j : ℕ} (hij : i < j) (hjk : j ≤ k)
    (hL : 2 * eps < (j : ℝ) - i) :
    surv_goodB eps z D (Real.exp (γ' * (2 * (k + 2 * eps))))
        (fun n => K₁ * eps * Real.exp (-(8 * γ')) ^ n) k i j ≤
      K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * Real.exp (1 / 2) * ((k : ℝ) + 1) ^ 2 * eps ^ 3 *
        Real.exp (-(6 * γ' * k)) := by
  have hγ1 : 8 * γ' ≤ 1 := by nlinarith
  have heps0 : 0 < eps := by linarith
  set q := Real.exp (-(8 * γ')) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  set E := Real.exp (γ' * (2 * (k + 2 * eps))) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  have hLk : j - i ≤ k := by omega
  have hLr : 2 * eps < ((j - i : ℕ) : ℝ) := by rw [Nat.cast_sub hij.le]; exact hL
  have hinner := surv_inner_le heps hγ0 hγ1 hD hK₁ hz hLk hLr
  unfold surv_goodB
  have hpow : q ^ (k - j) * q ^ i * q ^ (j - i) = q ^ k := by
    rw [← pow_add, ← pow_add, show k - j + i + (j - i) = k by omega]
  have hEq := surv_Eq_le hγε k
  have hKq : 0 ≤ E * (K₁ * eps * q ^ (k - j)) * (K₁ * eps * q ^ i) := by positivity
  calc E * (K₁ * eps * q ^ (k - j)) * (K₁ * eps * q ^ i) *
        (∑ m ∈ Finset.range (j - i), ‖1 - z‖ * ‖z‖ ^ (j - i - 1 - m) *
          (3 * (((j - i : ℕ) : ℝ) - 2 * eps) / 2 * (D * (K₁ * eps * q ^ m))) + ‖z‖ ^ (j - i))
      ≤ E * (K₁ * eps * q ^ (k - j)) * (K₁ * eps * q ^ i) *
        ((3 * Real.exp 1 * D * K₁ + 1) * ((k : ℝ) + 1) ^ 2 * eps * q ^ (j - i)) :=
        mul_le_mul_of_nonneg_left hinner hKq
    _ = K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * ((k : ℝ) + 1) ^ 2 * eps ^ 3 *
        (E * (q ^ (k - j) * q ^ i * q ^ (j - i))) := by ring
    _ = K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * ((k : ℝ) + 1) ^ 2 * eps ^ 3 * (E * q ^ k) := by
        rw [hpow]
    _ ≤ K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * ((k : ℝ) + 1) ^ 2 * eps ^ 3 *
        (Real.exp (1 / 2) * Real.exp (-(6 * γ' * k))) := by
        gcongr
    _ = _ := by ring

/-- The number of certificate pairs is at most `(k+1)²`. -/
theorem surv_card_certPairs_le (eps : ℝ) (k : ℕ) : (certPairs eps k).card ≤ (k + 1) ^ 2 := by
  unfold certPairs
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_range, sq]

/-- **The sum of the good-slope bounds over all certificates.** -/
theorem surv_sum_goodB_le {eps γ' D K₁ : ℝ} (heps : 1 ≤ eps) (hγ0 : 0 < γ') (hγε : 4 * γ' * eps ≤ 1 / 2)
    (hD : 0 < D) (hK₁ : 1 ≤ K₁) {z : ℂ} (hz : ‖z‖ ≤ 1 / 3) (k : ℕ) :
    ∑ ij ∈ certPairs eps k, surv_goodB eps z D (Real.exp (γ' * (2 * (k + 2 * eps))))
        (fun n => K₁ * eps * Real.exp (-(8 * γ')) ^ n) k ij.1 ij.2 ≤
      K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * Real.exp (1 / 2) * ((k : ℝ) + 1) ^ 4 * eps ^ 3 *
        Real.exp (-(6 * γ' * k)) := by
  have h := Finset.sum_le_card_nsmul (certPairs eps k) _
    (K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * Real.exp (1 / 2) * ((k : ℝ) + 1) ^ 2 * eps ^ 3 *
      Real.exp (-(6 * γ' * k))) fun ij hij => by
        obtain ⟨h1, h2, h3⟩ := mem_certPairs.1 hij
        exact surv_goodB_le heps hγ0 hγε hD hK₁ hz h1 h2 h3
  refine h.trans ?_
  rw [nsmul_eq_mul]
  have hc : ((certPairs eps k).card : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    have := surv_card_certPairs_le eps k
    exact_mod_cast this
  have hnn : 0 ≤ K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * Real.exp (1 / 2) * ((k : ℝ) + 1) ^ 2 *
      eps ^ 3 * Real.exp (-(6 * γ' * k)) := by
    have : (0 : ℝ) ≤ eps := by linarith
    positivity
  calc _ ≤ ((k : ℝ) + 1) ^ 2 * (K₁ ^ 2 * (3 * Real.exp 1 * D * K₁ + 1) * Real.exp (1 / 2) *
        ((k : ℝ) + 1) ^ 2 * eps ^ 3 * Real.exp (-(6 * γ' * k))) :=
        mul_le_mul_of_nonneg_right hc hnn
    _ = _ := by ring

/-! ## Series -/

/-- `∑_k e^{-βk} ≤ 1 + 1/β` for `β > 0`. -/
theorem surv_tsum_exp_neg {β : ℝ} (hβ : 0 < β) :
    Summable (fun k : ℕ => Real.exp (-(β * k))) ∧
      ∑' k : ℕ, Real.exp (-(β * k)) ≤ 1 + 1 / β := by
  have he : ∀ k : ℕ, Real.exp (-(β * k)) = Real.exp (-β) ^ k := fun k => by
    rw [← Real.exp_nat_mul]; ring_nf
  have hρ0 : 0 ≤ Real.exp (-β) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-β) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  simp only [he]
  refine ⟨summable_geometric_of_lt_one hρ0 hρ1, ?_⟩
  rw [tsum_geometric_of_lt_one hρ0 hρ1]
  have hρβ : Real.exp (-β) * (1 + β) ≤ 1 := by
    rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos β), mul_one]
    linarith [Real.add_one_le_exp β]
  rw [inv_le_iff_one_le_mul₀' (by linarith)]
  have e : (1 - Real.exp (-β)) * (1 + 1 / β) = 1 - Real.exp (-β) + (1 - Real.exp (-β)) / β := by
    ring
  rw [e]
  have h : Real.exp (-β) ≤ (1 - Real.exp (-β)) / β := by
    rw [le_div_iff₀ hβ]
    linarith
  linarith

/-- `(k+1)⁴ e^{-αk} ≤ 384 α⁻⁴ e^{α/2} e^{-(α/2)k}`. -/
theorem surv_poly_exp_le {α : ℝ} (hα : 0 < α) (k : ℕ) :
    ((k : ℝ) + 1) ^ 4 * Real.exp (-(α * k)) ≤
      384 * (α⁻¹) ^ 4 * Real.exp (α / 2) * Real.exp (-(α / 2 * k)) := by
  have hx : 0 ≤ α * ((k : ℝ) + 1) / 2 := by positivity
  have h := Real.pow_div_factorial_le_exp _ hx 4
  have hfac : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac] at h
  have e : ((k : ℝ) + 1) ^ 4 = 16 * (α⁻¹) ^ 4 * (α * ((k : ℝ) + 1) / 2) ^ 4 := by
    field_simp
    ring
  have h2 : ((k : ℝ) + 1) ^ 4 ≤ 384 * (α⁻¹) ^ 4 * Real.exp (α * ((k : ℝ) + 1) / 2) := by
    rw [e]
    have h' : (α * ((k : ℝ) + 1) / 2) ^ 4 ≤ 24 * Real.exp (α * ((k : ℝ) + 1) / 2) := by
      rw [div_le_iff₀ (by norm_num)] at h
      linarith
    have hα4 : 0 ≤ 16 * (α⁻¹) ^ 4 := by positivity
    calc 16 * (α⁻¹) ^ 4 * (α * ((k : ℝ) + 1) / 2) ^ 4
        ≤ 16 * (α⁻¹) ^ 4 * (24 * Real.exp (α * ((k : ℝ) + 1) / 2)) :=
          mul_le_mul_of_nonneg_left h' hα4
      _ = 384 * (α⁻¹) ^ 4 * Real.exp (α * ((k : ℝ) + 1) / 2) := by ring
  calc ((k : ℝ) + 1) ^ 4 * Real.exp (-(α * k))
      ≤ 384 * (α⁻¹) ^ 4 * Real.exp (α * ((k : ℝ) + 1) / 2) * Real.exp (-(α * k)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = 384 * (α⁻¹) ^ 4 * Real.exp (α / 2) * Real.exp (-(α / 2 * k)) := by
        rw [mul_assoc (384 * (α⁻¹) ^ 4), ← Real.exp_add, mul_assoc (384 * (α⁻¹) ^ 4),
          ← Real.exp_add]
        congr 2
        ring

/-- `∑_k (k+1)⁴ e^{-αk} ≤ 1152 e^{1/2} (α⁻¹)⁵` for `0 < α ≤ 1`. -/
theorem surv_tsum_poly {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 * Real.exp (-(α * k))) ∧
      ∑' k : ℕ, ((k : ℝ) + 1) ^ 4 * Real.exp (-(α * k)) ≤
        1152 * Real.exp (1 / 2) * (α⁻¹) ^ 5 := by
  obtain ⟨hs, hsum⟩ := surv_tsum_exp_neg (β := α / 2) (by positivity)
  have hC : 0 ≤ 384 * (α⁻¹) ^ 4 * Real.exp (α / 2) := by positivity
  have hs' : Summable fun k : ℕ => 384 * (α⁻¹) ^ 4 * Real.exp (α / 2) * Real.exp (-(α / 2 * k)) :=
    hs.mul_left _
  have hle : ∀ k : ℕ, ((k : ℝ) + 1) ^ 4 * Real.exp (-(α * k)) ≤
      384 * (α⁻¹) ^ 4 * Real.exp (α / 2) * Real.exp (-(α / 2 * k)) := surv_poly_exp_le hα
  have hnn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) ^ 4 * Real.exp (-(α * k)) := fun k => by positivity
  refine ⟨Summable.of_nonneg_of_le hnn hle hs', ?_⟩
  refine ((Summable.of_nonneg_of_le hnn hle hs').tsum_le_tsum hle hs').trans ?_
  rw [tsum_mul_left]
  have hinv : 1 ≤ α⁻¹ := one_le_inv₀ hα |>.2 hα1
  have h1 : 1 + 1 / (α / 2) ≤ 3 * α⁻¹ := by
    rw [one_div, inv_div, div_eq_mul_inv]
    linarith
  have he : Real.exp (α / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  calc 384 * (α⁻¹) ^ 4 * Real.exp (α / 2) * ∑' k : ℕ, Real.exp (-(α / 2 * k))
      ≤ 384 * (α⁻¹) ^ 4 * Real.exp (1 / 2) * (3 * α⁻¹) := by
        gcongr
        exact hsum.trans h1
    _ = 1152 * Real.exp (1 / 2) * (α⁻¹) ^ 5 := by ring

/-! ## `k = 0` -/

theorem surv_cSurv_zero_le (eps : ℝ) (ν σ : ProbabilityMeasure ℝ) (z : ℂ) (G : ℝ → ℝ) :
    ‖cSurv eps ν σ z 0 G‖ ≤ |G 0| := by
  rw [cSurv_eq]
  simp only [Finset.range_zero, Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty,
    Nat.sub_zero, pow_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold survInt
  have h := norm_integral_le_of_norm_le_const (μ := wordLaw ν σ ∅)
    (f := fun g => (survSet eps 0).indicator (fun g => G (gapKeys g 0)) g) (C := |G 0|)
    (Filter.Eventually.of_forall fun g => by
      refine (norm_indicator_le_norm_self _ _).trans ?_
      rw [gapKeys_zero, Real.norm_eq_abs])
  simpa using h

end

end PGM
