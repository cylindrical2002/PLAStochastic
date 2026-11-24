import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import Mathlib.Data.Nat.Log

/-! # Reducing all horizons to powers of sixteen

At horizon `16^k`, a leaf length `2^k` and tree depth `3k` give an exact
fourth-root partition. Enlarging an arbitrary horizon costs only a fixed
constant in the frozen strong-approximation rate.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Shortening the horizon and increasing the error or failure budget preserves a coupling. -/
theorem HasSACoupling.mono {ν : ProbabilityMeasure ℝ} {n N : ℕ} {a A p P : ℝ}
    (h : HasSACoupling ν N a p) (hn : n ≤ N) (ha : a ≤ A) (hp : p ≤ P) :
    HasSACoupling ν n A P := by
  obtain ⟨π, hπ, hleft, hright, hbad⟩ := h
  let := hπ
  refine ⟨π, hπ, hleft, hright, ?_⟩
  refine (measureReal_mono ?_).trans (hbad.trans hp)
  rintro q ⟨k, hk, herror⟩
  exact ⟨k, hk.trans hn, ha.trans_lt herror⟩

/-- A constant-factor enlargement of the horizon preserves the required rate. -/
theorem sa_rate_enlargement {n N : ℕ} (hn : 16 ≤ n) (hN : n ≤ N) (hN' : N ≤ 16 * n) :
    (N : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log N) ≤
      32 * ((n : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log n)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn16 : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hN16 : (N : ℝ) ≤ 16 * n := by exact_mod_cast hN'
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hlog : Real.log N ≤ 2 * Real.log n := by
    calc
      Real.log N ≤ Real.log (16 * n) := Real.log_le_log hN0 hN16
      _ = Real.log 16 + Real.log n := Real.log_mul (by norm_num) hn0.ne'
      _ ≤ 2 * Real.log n := by linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 16) hn16]
  have hsqrt : Real.sqrt (Real.log N) ≤ 2 * Real.sqrt (Real.log n) := by
    apply Real.sqrt_le_iff.2
    constructor
    · positivity
    · have hln := Real.log_nonneg hn1
      nlinarith [Real.sq_sqrt hln]
  have hpow : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ 16 * (n : ℝ) ^ ((1 : ℝ) / 8) := by
    calc
      _ ≤ (16 * (n : ℝ)) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow hN0.le hN16 (by norm_num)
      _ = (16 : ℝ) ^ ((1 : ℝ) / 8) * (n : ℝ) ^ ((1 : ℝ) / 8) :=
        Real.mul_rpow (by norm_num) hn0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)) (by positivity)
  calc
    _ ≤ (16 * (n : ℝ) ^ ((1 : ℝ) / 8)) * (2 * Real.sqrt (Real.log n)) :=
      mul_le_mul hpow hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

/-- It suffices to construct class-uniform couplings at fourth-power dyadic horizons. -/
theorem strongApproxClass_of_pow_sixteen (vlo vhi κ₃ B θ D c₀ : ℝ)
    (h : ∃ K : ℝ, ∃ k₀ : ℕ, 0 ≤ K ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c₀ ν →
        ∀ k : ℕ, k₀ ≤ k →
          HasSACoupling ν (16 ^ k)
            (K * ((16 ^ k : ℕ) : ℝ) ^ ((1 : ℝ) / 8) * Real.sqrt (Real.log (16 ^ k : ℕ)))
            (((16 ^ k : ℕ) : ℝ) ^ (-(2 : ℝ)))) :
    StrongApproxClass vlo vhi κ₃ B θ D c₀ := by
  obtain ⟨K, k₀, hK, hcouple⟩ := h
  refine ⟨32 * K, max 16 (16 ^ k₀), by positivity, le_max_left _ _, ?_⟩
  intro ν hν hsm n hn
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hnbase : 16 ^ k₀ ≤ n := (le_max_right _ _).trans hn
  have hn0 : n ≠ 0 := by omega
  let k := Nat.log 16 n + 1
  have hk : k₀ ≤ k := (Nat.le_log_of_pow_le (by norm_num) hnbase).trans (Nat.le_succ _)
  have hN : n ≤ 16 ^ k := (Nat.lt_pow_succ_log_self (by norm_num : 1 < 16) n).le
  have hN' : 16 ^ k ≤ 16 * n := by
    dsimp [k]
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left 16 (Nat.pow_log_le_self 16 hn0)
  apply (hcouple ν hν hsm k hk).mono hN
  · have he := mul_le_mul_of_nonneg_left (sa_rate_enlargement hn16 hN hN') hK
    nlinarith [he]
  · exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hN) (by norm_num)

end

end PGM
