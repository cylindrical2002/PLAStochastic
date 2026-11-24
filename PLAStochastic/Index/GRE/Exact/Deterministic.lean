import PLAStochastic.Index.Algorithm.RankHeightRecursion
import PLAStochastic.Index.Algorithm.GreedyMinimality

/-!
# The exact ALG-RE height from per-layer count brackets

Deterministic part of `thm:GRE` (`research/2026-09-24-height-precision-ceiling/tex/main.tex`).
Write `N_ℓ = reSize`, `Δ_ℓ = reDelta`, `M_{ℓ+1} = reSegs`, `mbar_ℓ = N_ℓ / (Δ_ℓ A)` (`reMbar`)
and `H = reHeight`.  The count bracket `a mbar_ℓ - t ≤ M_{ℓ+1} ≤ B mbar_ℓ + t` holds on every
layer, with `0 < a ≤ 1 ≤ B`, `1 ≤ t`, `4 B < A` and `τ = 4 t / a`.

* Step 1 (`reSize_succ_eq_one_of_tube`): a layer whose keys stay in a tube of rank width `eps`
  around a line is one segment, so the next layer is a single key.  The hypothesis `hone` of
  the main theorem is this statement for all layers with `N_ℓ ≤ θ`.
* Steps 2–3: `L = reCutoff` is the first layer with `mbar_L < τ`.  Before `L` the spacing obeys
  `A / (4 B) Δ² ≤ Δ' ≤ (2 / a) A Δ²`, so `L < H`, and `L` is located from both sides by the
  sharp conditions `(2^(ℓ+1) - 1) log ((2 / a) A) ≤ log n - log τ` (`lt_reCutoff_of_log`) and
  `log n ≤ (2^(ℓ+1) - 1) log (A / (4 B))` (`reCutoff_le_of_log`).
* Step 4: `H ≤ L + 2`, and `H ≤ L + 1` once `N_L ≤ θ`, which holds when
  `log (2 n / θ) ≤ (2^L - 1) log (A / (4 B))`.
* Step 5 (`reHeight_window_of_bracket`): the three conditions, in `log₂` form, turn into the
  window `y - w < H ≤ y + 1 + w` and `H = ⌈y⌉` at distance `≥ w` from `ℤ`, for any `y ≥ 0`
  and `w > 0` that dominate the three `log₂` thresholds.

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

open Finset

/-! ## Step 1: a small layer is one segment -/

/-- If all `K ≥ 1` keys are feasible together, ALG-OPT uses one segment. -/
private theorem finSegCount_eq_one_of_feasible {eps : ℝ} {p : ℕ → ℝ} {K : ℕ} (hK : 1 ≤ K)
    (h : prefixAffineFeasible eps p K) : finSegCount eps p K = 1 := by
  refine le_antisymm ?_ (one_le_finSegCount p hK)
  have hc := finSegCount_le_ceilDiv_of_short (eps := eps) (p := p) (K := K) hK
    (fun a len hlen _ => prefixAffineFeasible_window (r := a) (w := len) h hlen)
  have h1 : K ⌈/⌉ K = 1 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  omega

/-- **Step 1.**  If the keys of layer `ℓ` stay within `μ Δ_ℓ eps` of the line `x0 + μ s`
(in input rank `s`), the whole layer is one segment and layer `ℓ + 1` is a single key. -/
theorem reSize_succ_eq_one_of_tube {eps μ x0 : ℝ} {p : ℕ → ℝ} {n ℓ : ℕ} (heps : 1 ≤ eps)
    (hn : 1 ≤ n) (hμ : 0 < μ)
    (h : ∀ j < reSize eps p n ℓ, |p (j * reDelta eps p n ℓ) - x0 -
      μ * ((j * reDelta eps p n ℓ : ℕ) : ℝ)| ≤ μ * reDelta eps p n ℓ * eps) :
    reSize eps p n (ℓ + 1) = 1 := by
  have hΔ : (0 : ℝ) < reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  have hN : 1 ≤ reSize eps p n ℓ := one_le_reSize heps hn ℓ
  have hμΔ : 0 < μ * reDelta eps p n ℓ := mul_pos hμ hΔ
  have hM : reSegs eps p n ℓ = 1 := by
    rw [reSegs]
    apply finSegCount_eq_one_of_feasible hN
    refine prefixAffineFeasible_of_line (1 / (μ * reDelta eps p n ℓ))
      (-(x0 / (μ * reDelta eps p n ℓ))) fun j hj => ?_
    have hj' := h j hj
    have heq : (j : ℝ) - (1 / (μ * reDelta eps p n ℓ) * p (j * reDelta eps p n ℓ) +
        -(x0 / (μ * reDelta eps p n ℓ))) =
        -((p (j * reDelta eps p n ℓ) - x0 - μ * ((j * reDelta eps p n ℓ : ℕ) : ℝ)) /
          (μ * reDelta eps p n ℓ)) := by
      push_cast
      field_simp
      ring
    rw [heq, abs_neg, abs_div, abs_of_pos hμΔ, div_le_iff₀ hμΔ]
    linarith
  rw [reSize_succ, reStep, hM, Nat.div_one, Nat.ceilDiv_eq_add_pred_div]
  exact Nat.div_eq_of_lt_le (by omega) (by omega)

/-! ## The first cutoff -/

/-- The first layer with `mbar_ℓ < τ` (TeX `L`). -/
def reCutoff (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) (A τ : ℝ) : ℕ :=
  sInf {ℓ | reMbar eps p n A ℓ < τ}

section Cutoff

variable {eps : ℝ} {p : ℕ → ℝ} {n : ℕ} {A a B t : ℝ}

theorem reCutoff_spec (heps : 1 ≤ eps) (hn : 1 ≤ n) (hA : 1 ≤ A) {τ : ℝ} (hτ : 1 < τ) :
    reMbar eps p n A (reCutoff eps p n A τ) < τ ∧
      ∀ ℓ < reCutoff eps p n A τ, τ ≤ reMbar eps p n A ℓ := by
  have hne : reHeight eps p n ∈ {ℓ | reMbar eps p n A ℓ < τ} := by
    have := reMbar_le_one_of_reSize_eq_one heps hn hA (reSize_reHeight (p := p) heps hn)
    show _ < τ
    linarith
  exact ⟨Nat.sInf_mem ⟨_, hne⟩, fun ℓ hℓ => not_lt.1 (Nat.notMem_of_lt_sInf hℓ)⟩

private theorem one_lt_tau (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) : 1 < 4 * t / a := by
  rw [lt_div_iff₀ ha]; linarith

private theorem one_le_of_bracket (hB : 1 ≤ B) (hBA : 4 * B < A) : 1 ≤ A := by linarith

variable (heps : 1 ≤ eps) (hn : 1 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B) (ht : 1 ≤ t)
  (hBA : 4 * B < A)
  (hM : ∀ ℓ, a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ ∧
    (reSegs eps p n ℓ : ℝ) ≤ B * reMbar eps p n A ℓ + t)
include heps hn ha ha1 hB ht hBA hM

/-- Steps 2–3, `eq:GREiter`: `(A / (4 B))^(2^ℓ - 1) ≤ Δ_ℓ ≤ ((2 / a) A)^(2^ℓ - 1)` for
`ℓ ≤ L`. -/
theorem reDelta_bounds_of_le_reCutoff {ℓ : ℕ} (hℓ : ℓ ≤ reCutoff eps p n A (4 * t / a)) :
    (1 / (4 * B) * A) ^ (2 ^ ℓ - 1) ≤ (reDelta eps p n ℓ : ℝ) ∧
      (reDelta eps p n ℓ : ℝ) ≤ (2 / a * A) ^ (2 ^ ℓ - 1) := by
  have hA := one_le_of_bracket hB hBA
  obtain ⟨-, hbefore⟩ := reCutoff_spec (p := p) heps hn hA (one_lt_tau ha ha1 ht)
  have hB0 : 0 < B := by linarith
  have hlo : ∀ j, j < reCutoff eps p n A (4 * t / a) →
      1 / (4 * B) * A * (reDelta eps p n j : ℝ) ^ 2 ≤ reDelta eps p n (j + 1) := fun j hj => by
    have := re_compress_lower heps hn ha ha1 hB ht hBA.le (hM j).2 (hbefore j hj)
    calc 1 / (4 * B) * A * (reDelta eps p n j : ℝ) ^ 2 =
        A / (4 * B) * (reDelta eps p n j : ℝ) ^ 2 := by ring
      _ ≤ _ := this
  have hup : ∀ j, j < reCutoff eps p n A (4 * t / a) →
      (reDelta eps p n (j + 1) : ℝ) ≤ 2 / a * A * (reDelta eps p n j : ℝ) ^ 2 := fun j hj =>
    (re_compress_upper heps hn ha ht hA (hM j).1 (hbefore j hj)).1
  have h0 : ((reDelta eps p n 0 : ℕ) : ℝ) = 1 := by simp
  exact ⟨dexp_lower (Δ := fun j => (reDelta eps p n j : ℝ)) (by positivity) h0 hlo ℓ hℓ,
    dexp_upper (Δ := fun j => (reDelta eps p n j : ℝ)) (by positivity) (by positivity) h0 hlo
      hup ℓ hℓ⟩

/-- Step 2: `L < H`, since every layer `1 ≤ ℓ ≤ L` has at least two keys. -/
theorem reCutoff_lt_reHeight : reCutoff eps p n A (4 * t / a) < reHeight eps p n := by
  have hA := one_le_of_bracket hB hBA
  obtain ⟨-, hbefore⟩ := reCutoff_spec (p := p) heps hn hA (one_lt_tau ha ha1 ht)
  rcases Nat.eq_zero_or_pos (reCutoff eps p n A (4 * t / a)) with h0 | hpos
  · rw [h0]; exact one_le_reHeight heps hn
  · obtain ⟨j, hj⟩ : ∃ j, reCutoff eps p n A (4 * t / a) = j + 1 :=
      ⟨reCutoff eps p n A (4 * t / a) - 1, by omega⟩
    have h2 := (re_compress_upper heps hn ha ht hA (hM j).1 (hbefore j (by omega))).2.2
    rw [hj]
    exact (lt_reHeight_iff heps hn (by omega)).2 h2

/-- Step 3, lower side: under `(2^(ℓ+1) - 1) log ((2 / a) A) ≤ log n - log τ`, `ℓ < L`. -/
theorem lt_reCutoff_of_log {ℓ : ℕ}
    (hcond : ((2 : ℝ) ^ (ℓ + 1) - 1) * Real.log (2 / a * A) ≤
      Real.log n - Real.log (4 * t / a)) :
    ℓ < reCutoff eps p n A (4 * t / a) := by
  have hA := one_le_of_bracket hB hBA
  have hτ := one_lt_tau ha ha1 ht
  obtain ⟨hL, -⟩ := reCutoff_spec (p := p) heps hn hA hτ
  have hb : 1 ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  have hbA : 1 ≤ 2 / a * A := one_le_mul_of_one_le_of_one_le hb hA
  have hlbA : 0 ≤ Real.log (2 / a * A) := Real.log_nonneg hbA
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  -- every `j ≤ ℓ` with `j ≤ L` is below `L`
  have key : ∀ j, j ≤ ℓ → j ≤ reCutoff eps p n A (4 * t / a) →
      j < reCutoff eps p n A (4 * t / a) := by
    intro j hjℓ hjL
    refine lt_of_le_of_ne hjL fun hjeq => ?_
    have hΔu := (reDelta_bounds_of_le_reCutoff heps hn ha ha1 hB ht hBA hM hjL).2
    have hΔ1 : (1 : ℝ) ≤ reDelta eps p n j := by exact_mod_cast one_le_reDelta heps hn j
    have hpow : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have hlogΔ : Real.log (reDelta eps p n j) ≤ ((2 : ℝ) ^ j - 1) * Real.log (2 / a * A) := by
      have := Real.log_le_log (by linarith) hΔu
      rw [Real.log_pow, Nat.cast_sub hpow] at this
      push_cast at this
      exact this
    have hlogA : Real.log A ≤ Real.log (2 / a * A) :=
      Real.log_le_log (by linarith) (le_mul_of_one_le_left (by linarith) hb)
    have h2j : (2 : ℝ) ^ (j + 1) ≤ 2 ^ (ℓ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hcondj : ((2 : ℝ) ^ (j + 1) - 1) * Real.log (2 / a * A) ≤
        Real.log n - Real.log (4 * t / a) :=
      le_trans (mul_le_mul_of_nonneg_right (by linarith) hlbA) hcond
    -- `A Δ² τ ≤ n`
    have hprod : A * (reDelta eps p n j : ℝ) ^ 2 * (4 * t / a) ≤ n := by
      rw [← Real.log_le_log_iff (by positivity) hnpos, Real.log_mul (by positivity)
        (by linarith), Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have : ((2 : ℝ) ^ (j + 1) - 1) = 1 + 2 * ((2 : ℝ) ^ j - 1) := by rw [pow_succ]; ring
      rw [this] at hcondj
      push_cast
      nlinarith
    have hcov : (n : ℝ) ≤ (reSize eps p n j : ℝ) * reDelta eps p n j := by
      exact_mod_cast (re_cover (p := p) heps hn j).2
    have hge : 4 * t / a ≤ reMbar eps p n A j := by
      unfold reMbar
      rw [le_div_iff₀ (by positivity)]
      have h3 : 4 * t / a * ((reDelta eps p n j : ℝ) * A) * reDelta eps p n j ≤
          (reSize eps p n j : ℝ) * reDelta eps p n j := by nlinarith
      exact le_of_mul_le_mul_right h3 (by linarith)
    rw [hjeq] at hge
    linarith
  induction ℓ with
  | zero => exact key 0 le_rfl (Nat.zero_le _)
  | succ ℓ ih =>
    have hcond' : ((2 : ℝ) ^ (ℓ + 1) - 1) * Real.log (2 / a * A) ≤
        Real.log n - Real.log (4 * t / a) := by
      have h2 : (2 : ℝ) ^ (ℓ + 1) ≤ 2 ^ (ℓ + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hlbA) hcond
    have hlt := ih hcond' fun j hj hjL => key j (by omega) hjL
    exact key (ℓ + 1) le_rfl hlt

/-- Step 3, upper side: under `log n ≤ (2^(ℓ+1) - 1) log (A / (4 B))`, `L ≤ ℓ`. -/
theorem reCutoff_le_of_log {ℓ : ℕ}
    (hcond : Real.log n ≤ ((2 : ℝ) ^ (ℓ + 1) - 1) * Real.log (A / (4 * B))) :
    reCutoff eps p n A (4 * t / a) ≤ ℓ := by
  have hA := one_le_of_bracket hB hBA
  obtain ⟨-, hbefore⟩ := reCutoff_spec (p := p) heps hn hA (one_lt_tau ha ha1 ht)
  by_contra hlt
  push Not at hlt
  have hge := hbefore ℓ hlt
  have hΔl := (reDelta_bounds_of_le_reCutoff heps hn ha ha1 hB ht hBA hM hlt.le).1
  have hB0 : 0 < B := by linarith
  have hq1 : 1 < A / (4 * B) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hqA : A / (4 * B) ≤ A := div_le_self (by linarith) (by linarith)
  have hΔ1 : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have hq : 1 / (4 * B) * A = A / (4 * B) := by ring
  rw [hq] at hΔl
  -- `n ≤ A Δ²`
  have hnA : (n : ℝ) ≤ A * (reDelta eps p n ℓ : ℝ) ^ 2 := by
    rw [← Real.log_le_log_iff hnpos (by positivity), Real.log_mul (by linarith) (by positivity),
      Real.log_pow]
    have h1 := Real.log_le_log (by positivity) hΔl
    rw [Real.log_pow, Nat.cast_sub hpow] at h1
    push_cast at h1
    have h2 := Real.log_le_log (by linarith) hqA
    have : ((2 : ℝ) ^ (ℓ + 1) - 1) = 1 + 2 * ((2 : ℝ) ^ ℓ - 1) := by rw [pow_succ]; ring
    rw [this] at hcond
    push_cast
    nlinarith
  -- `N Δ < n + Δ`
  have hcov : ((reSize eps p n ℓ : ℝ) - 1) * reDelta eps p n ℓ < n := by
    have h := (re_cover (p := p) heps hn ℓ).1
    have h1 := one_le_reSize (p := p) heps hn ℓ
    have : (((reSize eps p n ℓ - 1 : ℕ) : ℝ)) = (reSize eps p n ℓ : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; simp
    rw [← this]
    exact_mod_cast h
  have hlt2 : reMbar eps p n A ℓ < 2 := by
    unfold reMbar
    rw [div_lt_iff₀ (by positivity)]
    have hAΔ : (1 : ℝ) ≤ A * reDelta eps p n ℓ := by nlinarith
    have h3 : (reSize eps p n ℓ : ℝ) * reDelta eps p n ℓ <
        2 * ((reDelta eps p n ℓ : ℝ) * A) * reDelta eps p n ℓ := by nlinarith
    exact lt_of_mul_lt_mul_right h3 (by linarith)
  have h4 : (4 : ℝ) ≤ 4 * t / a := by rw [le_div_iff₀ ha]; nlinarith
  linarith

/-- Step 4, second alternative: `H ≤ L + 2`, since `N_{L+1} ≤ 2 (B τ + t) ≤ θ`. -/
theorem reHeight_le_reCutoff_add_two {θ : ℝ}
    (hone : ∀ ℓ, (reSize eps p n ℓ : ℝ) ≤ θ → reSize eps p n (ℓ + 1) = 1)
    (hθ : 2 * (B * (4 * t / a) + t) ≤ θ) :
    reHeight eps p n ≤ reCutoff eps p n A (4 * t / a) + 2 := by
  have hA := one_le_of_bracket hB hBA
  obtain ⟨hL, -⟩ := reCutoff_spec (p := p) heps hn hA (one_lt_tau ha ha1 ht)
  set L := reCutoff eps p n A (4 * t / a)
  have hML := (hM L).2
  have hB0 : 0 < B := by linarith
  have hN : (reSize eps p n (L + 1) : ℝ) ≤ 2 * reSegs eps p n L := by
    exact_mod_cast (reSize_succ_bounds heps hn L).2
  have hBm : B * reMbar eps p n A L ≤ B * (4 * t / a) := mul_le_mul_of_nonneg_left hL.le hB0.le
  exact reHeight_le (by omega) (hone (L + 1) (by linarith))

/-- Step 4, first alternative: `H ≤ L + 1` once `log (2 n / θ) ≤ (2^L - 1) log (A / (4 B))`,
because then `N_L ≤ n / Δ_L + 1 ≤ θ`. -/
theorem reHeight_le_reCutoff_add_one {θ : ℝ}
    (hone : ∀ ℓ, (reSize eps p n ℓ : ℝ) ≤ θ → reSize eps p n (ℓ + 1) = 1) (hθ2 : 2 ≤ θ)
    (hcond : Real.log (2 * n / θ) ≤
      ((2 : ℝ) ^ reCutoff eps p n A (4 * t / a) - 1) * Real.log (A / (4 * B))) :
    reHeight eps p n ≤ reCutoff eps p n A (4 * t / a) + 1 := by
  set L := reCutoff eps p n A (4 * t / a)
  have hΔl := (reDelta_bounds_of_le_reCutoff heps hn ha ha1 hB ht hBA hM (le_refl L)).1
  have hB0 : 0 < B := by linarith
  have hq1 : 1 < A / (4 * B) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hq : 1 / (4 * B) * A = A / (4 * B) := by ring
  rw [hq] at hΔl
  have hΔ1 : (1 : ℝ) ≤ reDelta eps p n L := by exact_mod_cast one_le_reDelta heps hn L
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  have hΔ2 : 2 * n / θ ≤ (reDelta eps p n L : ℝ) := by
    rw [← Real.log_le_log_iff (by positivity) (by linarith)]
    have h1 := Real.log_le_log (by positivity) hΔl
    rw [Real.log_pow, Nat.cast_sub hpow] at h1
    push_cast at h1
    linarith
  have hcov : ((reSize eps p n L : ℝ) - 1) * reDelta eps p n L < n := by
    have h := (re_cover (p := p) heps hn L).1
    have h1 := one_le_reSize (p := p) heps hn L
    have : (((reSize eps p n L - 1 : ℕ) : ℝ)) = (reSize eps p n L : ℝ) - 1 := by
      rw [Nat.cast_sub h1]; simp
    rw [← this]
    exact_mod_cast h
  have hNL : (reSize eps p n L : ℝ) ≤ θ := by
    have h2 : 2 * n ≤ θ * reDelta eps p n L := by
      rw [div_le_iff₀ (by linarith)] at hΔ2; linarith
    nlinarith
  exact reHeight_le (by omega) (hone L hNL)

end Cutoff

/-! ## Step 5: the window -/

/-- The integer bookkeeping of Step 5.  `L` is located by `αlo` from below and by `αup` from
above, `L + 1 ≤ H ≤ L + 2`, and `H = L + 1` once `β ≤ L + 1`. -/
private theorem window_of_cutoff {H L : ℕ} {y w αlo αup β : ℝ} (hy : 0 ≤ y) (hw : 0 < w)
    (hlo : y - w ≤ αlo) (hup : αup ≤ y + w) (htop : β ≤ y + w)
    (h1 : ∀ ℓ : ℕ, (ℓ : ℝ) + 1 ≤ αlo → ℓ < L) (h2 : ∀ ℓ : ℕ, αup ≤ ℓ + 1 → L ≤ ℓ)
    (h3 : L + 1 ≤ H) (h4 : H ≤ L + 2) (h5 : β ≤ L + 1 → H ≤ L + 1) :
    (y - w < H ∧ (H : ℝ) ≤ y + 1 + w) ∧ ((∀ m : ℤ, w ≤ |y - m|) → (H : ℤ) = ⌈y⌉) := by
  have h3' : (L : ℝ) + 1 ≤ H := by exact_mod_cast h3
  have h4' : (H : ℝ) ≤ L + 2 := by exact_mod_cast h4
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- lower bound
    rcases lt_or_ge αlo 1 with hα | hα
    · have : (0 : ℝ) ≤ L := Nat.cast_nonneg _
      linarith
    · set k := ⌊αlo⌋₊ with hk
      have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hα)
      have hkα : (k : ℝ) ≤ αlo := Nat.floor_le (by linarith)
      have hlt := h1 (k - 1) (by rw [Nat.cast_sub hk1]; simp; exact hkα)
      have hkL : (k : ℝ) ≤ L := by exact_mod_cast (show k ≤ L by omega)
      have := Nat.lt_floor_add_one αlo
      linarith
  · -- upper bound
    by_cases hb : β ≤ L + 1
    · have hH := h5 hb
      have hH' : (H : ℝ) ≤ L + 1 := by exact_mod_cast hH
      have hLy : (L : ℝ) ≤ y + w := by
        by_contra hc
        push Not at hc
        have hL1 : 1 ≤ L := by
          by_contra h0
          have : L = 0 := by omega
          rw [this] at hc
          simp at hc
          linarith
        have := h2 (L - 1) (by rw [Nat.cast_sub hL1]; simp; linarith)
        omega
      linarith
    · push Not at hb
      linarith
  · -- the exact value
    intro hm
    set m := ⌊y⌋ with hmdef
    have hm0 : 0 ≤ m := Int.floor_nonneg.2 hy
    have hmy : (m : ℝ) ≤ y := Int.floor_le y
    have hym : y < m + 1 := Int.lt_floor_add_one y
    have hw1 : w ≤ y - m := by
      have := hm m
      rwa [abs_of_nonneg (by linarith)] at this
    have hw2 : w ≤ m + 1 - y := by
      have := hm (m + 1)
      push_cast at this
      rwa [abs_of_neg (by linarith), neg_sub] at this
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = m := ⟨m.toNat, Int.toNat_of_nonneg hm0⟩
    have hkR : (k : ℝ) = m := by rw [← hk]; rfl
    have hLk : k ≤ L := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · omega
      · have := h1 (k - 1) (by rw [Nat.cast_sub hpos]; simp; linarith)
        omega
    have hkL : L ≤ k := h2 k (by linarith)
    have hLeq : L = k := le_antisymm hkL hLk
    have hH : H = k + 1 := by
      have := h5 (by rw [hLeq]; linarith)
      omega
    have hceil : ⌈y⌉ = m + 1 := by
      rw [Int.ceil_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hceil, hH, ← hk]
    push_cast
    ring

/-- **Pathwise window** (Steps 1–5 of `thm:GRE`).  Under the count bracket on every layer and
Step 1 below the threshold `θ`, any `y ≥ 0`, `w > 0` dominating the three `log₂` thresholds
give `y - w < H ≤ y + 1 + w`, and `H = ⌈y⌉` when `y` is at distance at least `w` from `ℤ`. -/
theorem reHeight_window_of_bracket {eps : ℝ} {p : ℕ → ℝ} {n : ℕ} {A a B t θ Xtop y w : ℝ}
    (heps : 1 ≤ eps) (hn : 1 ≤ n) (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hBA : 4 * B < A)
    (hM : ∀ ℓ, a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ ∧
      (reSegs eps p n ℓ : ℝ) ≤ B * reMbar eps p n A ℓ + t)
    (hone : ∀ ℓ, (reSize eps p n ℓ : ℝ) ≤ θ → reSize eps p n (ℓ + 1) = 1)
    (hθ : 2 * (B * (4 * t / a) + t) ≤ θ) (hθn : θ ≤ 2 * n) (hτn : 4 * t / a ≤ n)
    (hXtop : 2 * Real.log (2 * n / θ) + Real.log (A / (4 * B)) ≤ Xtop)
    (hy : 0 ≤ y) (hw : 0 < w)
    (hlo : y - w ≤
      Real.logb 2 ((Real.log n - Real.log (4 * t / a)) / Real.log (2 / a * A) + 1))
    (hup : Real.logb 2 (Real.log n / Real.log (A / (4 * B)) + 1) ≤ y + w)
    (htop : Real.logb 2 (Xtop / Real.log (A / (4 * B)) + 1) ≤ y + w) :
    (y - w < reHeight eps p n ∧ (reHeight eps p n : ℝ) ≤ y + 1 + w) ∧
      ((∀ m : ℤ, w ≤ |y - m|) → ((reHeight eps p n : ℕ) : ℤ) = ⌈y⌉) := by
  have hA := one_le_of_bracket hB hBA
  have hB0 : 0 < B := by linarith
  have hq1 : 1 < A / (4 * B) := by rw [lt_div_iff₀ (by linarith)]; linarith
  have hlq : 0 < Real.log (A / (4 * B)) := Real.log_pos hq1
  have hb : 2 ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  have hlb : 0 < Real.log (2 / a * A) := Real.log_pos (by nlinarith)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hτ := one_lt_tau ha ha1 ht
  have hθ2 : 2 ≤ θ := by
    have : 0 ≤ B * (4 * t / a) := by positivity
    linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hXlo : 0 ≤ Real.log n - Real.log (4 * t / a) := by
    have := Real.log_le_log (by linarith) hτn
    linarith
  have h2n : 0 ≤ Real.log (2 * n / θ) := Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
  have hXtop0 : 0 ≤ Xtop := by linarith
  -- `2 ^ (ℓ + 1)` as a real power
  have hrp : ∀ ℓ : ℕ, (2 : ℝ) ^ ((ℓ : ℝ) + 1) = 2 ^ (ℓ + 1) := fun ℓ => by
    rw [← Real.rpow_natCast]; push_cast; rfl
  refine window_of_cutoff (L := reCutoff eps p n A (4 * t / a)) hy hw hlo hup htop ?_ ?_
    (reCutoff_lt_reHeight heps hn ha ha1 hB ht hBA hM)
    (reHeight_le_reCutoff_add_two heps hn ha ha1 hB ht hBA hM hone hθ) ?_
  · intro ℓ hℓ
    rw [Real.le_logb_iff_rpow_le one_lt_two (by positivity), hrp] at hℓ
    apply lt_reCutoff_of_log heps hn ha ha1 hB ht hBA hM
    have := (le_div_iff₀ hlb).1 (show (2 : ℝ) ^ (ℓ + 1) - 1 ≤
      (Real.log n - Real.log (4 * t / a)) / Real.log (2 / a * A) by linarith)
    linarith
  · intro ℓ hℓ
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity), hrp] at hℓ
    apply reCutoff_le_of_log heps hn ha ha1 hB ht hBA hM
    have := (div_le_iff₀ hlq).1 (show Real.log n / Real.log (A / (4 * B)) ≤
      (2 : ℝ) ^ (ℓ + 1) - 1 by linarith)
    linarith
  · intro hβ
    apply reHeight_le_reCutoff_add_one heps hn ha ha1 hB ht hBA hM hone hθ2
    have hβ' : Real.logb 2 (Xtop / Real.log (A / (4 * B)) + 1) ≤
        ((reCutoff eps p n A (4 * t / a) : ℕ) : ℝ) + 1 := hβ
    rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity), hrp] at hβ'
    have := (div_le_iff₀ hlq).1 (show Xtop / Real.log (A / (4 * B)) ≤
      (2 : ℝ) ^ (reCutoff eps p n A (4 * t / a) + 1) - 1 by linarith)
    rw [pow_succ] at this
    nlinarith

end

end PGM
