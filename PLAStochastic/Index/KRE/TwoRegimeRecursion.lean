import PLAStochastic.Index.Algorithm.RankHeightRecursion
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Height of ALG-RE with a noise regime and a curvature regime (Model K)

Deterministic part of `thm:heightKre` (`proofs/proofK_rank_core.tex`), in the simplified
form that uses only the "short windows are feasible" count of `lem:shortseg` in the
curvature regime.  Notation as in `PLAStochastic.Index.Algorithm.RankHeightRecursion`: `N_ℓ = reSize`, `Δ_ℓ = reDelta`,
`M_{ℓ+1} = reSegs`, `mbar_ℓ = N_ℓ / (Δ_ℓ A)` (`reMbar`), `τ = 4 t / a`, and
`s_ℓ = n / Δ_ℓ`.  A threshold `Dn` splits the layers into the noise regime `Δ_ℓ ≤ Dn` and
the curvature regime `Dn < Δ_ℓ`; since `Δ_ℓ` is non-decreasing (`reDelta_mono`) the run
never returns to the noise regime.

* Noise regime: the count bracket `a mbar_ℓ - t ≤ M_{ℓ+1} ≤ B mbar_ℓ + t` is assumed only
  there (its upper half for the upper bound, its lower half for the lower bound).
* Curvature regime: `M_{ℓ+1} ≤ N_ℓ / τ♭(Δ_ℓ) + 1` whenever `1 ≤ τ♭(Δ_ℓ)`, with
  `τ♭(Δ) = min (c₁ Δ, c₂ √(n / Δ), c₃ n / Δ)` (`kreTau`).  Either `N_ℓ ≤ τ♭` and then
  `N_{ℓ+1} ≤ 4`, or `τ♭(Δ_ℓ) Δ_ℓ ≤ 4 Δ_{ℓ+1}`, i.e. `s_{ℓ+1} ≤ 4 s_ℓ / τ♭(Δ_ℓ)`.
  The span entry gives `s_{ℓ+1} ≤ 4 / c₃`.  The curvature entry `c₂ √s` is below the noise
  entry `c₁ Δ` exactly when `c₂² n ≤ c₁² Δ³`; under `64 c₂² n ≤ c₁⁵ Dn⁶` this holds from
  the second curvature-regime layer on, because a noise-entry step has
  `Δ_{ℓ+1} ≥ c₁ Δ_ℓ² / 4 ≥ c₁ Dn² / 4` (at most one "band" layer).  There
  `s_{ℓ+1}² ≤ (16 / c₂²) s_ℓ`, so `log (s_ℓ / K)` halves, `K = max 1 (16 / c₂²)`, and within
  `⌈log₂ log n⌉` layers `s_ℓ ≤ C₀ = max (3 K) (4 / c₃)`, i.e. `N_ℓ ≤ C₀ + 1`.  With
  `1 ≤ c₁ Dn`, every curvature-regime layer with `C₀ < s_ℓ` has `1 ≤ τ♭(Δ_ℓ)`.
* Upper bound (`kreHeight_le`):
  `H ≤ log₂ (log n / log (A / (4 B))) + log₂ (2 (B τ + t)) + log₂ log n
      + log₂ (max (3 max 1 (16 / c₂²)) (4 / c₃) + 1) + 8`.
* Lower bound (`logb_lt_kreHeight`): if `n^{1/4} ≤ Dn` and `τ ≤ √n` then
  `log₂ (log n / (2 log ((2 / a) A))) < H`; the lower bracket is used only on layers with
  `A Δ_ℓ² ≤ √n`, which lie in the noise regime.

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

/-- `τ♭(Δ) = min (c₁ Δ, c₂ √(n / Δ), c₃ n / Δ)`, the short-window length of
    `lem:shortseg` (TeX `\tau_\flat`, with `c₁ ≍ eps² / log n`, `c₂ ≍ √eps`, and a fixed
    `c₃`; the third entry keeps the window span `τ Δ` below a multiple of `n`). -/
def kreTau (n : ℕ) (c₁ c₂ c₃ Δ : ℝ) : ℝ :=
  min (min (c₁ * Δ) (c₂ * Real.sqrt (n / Δ))) (c₃ * (n / Δ))

theorem kreTau_pos {n : ℕ} {c₁ c₂ c₃ Δ : ℝ} (hn : 1 ≤ n) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) (hΔ : 0 < Δ) : 0 < kreTau n c₁ c₂ c₃ Δ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_min (lt_min (mul_pos hc₁ hΔ) (mul_pos hc₂ (Real.sqrt_pos.2 (div_pos hn' hΔ))))
    (mul_pos hc₃ (div_pos hn' hΔ))

/-- `τ♭` is one of its two outer entries. -/
theorem kreTau_cases (n : ℕ) (c₁ c₂ c₃ Δ : ℝ) :
    kreTau n c₁ c₂ c₃ Δ = min (c₁ * Δ) (c₂ * Real.sqrt (n / Δ)) ∨
      kreTau n c₁ c₂ c₃ Δ = c₃ * (n / Δ) :=
  min_choice _ _

/-- The curvature entry of `τ♭` is the smaller one iff `c₂² n ≤ c₁² Δ³`. -/
theorem sqrt_entry_le_iff {n : ℕ} {c₁ c₂ Δ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hΔ : 0 < Δ) :
    c₂ * Real.sqrt (n / Δ) ≤ c₁ * Δ ↔ c₂ ^ 2 * n ≤ c₁ ^ 2 * Δ ^ 3 := by
  have h0 : 0 ≤ c₂ * Real.sqrt (n / Δ) := mul_nonneg hc₂ (Real.sqrt_nonneg _)
  have h1 : 0 ≤ c₁ * Δ := (mul_pos hc₁ hΔ).le
  rw [← pow_le_pow_iff_left₀ h0 h1 two_ne_zero, mul_pow,
    Real.sq_sqrt (div_nonneg (Nat.cast_nonneg _) hΔ.le), mul_pow, mul_div_assoc',
    div_le_iff₀ hΔ]
  have : c₁ ^ 2 * Δ ^ 2 * Δ = c₁ ^ 2 * Δ ^ 3 := by ring
  rw [this]

/-- In the curvature branch `c₂² n ≤ c₁² Δ³`, `min (c₁ Δ) (c₂ √(n / Δ)) = c₂ √(n / Δ)`. -/
theorem min_entry_eq_of_curv {n : ℕ} {c₁ c₂ Δ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hΔ : 0 < Δ) (h : c₂ ^ 2 * n ≤ c₁ ^ 2 * Δ ^ 3) :
    min (c₁ * Δ) (c₂ * Real.sqrt (n / Δ)) = c₂ * Real.sqrt (n / Δ) :=
  min_eq_right ((sqrt_entry_le_iff hc₁ hc₂ hΔ).2 h)

/-- Outside the curvature branch, `min (c₁ Δ) (c₂ √(n / Δ)) = c₁ Δ`. -/
theorem min_entry_eq_of_not_curv {n : ℕ} {c₁ c₂ Δ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 ≤ c₂)
    (hΔ : 0 < Δ) (h : ¬ c₂ ^ 2 * n ≤ c₁ ^ 2 * Δ ^ 3) :
    min (c₁ * Δ) (c₂ * Real.sqrt (n / Δ)) = c₁ * Δ :=
  min_eq_left (le_of_not_ge fun h' => h ((sqrt_entry_le_iff hc₁ hc₂ hΔ).1 h'))

theorem one_le_log_of_three_le {n : ℕ} (hn3 : 3 ≤ n) : 1 ≤ Real.log n := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have h1 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).2 Real.exp_one_lt_three
  have h2 := Real.log_le_log (by norm_num) h3
  linarith

/-- On a curvature-regime spacing `Dn < Δ` with `1 ≤ c₁ Dn` and
    `max (3 max 1 (16 / c₂²)) (4 / c₃) < n / Δ`, all three entries of `τ♭(Δ)` are at
    least `1`. -/
theorem one_le_kreTau_of_lt {n : ℕ} {c₁ c₂ c₃ Dn Δ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hc₃ : 0 < c₃) (hc₁D : 1 ≤ c₁ * Dn) (hΔ : Dn < Δ)
    (hs : max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃) < n / Δ) :
    1 ≤ kreTau n c₁ c₂ c₃ Δ := by
  have hK := le_max_right (1 : ℝ) (16 / c₂ ^ 2)
  have hC1 := le_max_left (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃)
  have hC2 := le_max_right (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃)
  have h16 : 1 / c₂ ^ 2 ≤ 16 / c₂ ^ 2 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have h4 : 1 / c₃ ≤ 4 / c₃ := div_le_div_of_nonneg_right (by norm_num) hc₃.le
  have hs2 : 1 / c₂ ^ 2 ≤ n / Δ := by
    have : 0 ≤ 16 / c₂ ^ 2 := by positivity
    linarith
  have hs3 : 1 / c₃ ≤ n / Δ := by linarith
  refine le_min (le_min ?_ ?_) ?_
  · exact hc₁D.trans (mul_le_mul_of_nonneg_left hΔ.le hc₁.le)
  · have hsq : 1 / c₂ ≤ Real.sqrt (n / Δ) := by
      rw [Real.le_sqrt (by positivity) ((by positivity : (0 : ℝ) ≤ 1 / c₂ ^ 2).trans hs2),
        div_pow, one_pow]
      exact hs2
    calc (1 : ℝ) = c₂ * (1 / c₂) := by field_simp
      _ ≤ c₂ * Real.sqrt (n / Δ) := mul_le_mul_of_nonneg_left hsq hc₂.le
  · calc (1 : ℝ) = c₃ * (1 / c₃) := by field_simp
      _ ≤ c₃ * (n / Δ) := mul_le_mul_of_nonneg_left hs3 hc₃.le

section Run

variable {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}

/-! ## Monotonicity of the spacing and the terminal buffer -/

theorem reDelta_le_succ (heps : 1 ≤ eps) (hn : 1 ≤ n) (ℓ : ℕ) :
    reDelta eps p n ℓ ≤ reDelta eps p n (ℓ + 1) := by
  rw [reDelta_succ]
  exact Nat.le_mul_of_pos_left _ (one_le_reStep heps hn ℓ)

/-- `ℓ ↦ Δ_ℓ` is non-decreasing. -/
theorem reDelta_mono (heps : 1 ≤ eps) (hn : 1 ≤ n) : Monotone (reDelta eps p n) :=
  monotone_nat_of_le_succ (reDelta_le_succ heps hn)

theorem reDelta_le_of_le (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ ℓ' : ℕ} (h : ℓ ≤ ℓ') :
    (reDelta eps p n ℓ : ℝ) ≤ reDelta eps p n ℓ' := by
  exact_mod_cast reDelta_mono (p := p) heps hn h

/-- If `N_{ℓ+1} ≤ 4` then `H ≤ ℓ + 4`. -/
theorem reHeight_le_of_reSize_succ_le_four (heps : 1 ≤ eps) (hn : 1 ≤ n) {ℓ : ℕ}
    (h : reSize eps p n (ℓ + 1) ≤ 4) : reHeight eps p n ≤ ℓ + 4 := by
  have h1 := reHeight_le_add_log (p := p) heps hn (ℓ + 1)
  have h2 : Nat.log 2 (reSize eps p n (ℓ + 1)) ≤ 2 := by
    calc Nat.log 2 (reSize eps p n (ℓ + 1)) ≤ Nat.log 2 (2 ^ 2) := Nat.log_mono_right h
      _ = 2 := Nat.log_pow (by norm_num) 2
  omega

/-- If `s_ℓ = n / Δ_ℓ ≤ C` then `N_ℓ ≤ C + 1` and `H ≤ ℓ + log₂ (C + 1) + 1`. -/
theorem reHeight_le_of_div_le (heps : 1 ≤ eps) (hn : 1 ≤ n) {C : ℝ} {ℓ : ℕ}
    (h : (n : ℝ) / reDelta eps p n ℓ ≤ C) :
    (reHeight eps p n : ℝ) ≤ ℓ + Real.logb 2 (C + 1) + 1 := by
  have hΔ : (0 : ℝ) < reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  have hN1 := one_le_reSize (p := p) heps hn ℓ
  have hNC : (reSize eps p n ℓ : ℝ) ≤ C + 1 := by
    have h1 : ((reSize eps p n ℓ - 1 : ℕ) : ℝ) * reDelta eps p n ℓ < n := by
      exact_mod_cast (re_cover heps hn ℓ).1
    rw [Nat.cast_sub hN1, Nat.cast_one] at h1
    have h2 : (reSize eps p n ℓ : ℝ) - 1 < n / reDelta eps p n ℓ := by
      rw [lt_div_iff₀ hΔ]; exact h1
    linarith
  have hlog : (Nat.log 2 (reSize eps p n ℓ) : ℝ) ≤ Real.logb 2 (C + 1) := by
    have h1 := Real.natLog_le_logb (reSize eps p n ℓ) 2
    have hpos : (0 : ℝ) < reSize eps p n ℓ := by exact_mod_cast hN1
    push_cast at h1
    exact h1.trans (Real.logb_le_logb_of_le one_lt_two hpos hNC)
  have hH : (reHeight eps p n : ℝ) ≤ ℓ + Nat.log 2 (reSize eps p n ℓ) + 1 := by
    exact_mod_cast reHeight_le_add_log heps hn ℓ
  linarith

/-! ## One layer of the curvature regime -/

/-- **Near-terminal layer**: if `M_{ℓ+1} ≤ N_ℓ / τ + 1` and `N_ℓ ≤ τ`, then
    `M_{ℓ+1} ≤ 2` and `N_{ℓ+1} ≤ 4`. -/
theorem reSize_succ_le_four_of_le_tau (heps : 1 ≤ eps) (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ)
    {ℓ : ℕ} (hM : (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n ℓ / τ + 1)
    (hN : (reSize eps p n ℓ : ℝ) ≤ τ) : reSize eps p n (ℓ + 1) ≤ 4 := by
  have h1 : (reSize eps p n ℓ : ℝ) / τ ≤ 1 := (div_le_one hτ).2 hN
  have h2 : reSegs eps p n ℓ ≤ 2 := by
    have : (reSegs eps p n ℓ : ℝ) ≤ 2 := by linarith
    exact_mod_cast this
  have := (reSize_succ_bounds (p := p) heps hn ℓ).2
  omega

/-- **Short windows force a long step**: if `M_{ℓ+1} ≤ N_ℓ / τ + 1` and `τ < N_ℓ`, then
    `d_ℓ > τ / 4`, i.e. `τ Δ_ℓ ≤ 4 Δ_{ℓ+1}`. -/
theorem tau_mul_le_reDelta_succ (heps : 1 ≤ eps) (hn : 1 ≤ n) {τ : ℝ} (hτ : 0 < τ)
    {ℓ : ℕ} (hM : (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n ℓ / τ + 1)
    (hN : τ < reSize eps p n ℓ) :
    τ * reDelta eps p n ℓ ≤ 4 * reDelta eps p n (ℓ + 1) := by
  have hM0 : 0 < reSegs eps p n ℓ := one_le_reSegs heps hn ℓ
  have hd1 : (1 : ℝ) ≤ reStep eps p n ℓ := by exact_mod_cast one_le_reStep heps hn ℓ
  have hlt : ((reSize eps p n ℓ : ℕ) : ℝ) <
      (reStep eps p n ℓ : ℝ) * reSegs eps p n ℓ + reSegs eps p n ℓ := by
    have : reSize eps p n ℓ < reStep eps p n ℓ * reSegs eps p n ℓ + reSegs eps p n ℓ :=
      Nat.lt_div_mul_add hM0
    exact_mod_cast this
  have hMd : (reSegs eps p n ℓ : ℝ) ≤ (reStep eps p n ℓ : ℝ) * reSegs eps p n ℓ :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) hd1
  have hMτ : (reSegs eps p n ℓ : ℝ) * τ < 2 * reSize eps p n ℓ := by
    have := mul_le_mul_of_nonneg_right hM hτ.le
    rw [add_mul, div_mul_cancel₀ _ hτ.ne', one_mul] at this
    linarith
  have hNpos : (0 : ℝ) < reSize eps p n ℓ := by linarith
  have h3 : (reSize eps p n ℓ : ℝ) * τ < (reSize eps p n ℓ : ℝ) * (4 * reStep eps p n ℓ) := by
    calc (reSize eps p n ℓ : ℝ) * τ
        < (2 * (reStep eps p n ℓ : ℝ) * reSegs eps p n ℓ) * τ :=
          mul_lt_mul_of_pos_right (by linarith) hτ
      _ = 2 * (reStep eps p n ℓ : ℝ) * ((reSegs eps p n ℓ : ℝ) * τ) := by ring
      _ ≤ 2 * (reStep eps p n ℓ : ℝ) * (2 * reSize eps p n ℓ) :=
          mul_le_mul_of_nonneg_left hMτ.le (by positivity)
      _ = (reSize eps p n ℓ : ℝ) * (4 * reStep eps p n ℓ) := by ring
  have h4 : τ < 4 * reStep eps p n ℓ := lt_of_mul_lt_mul_left h3 hNpos.le
  rw [reDelta_succ, Nat.cast_mul]
  calc τ * reDelta eps p n ℓ ≤ (4 * reStep eps p n ℓ) * reDelta eps p n ℓ :=
        mul_le_mul_of_nonneg_right h4.le (Nat.cast_nonneg _)
    _ = 4 * ((reStep eps p n ℓ : ℝ) * reDelta eps p n ℓ) := by ring

/-- **The span branch**: if `c₃ (n / Δ_ℓ) Δ_ℓ ≤ 4 Δ_{ℓ+1}` then `s_{ℓ+1} ≤ 4 / c₃`. -/
theorem div_reDelta_succ_le_of_span (heps : 1 ≤ eps) (hn : 1 ≤ n) {c₃ : ℝ} (hc₃ : 0 < c₃)
    {ℓ : ℕ} (h : c₃ * (n / reDelta eps p n ℓ) * reDelta eps p n ℓ ≤
      4 * reDelta eps p n (ℓ + 1)) :
    (n : ℝ) / reDelta eps p n (ℓ + 1) ≤ 4 / c₃ := by
  have hΔ : (0 : ℝ) < reDelta eps p n ℓ := by
    have : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
    linarith
  have hΔ' : (0 : ℝ) < reDelta eps p n (ℓ + 1) := by
    have : (1 : ℝ) ≤ reDelta eps p n (ℓ + 1) := by exact_mod_cast one_le_reDelta heps hn _
    linarith
  rw [mul_assoc, div_mul_cancel₀ _ hΔ.ne'] at h
  rw [div_le_div_iff₀ hΔ' hc₃]
  linarith

/-! ## The curvature phase -/

/-- **Curvature phase** (`lem:phase2rec` in the simplified form).  Let layer `m` be in the
    curvature regime `Dn < Δ_m` and in the curvature branch `c₂² n ≤ c₁² Δ_m³`; both
    persist, so there `τ♭ = min (c₂ √s) (c₃ s)`.  Put `K = max 1 (16 / c₂²)` and
    `C₀ = max (3 K) (4 / c₃)`.  While `τ♭(Δ_ℓ) < N_ℓ` and `C₀ < s_ℓ`, either
    `s_{ℓ+1}² ≤ K s_ℓ` (curvature entry) or `s_{ℓ+1} ≤ 4 / c₃` (span entry), so within
    `⌈log₂ log n⌉` layers either `N_ℓ ≤ τ♭(Δ_ℓ)` (then `N_{ℓ+1} ≤ 4`) or `s_ℓ ≤ C₀`
    (then `N_ℓ ≤ C₀ + 1`).  Hence `H ≤ m + log₂ log n + log₂ (C₀ + 1) + 5`. -/
theorem reHeight_le_curv (heps : 1 ≤ eps) (hn3 : 3 ≤ n) {c₁ c₂ c₃ Dn : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₁D : 1 ≤ c₁ * Dn)
    (hC : ∀ ℓ, Dn < (reDelta eps p n ℓ : ℝ) → 1 ≤ kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) →
      (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n ℓ / kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) + 1)
    {m : ℕ} (hmD : Dn < reDelta eps p n m)
    (hmc : c₂ ^ 2 * n ≤ c₁ ^ 2 * (reDelta eps p n m : ℝ) ^ 3) :
    (reHeight eps p n : ℝ) ≤ m + Real.logb 2 (Real.log n) +
      Real.logb 2 (max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃) + 1) + 5 := by
  have hn : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set K : ℝ := max 1 (16 / c₂ ^ 2) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK16 : 16 / c₂ ^ 2 ≤ K := le_max_right _ _
  set C₀ : ℝ := max (3 * K) (4 / c₃) with hC₀
  have h3K : 3 * K ≤ C₀ := le_max_left _ _
  have h4c : 4 / c₃ ≤ C₀ := le_max_right _ _
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hΔ1 : ∀ ℓ, (1 : ℝ) ≤ reDelta eps p n ℓ := fun ℓ => by
    exact_mod_cast one_le_reDelta heps hn ℓ
  have hΔpos : ∀ ℓ, (0 : ℝ) < reDelta eps p n ℓ := fun ℓ => by linarith [hΔ1 ℓ]
  have hspos : ∀ ℓ, (0 : ℝ) < n / reDelta eps p n ℓ := fun ℓ => div_pos hnpos (hΔpos ℓ)
  -- every layer from `m` on is in the curvature regime and in the curvature branch
  have hD : ∀ ℓ, m ≤ ℓ → Dn < reDelta eps p n ℓ := fun ℓ hℓ =>
    hmD.trans_le (reDelta_le_of_le heps hn hℓ)
  have hτeq : ∀ ℓ, m ≤ ℓ → min (c₁ * reDelta eps p n ℓ)
      (c₂ * Real.sqrt (n / reDelta eps p n ℓ)) = c₂ * Real.sqrt (n / reDelta eps p n ℓ) := by
    intro ℓ hℓ
    refine min_entry_eq_of_curv hc₁ hc₂.le (hΔpos ℓ) (hmc.trans ?_)
    have h1 := reDelta_le_of_le (p := p) heps hn hℓ
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hΔpos m).le h1 3) (by positivity)
  have hτpos : ∀ ℓ, 0 < kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) := fun ℓ =>
    kreTau_pos hn hc₁ hc₂ hc₃ (hΔpos ℓ)
  -- the stopping predicate
  set Q : ℕ → Prop := fun ℓ =>
    (reSize eps p n ℓ : ℝ) ≤ kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) ∨
      (n : ℝ) / reDelta eps p n ℓ ≤ C₀ with hQ
  -- one step: `s_{ℓ+1}² ≤ K s_ℓ` (curvature entry) or `s_{ℓ+1} ≤ C₀` (span entry)
  have hstep : ∀ ℓ, m ≤ ℓ → ¬ Q ℓ →
      ((n : ℝ) / reDelta eps p n (ℓ + 1)) ^ 2 ≤ K * (n / reDelta eps p n ℓ) ∨
        (n : ℝ) / reDelta eps p n (ℓ + 1) ≤ C₀ := by
    intro ℓ hℓ hnQ
    have hlt : kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) < reSize eps p n ℓ :=
      lt_of_not_ge fun h => hnQ (Or.inl h)
    have hτ1 : 1 ≤ kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) :=
      one_le_kreTau_of_lt hc₁ hc₂ hc₃ hc₁D (hD ℓ hℓ) (lt_of_not_ge fun h => hnQ (Or.inr h))
    have h1 := tau_mul_le_reDelta_succ heps hn (hτpos ℓ) (hC ℓ (hD ℓ hℓ) hτ1) hlt
    rcases kreTau_cases n c₁ c₂ c₃ (reDelta eps p n ℓ) with hτ | hτ
    swap
    · rw [hτ] at h1
      exact Or.inr ((div_reDelta_succ_le_of_span heps hn hc₃ h1).trans h4c)
    left
    rw [hτ, hτeq ℓ hℓ] at h1
    have hΔ := hΔpos ℓ
    have hΔ' := hΔpos (ℓ + 1)
    set Δ : ℝ := (reDelta eps p n ℓ : ℝ)
    set Δ' : ℝ := (reDelta eps p n (ℓ + 1) : ℝ)
    have h2 : c₂ ^ 2 * n * Δ ≤ 16 * Δ' ^ 2 := by
      have h0 : 0 ≤ c₂ * Real.sqrt (n / Δ) * Δ := by positivity
      have h3 := pow_le_pow_left₀ h0 h1 2
      have hsq : (c₂ * Real.sqrt (n / Δ) * Δ) ^ 2 = c₂ ^ 2 * n * Δ := by
        rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hnpos.le hΔ.le)]
        field_simp
      calc c₂ ^ 2 * n * Δ = (c₂ * Real.sqrt (n / Δ) * Δ) ^ 2 := hsq.symm
        _ ≤ (4 * Δ') ^ 2 := h3
        _ = 16 * Δ' ^ 2 := by ring
    have h3 : ((n : ℝ) / Δ') ^ 2 ≤ 16 / c₂ ^ 2 * (n / Δ) := by
      rw [div_pow, div_le_iff₀ (by positivity),
        show 16 / c₂ ^ 2 * (n / Δ) * Δ' ^ 2 = n * (16 * Δ' ^ 2) / (c₂ ^ 2 * Δ) by
          field_simp,
        le_div_iff₀ (by positivity)]
      calc (n : ℝ) ^ 2 * (c₂ ^ 2 * Δ) = n * (c₂ ^ 2 * n * Δ) := by ring
        _ ≤ n * (16 * Δ' ^ 2) := mul_le_mul_of_nonneg_left h2 hnpos.le
    exact h3.trans (mul_le_mul_of_nonneg_right hK16 (hspos ℓ).le)
  -- in logarithms: `log (s_{ℓ+1} / K) ≤ log (s_ℓ / K) / 2`
  have hlogstep : ∀ ℓ, m ≤ ℓ → ¬ Q ℓ → ¬ Q (ℓ + 1) →
      Real.log (n / reDelta eps p n (ℓ + 1)) - Real.log K ≤
        (Real.log (n / reDelta eps p n ℓ) - Real.log K) / 2 := by
    intro ℓ hℓ hnQ hnQ'
    have hs := (hstep ℓ hℓ hnQ).resolve_right fun h => hnQ' (Or.inr h)
    have h1 := Real.log_le_log (pow_pos (hspos (ℓ + 1)) 2) hs
    rw [Real.log_pow, Real.log_mul (by linarith) (hspos ℓ).ne'] at h1
    push_cast at h1
    linarith
  have hind : ∀ j, (∀ i ≤ j, ¬ Q (m + i)) →
      Real.log (n / reDelta eps p n (m + j)) - Real.log K ≤
        (Real.log (n / reDelta eps p n m) - Real.log K) / 2 ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro h
      have h1 := ih fun i hi => h i (by omega)
      have h2 := hlogstep (m + j) (by omega) (h j (by omega)) (h (j + 1) le_rfl)
      rw [← Nat.add_assoc]
      have h3 : (Real.log (n / reDelta eps p n (m + j)) - Real.log K) / 2 ≤
          ((Real.log (n / reDelta eps p n m) - Real.log K) / 2 ^ j) / 2 :=
        div_le_div_of_nonneg_right h1 (by norm_num)
      calc Real.log (n / reDelta eps p n (m + j + 1)) - Real.log K
          ≤ ((Real.log (n / reDelta eps p n m) - Real.log K) / 2 ^ j) / 2 := h2.trans h3
        _ = (Real.log (n / reDelta eps p n m) - Real.log K) / 2 ^ (j + 1) := by
          rw [pow_succ, div_div]
  -- the initial potential is at most `log n`
  have hw0 : Real.log (n / reDelta eps p n m) - Real.log K ≤ Real.log n := by
    have h1 : (n : ℝ) / reDelta eps p n m ≤ n := div_le_self hnpos.le (hΔ1 m)
    have := Real.log_le_log (hspos m) h1
    linarith
  -- `⌈log₂ log n⌉` halvings bring it below `1`
  have hlogn1 : 1 ≤ Real.log n := one_le_log_of_three_le hn3
  have hlb0 : 0 ≤ Real.logb 2 (Real.log n) := Real.logb_nonneg one_lt_two hlogn1
  set k := ⌈Real.logb 2 (Real.log n)⌉₊ with hk
  have hk2 : Real.log n ≤ 2 ^ k := by
    have h1 : Real.logb 2 (Real.log n) ≤ k := Nat.le_ceil _
    calc Real.log n = (2 : ℝ) ^ (Real.logb 2 (Real.log n)) :=
          (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ (2 : ℝ) ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      _ = 2 ^ k := Real.rpow_natCast 2 k
  have hexists : ∃ j ≤ k, Q (m + j) := by
    by_contra hne
    push Not at hne
    have h1 := hind k hne
    have h2 : (Real.log (n / reDelta eps p n m) - Real.log K) / 2 ^ k ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h3 : Real.log (n / reDelta eps p n (m + k)) ≤ 1 + Real.log K := by linarith
    have h4 : (n : ℝ) / reDelta eps p n (m + k) ≤ C₀ := by
      rw [Real.log_le_iff_le_exp (hspos _)] at h3
      calc (n : ℝ) / reDelta eps p n (m + k) ≤ Real.exp (1 + Real.log K) := h3
        _ = Real.exp 1 * K := by rw [Real.exp_add, Real.exp_log (by linarith)]
        _ ≤ 3 * K := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by linarith)
        _ ≤ C₀ := h3K
    exact hne k le_rfl (Or.inr h4)
  -- finish from the stopping layer `m + j`
  obtain ⟨j, hjk, hQj⟩ := hexists
  have hk1 : (k : ℝ) ≤ Real.logb 2 (Real.log n) + 1 := (Nat.ceil_lt_add_one hlb0).le
  have hlogC : 0 ≤ Real.logb 2 (C₀ + 1) := Real.logb_nonneg one_lt_two (by linarith)
  have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
  rcases hQj with h | h
  · have hN1 : (1 : ℝ) ≤ reSize eps p n (m + j) := by
      exact_mod_cast one_le_reSize heps hn (m + j)
    have h4 := reSize_succ_le_four_of_le_tau heps hn (hτpos _)
      (hC _ (hD _ (by omega)) (hN1.trans h)) h
    have h5 := reHeight_le_of_reSize_succ_le_four heps hn h4
    have h6 : (reHeight eps p n : ℝ) ≤ m + j + 4 := by exact_mod_cast h5
    linarith
  · have h5 := reHeight_le_of_div_le heps hn h
    push_cast at h5
    linarith

/-! ## The band layer and the upper bound -/

/-- **The band layer** (`lem:oneband` in the simplified form).  Let `Dn < Δ_L` and
    `64 c₂² n ≤ c₁⁵ Dn⁶`.  Either `N_L ≤ τ♭(Δ_L)`, and then `N_{L+1} ≤ 4`; or
    `τ♭(Δ_L) Δ_L ≤ 4 Δ_{L+1}`.  In the span entry `s_{L+1} ≤ 4 / c₃`; otherwise layer
    `L + 1` is in the curvature branch `c₂² n ≤ c₁² Δ_{L+1}³` (if `L` is not,
    `τ♭(Δ_L) = c₁ Δ_L` and `Δ_{L+1} ≥ c₁ Dn² / 4`).  Hence
    `H ≤ L + log₂ log n + log₂ (C₀ + 1) + 6`, `C₀ = max (3 max 1 (16 / c₂²)) (4 / c₃)`. -/
theorem reHeight_le_band (heps : 1 ≤ eps) (hn3 : 3 ≤ n) {c₁ c₂ c₃ Dn : ℝ}
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₁D : 1 ≤ c₁ * Dn)
    (hside : 64 * c₂ ^ 2 * n ≤ c₁ ^ 5 * Dn ^ 6)
    (hC : ∀ ℓ, Dn < (reDelta eps p n ℓ : ℝ) → 1 ≤ kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) →
      (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n ℓ / kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) + 1)
    {L : ℕ} (hLD : Dn < reDelta eps p n L) :
    (reHeight eps p n : ℝ) ≤ L + Real.logb 2 (Real.log n) +
      Real.logb 2 (max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃) + 1) + 6 := by
  have hn : 1 ≤ n := by omega
  have hDn : 0 < Dn := pos_of_mul_pos_right (by linarith) hc₁.le
  have hΔpos : ∀ ℓ, (0 : ℝ) < reDelta eps p n ℓ := fun ℓ => by
    have : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
    linarith
  have hlb0 : 0 ≤ Real.logb 2 (Real.log n) :=
    Real.logb_nonneg one_lt_two (one_le_log_of_three_le hn3)
  have hlogC : 0 ≤ Real.logb 2 (max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃) + 1) := by
    have h1 := le_max_left (1 : ℝ) (16 / c₂ ^ 2)
    have h2 := le_max_left (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃)
    exact Real.logb_nonneg one_lt_two (by linarith)
  have hτpos := kreTau_pos hn hc₁ hc₂ hc₃ (hΔpos L)
  by_cases hNτ : (reSize eps p n L : ℝ) ≤ kreTau n c₁ c₂ c₃ (reDelta eps p n L)
  · have hN1 : (1 : ℝ) ≤ reSize eps p n L := by exact_mod_cast one_le_reSize heps hn L
    have h4 := reSize_succ_le_four_of_le_tau heps hn hτpos (hC L hLD (hN1.trans hNτ)) hNτ
    have h5 : (reHeight eps p n : ℝ) ≤ L + 4 := by
      exact_mod_cast reHeight_le_of_reSize_succ_le_four heps hn h4
    linarith
  -- a layer with `s_L ≤ C₀` already has `N_L ≤ C₀ + 1`
  by_cases hs : (n : ℝ) / reDelta eps p n L ≤ max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃)
  · have h5 := reHeight_le_of_div_le heps hn hs
    linarith
  have hτ1 := one_le_kreTau_of_lt hc₁ hc₂ hc₃ hc₁D hLD (lt_of_not_ge hs)
  have h1 := tau_mul_le_reDelta_succ heps hn hτpos (hC L hLD hτ1) (lt_of_not_ge hNτ)
  rcases kreTau_cases n c₁ c₂ c₃ (reDelta eps p n L) with hτ | hτ
  swap
  · -- the span entry: `s_{L+1} ≤ 4 / c₃ ≤ C₀`
    rw [hτ] at h1
    have h2 := (div_reDelta_succ_le_of_span heps hn hc₃ h1).trans
      (le_max_right (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃))
    have h5 := reHeight_le_of_div_le heps hn h2
    push_cast at h5
    linarith
  rw [hτ] at h1
  have hmono := reDelta_le_of_le (p := p) heps hn (Nat.le_succ L)
  have hcurv : c₂ ^ 2 * n ≤ c₁ ^ 2 * (reDelta eps p n (L + 1) : ℝ) ^ 3 := by
    by_cases hc : c₂ ^ 2 * n ≤ c₁ ^ 2 * (reDelta eps p n L : ℝ) ^ 3
    · exact hc.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hΔpos L).le hmono 3) (by positivity))
    · rw [min_entry_eq_of_not_curv hc₁ hc₂.le (hΔpos L) hc] at h1
      have hΔ := hΔpos L
      set Δ : ℝ := (reDelta eps p n L : ℝ)
      set Δ' : ℝ := (reDelta eps p n (L + 1) : ℝ)
      have h2 : c₁ * Dn ^ 2 / 4 ≤ Δ' := by
        have h3 : Dn ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hDn.le hLD.le 2
        have h4 : c₁ * Dn ^ 2 ≤ c₁ * Δ * Δ := by
          calc c₁ * Dn ^ 2 ≤ c₁ * Δ ^ 2 := mul_le_mul_of_nonneg_left h3 hc₁.le
            _ = c₁ * Δ * Δ := by ring
        linarith
      have h3 : (c₁ * Dn ^ 2 / 4) ^ 3 ≤ Δ' ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
      calc c₂ ^ 2 * n ≤ c₁ ^ 5 * Dn ^ 6 / 64 := by linarith
        _ = c₁ ^ 2 * (c₁ * Dn ^ 2 / 4) ^ 3 := by ring
        _ ≤ c₁ ^ 2 * Δ' ^ 3 := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 := reHeight_le_curv heps hn3 hc₁ hc₂ hc₃ hc₁D hC (hLD.trans_le hmono) hcurv
  push_cast at h5
  linarith

/-- **Upper bound** (`thm:heightKre`, upper half, deterministic part).  Assume the upper
    count bracket `M_{ℓ+1} ≤ B mbar_ℓ + t` on the noise-regime layers `Δ_ℓ ≤ Dn`, the
    short-window count `M_{ℓ+1} ≤ N_ℓ / τ♭(Δ_ℓ) + 1` on the curvature-regime layers
    `Dn < Δ_ℓ` with `1 ≤ τ♭(Δ_ℓ)`, `1 < A / (4 B) ≤ n`, and the side conditions
    `1 ≤ c₁ Dn` and `64 c₂² n ≤ c₁⁵ Dn⁶`.  Then
    `H ≤ log₂ (log n / log (A / (4 B))) + log₂ (2 (B τ + t)) + log₂ log n
      + log₂ (max (3 max 1 (16 / c₂²)) (4 / c₃) + 1) + 8`, `τ = 4 t / a`. -/
theorem kreHeight_le (heps : 1 ≤ eps) (hn3 : 3 ≤ n) {A a B t c₁ c₂ c₃ Dn : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hq : 1 < A / (4 * B)) (hqn : A / (4 * B) ≤ n)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃) (hc₁D : 1 ≤ c₁ * Dn)
    (hside : 64 * c₂ ^ 2 * n ≤ c₁ ^ 5 * Dn ^ 6)
    (hup : ∀ ℓ, (reDelta eps p n ℓ : ℝ) ≤ Dn →
      (reSegs eps p n ℓ : ℝ) ≤ B * reMbar eps p n A ℓ + t)
    (hC : ∀ ℓ, Dn < (reDelta eps p n ℓ : ℝ) → 1 ≤ kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) →
      (reSegs eps p n ℓ : ℝ) ≤ reSize eps p n ℓ / kreTau n c₁ c₂ c₃ (reDelta eps p n ℓ) + 1) :
    (reHeight eps p n : ℝ) ≤ Real.logb 2 (Real.log n / Real.log (A / (4 * B))) +
      Real.logb 2 (2 * (B * (4 * t / a) + t)) + Real.logb 2 (Real.log n) +
      Real.logb 2 (max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃) + 1) + 8 := by
  classical
  have hn : 1 ≤ n := by omega
  have hB0 : 0 < B := by linarith
  have hBA : 4 * B ≤ A := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * B)).1 hq
    linarith
  have hA : 1 ≤ A := by linarith
  have hτ4 : 4 ≤ 4 * t / a := by
    rw [le_div_iff₀ ha]; linarith
  have hlb0 : 0 ≤ Real.logb 2 (Real.log n) :=
    Real.logb_nonneg one_lt_two (one_le_log_of_three_le hn3)
  have hlogC : 0 ≤ Real.logb 2 (max (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃) + 1) := by
    have h1 := le_max_left (1 : ℝ) (16 / c₂ ^ 2)
    have h2 := le_max_left (3 * max 1 (16 / c₂ ^ 2)) (4 / c₃)
    exact Real.logb_nonneg one_lt_two (by linarith)
  have hlogT : 0 ≤ Real.logb 2 (2 * (B * (4 * t / a) + t)) := by
    have : 0 ≤ B * (4 * t / a) := mul_nonneg hB0.le (by linarith)
    exact Real.logb_nonneg one_lt_two (by linarith)
  -- the first layer that leaves the noise regime or the concentration range
  have hex : ∃ ℓ, Dn < reDelta eps p n ℓ ∨ reMbar eps p n A ℓ < 4 * t / a :=
    ⟨reHeight eps p n, Or.inr (by
      have := reMbar_le_one_of_reSize_eq_one heps hn hA (reSize_reHeight (p := p) heps hn)
      linarith)⟩
  obtain ⟨L, hL, hbefore⟩ : ∃ L, (Dn < reDelta eps p n L ∨ reMbar eps p n A L < 4 * t / a) ∧
      ∀ ℓ < L, (reDelta eps p n ℓ : ℝ) ≤ Dn ∧ 4 * t / a ≤ reMbar eps p n A ℓ := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun ℓ hℓ => ?_⟩
    have := Nat.find_min hex hℓ
    push Not at this
    exact this
  -- (a) the noise regime: `A / (4 B) Δ_ℓ² ≤ Δ_{ℓ+1}` and `Δ_ℓ < n` below `L`
  have hlo : ∀ ℓ, ℓ < L →
      A / (4 * B) * 1 * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ reDelta eps p n (ℓ + 1) := by
    intro ℓ hℓ
    rw [mul_one]
    exact re_compress_lower heps hn ha ha1 hB ht hBA (hup ℓ (hbefore ℓ hℓ).1) (hbefore ℓ hℓ).2
  have hbelow : ∀ ℓ, ℓ < L → (reDelta eps p n ℓ : ℝ) < n := by
    intro ℓ hℓ
    have hm := (hbefore ℓ hℓ).2
    have hN := reSize_eq_reMbar_mul (p := p) heps hn (by linarith : (0 : ℝ) < A) ℓ
    have hΔ : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
    have hΔA : (1 : ℝ) ≤ (reDelta eps p n ℓ : ℝ) * A := one_le_mul_of_one_le_of_one_le hΔ hA
    have h2 : (2 : ℝ) ≤ reSize eps p n ℓ := by
      rw [hN]
      calc (2 : ℝ) ≤ reMbar eps p n A ℓ * 1 := by linarith
        _ ≤ reMbar eps p n A ℓ * ((reDelta eps p n ℓ : ℝ) * A) :=
          mul_le_mul_of_nonneg_left hΔA (by linarith)
    have h2' : 2 ≤ reSize eps p n ℓ := by exact_mod_cast h2
    exact_mod_cast reDelta_lt heps hn h2'
  have hLle := dexp_cutoff_le_logb (Δ := fun ℓ => (reDelta eps p n ℓ : ℝ))
    (a := A / (4 * B)) (A := 1) (by rwa [mul_one]) (by simp) hlo (by rwa [mul_one]) hbelow
  rw [mul_one] at hLle
  rcases le_or_gt (reDelta eps p n L : ℝ) Dn with hD | hD
  · -- (b) the count drops below `τ` inside the noise regime: `N_{L+1} ≤ 2 (B τ + t)`
    have hmL : reMbar eps p n A L < 4 * t / a := hL.resolve_left (not_lt.2 hD)
    have hML : (reSegs eps p n L : ℝ) ≤ B * (4 * t / a) + t := by
      have h1 := hup L hD
      have h2 : B * reMbar eps p n A L ≤ B * (4 * t / a) :=
        mul_le_mul_of_nonneg_left hmL.le hB0.le
      linarith
    have hNL : (reSize eps p n (L + 1) : ℝ) ≤ 2 * (B * (4 * t / a) + t) := by
      have : (reSize eps p n (L + 1) : ℝ) ≤ 2 * (reSegs eps p n L : ℝ) := by
        exact_mod_cast (reSize_succ_bounds heps hn L).2
      linarith
    have hlog : (Nat.log 2 (reSize eps p n (L + 1)) : ℝ) ≤
        Real.logb 2 (2 * (B * (4 * t / a) + t)) := by
      have h1 := Real.natLog_le_logb (reSize eps p n (L + 1)) 2
      have hpos : (0 : ℝ) < reSize eps p n (L + 1) := by
        exact_mod_cast one_le_reSize heps hn (L + 1)
      push_cast at h1
      exact h1.trans (Real.logb_le_logb_of_le one_lt_two hpos hNL)
    have hH : (reHeight eps p n : ℝ) ≤ L + 1 + Nat.log 2 (reSize eps p n (L + 1)) + 1 := by
      exact_mod_cast reHeight_le_cutoff heps hn L
    linarith
  · -- (c) the curvature regime
    have := reHeight_le_band heps hn3 hc₁ hc₂ hc₃ hc₁D hside hC hD
    linarith

/-! ## Lower bound: the bracket is needed only in the noise regime -/

/-- **Bootstrap** (eq:re-bootstrap, noise-regime version).  If `n^{1/4} ≤ Dn`,
    `τ ≤ √n` and `2 ^ (ℓ₀ + 1) log ((2 / a) A) ≤ log n / 2`, then every layer `ℓ ≤ ℓ₀` has
    `A Δ_ℓ² ≤ √n`, hence lies in the noise regime `Δ_ℓ ≤ n^{1/4} ≤ Dn`, and is in the
    concentration range `τ ≤ mbar_ℓ`, `τ = 4 t / a`.  Only the lower bracket on
    noise-regime layers is used. -/
theorem kreMbar_conc_of_bootstrap (heps : 1 ≤ eps) (hn : 1 ≤ n) {A a t Dn : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn)
    (hlo : ∀ ℓ, (reDelta eps p n ℓ : ℝ) ≤ Dn →
      a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hsqrt : 4 * t / a ≤ Real.sqrt n) {ℓ₀ : ℕ}
    (hcut : 2 ^ (ℓ₀ + 1) * Real.log (2 / a * A) ≤ Real.log n / 2) :
    ∀ ℓ ≤ ℓ₀, (reDelta eps p n ℓ : ℝ) ≤ Dn ∧ 4 * t / a ≤ reMbar eps p n A ℓ := by
  have hb : 1 ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  have hbA : 1 ≤ 2 / a * A := one_le_mul_of_one_le_of_one_le hb hA
  have hlogbA : 0 ≤ Real.log (2 / a * A) := Real.log_nonneg hbA
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro hℓ
    have hup : ∀ j, j < ℓ →
        (reDelta eps p n (j + 1) : ℝ) ≤ 2 / a * A * (reDelta eps p n j : ℝ) ^ 2 := by
      intro j hj
      have hj' := ih j hj (by omega)
      exact (re_compress_upper heps hn ha ht hA (hlo j hj'.1) hj'.2).1
    have hlo0 : ∀ j, j < ℓ → 0 * A * (reDelta eps p n j : ℝ) ^ 2 ≤ reDelta eps p n (j + 1) :=
      fun j _ => by rw [zero_mul, zero_mul]; exact Nat.cast_nonneg _
    have hcutℓ : 2 ^ (ℓ + 1) * Real.log (2 / a * A) ≤ 1 / 2 * Real.log n := by
      have h2 : (2 : ℝ) ^ (ℓ + 1) ≤ 2 ^ (ℓ₀ + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have := mul_le_mul_of_nonneg_right h2 hlogbA
      linarith
    have hsq : A * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ Real.sqrt n := by
      have := dexp_mul_sq_le_sqrt (Δ := fun j => (reDelta eps p n j : ℝ)) (a := 0)
        (b := 2 / a) (L := ℓ) le_rfl hA hb (by simp) hlo0 hup hnpos le_rfl hcutℓ
      rw [Real.sqrt_eq_rpow]
      exact this
    have hΔ : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
    -- the layer is in the noise regime: `Δ_ℓ² ≤ A Δ_ℓ² ≤ √n`
    have hD : (reDelta eps p n ℓ : ℝ) ≤ Dn := by
      have h1 : (reDelta eps p n ℓ : ℝ) ^ 2 ≤ Real.sqrt n :=
        (le_mul_of_one_le_left (sq_nonneg _) hA).trans hsq
      have h2 : (reDelta eps p n ℓ : ℝ) ≤ Real.sqrt (Real.sqrt n) :=
        (Real.le_sqrt (by linarith) (Real.sqrt_nonneg _)).2 h1
      linarith
    have hcov : (n : ℝ) ≤ (reSize eps p n ℓ : ℝ) * reDelta eps p n ℓ := by
      exact_mod_cast (re_cover heps hn ℓ).2
    have key : Real.sqrt n * ((reDelta eps p n ℓ : ℝ) * A) ≤ reSize eps p n ℓ := by
      have h1 : Real.sqrt n * ((reDelta eps p n ℓ : ℝ) * A) * reDelta eps p n ℓ ≤
          (reSize eps p n ℓ : ℝ) * reDelta eps p n ℓ := by
        calc Real.sqrt n * ((reDelta eps p n ℓ : ℝ) * A) * reDelta eps p n ℓ
            = Real.sqrt n * (A * (reDelta eps p n ℓ : ℝ) ^ 2) := by ring
          _ ≤ Real.sqrt n * Real.sqrt n := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
          _ = n := Real.mul_self_sqrt hnpos.le
          _ ≤ (reSize eps p n ℓ : ℝ) * reDelta eps p n ℓ := hcov
      exact le_of_mul_le_mul_right h1 (by linarith)
    have hmbar : Real.sqrt n ≤ reMbar eps p n A ℓ := by
      unfold reMbar
      rw [le_div_iff₀ (mul_pos (by linarith) (by linarith))]
      exact key
    exact ⟨hD, by linarith⟩

/-- **Lower bound** (eq:re-cutoff-lower, noise-regime version).  With the lower bracket only
    on noise-regime layers, `n^{1/4} ≤ Dn`, `τ ≤ √n` and
    `2 ^ (ℓ₀ + 1) log ((2 / a) A) ≤ log n / 2`: `ℓ₀ + 1 < H`. -/
theorem lt_kreHeight (heps : 1 ≤ eps) (hn : 1 ≤ n) {A a t Dn : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn)
    (hlo : ∀ ℓ, (reDelta eps p n ℓ : ℝ) ≤ Dn →
      a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hsqrt : 4 * t / a ≤ Real.sqrt n) {ℓ₀ : ℕ}
    (hcut : 2 ^ (ℓ₀ + 1) * Real.log (2 / a * A) ≤ Real.log n / 2) :
    ℓ₀ + 1 < reHeight eps p n := by
  have hconc :=
    kreMbar_conc_of_bootstrap heps hn ha ha1 ht hA hDn hlo hsqrt hcut ℓ₀ le_rfl
  have h2 := (re_compress_upper heps hn ha ht hA (hlo ℓ₀ hconc.1) hconc.2).2.2
  exact (lt_reHeight_iff heps hn (by omega)).2 h2

/-- **Lower bound, log form** (`thm:heightKre`, lower half, deterministic part).  With the
    lower bracket `a mbar_ℓ - t ≤ M_{ℓ+1}` only on the noise-regime layers `Δ_ℓ ≤ Dn`,
    `n^{1/4} ≤ Dn` and `τ ≤ √n`: `log₂ (log n / (2 log ((2 / a) A))) < H`. -/
theorem logb_lt_kreHeight (heps : 1 ≤ eps) (hn : 1 ≤ n) {A a t Dn : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hDn : Real.sqrt (Real.sqrt n) ≤ Dn)
    (hlo : ∀ ℓ, (reDelta eps p n ℓ : ℝ) ≤ Dn →
      a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hsqrt : 4 * t / a ≤ Real.sqrt n) :
    Real.logb 2 (Real.log n / (2 * Real.log (2 / a * A))) < reHeight eps p n := by
  set X := Real.log n / (2 * Real.log (2 / a * A)) with hX
  have hb : 2 ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  have hbA : 1 < 2 / a * A := by nlinarith
  have hlbA : 0 < Real.log (2 / a * A) := Real.log_pos hbA
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hX0 : 0 ≤ X := div_nonneg (Real.log_nonneg hn1) (by linarith)
  have hH1 : (1 : ℝ) ≤ reHeight eps p n := by exact_mod_cast one_le_reHeight (p := p) heps hn
  rcases lt_or_ge X 2 with hX2 | hX2
  · have : Real.logb 2 X < 1 := by
      rcases hX0.eq_or_lt with h0 | h0
      · rw [← h0, Real.logb_zero]; norm_num
      · rw [Real.logb_lt_iff_lt_rpow one_lt_two h0, Real.rpow_one]; exact hX2
    linarith
  · have hl1 : 1 ≤ Real.logb 2 X := by
      rw [Real.le_logb_iff_rpow_le one_lt_two (by linarith), Real.rpow_one]; exact hX2
    set k := ⌊Real.logb 2 X⌋₊ with hk
    have hk1 : 1 ≤ k := Nat.le_floor (by simpa using hl1)
    have hkX : (2 : ℝ) ^ k ≤ X := by
      have h1 : (k : ℝ) ≤ Real.logb 2 X := Nat.floor_le (by linarith)
      calc (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm
        _ ≤ (2 : ℝ) ^ (Real.logb 2 X) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        _ = X := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
    have hcut : 2 ^ (k - 1 + 1) * Real.log (2 / a * A) ≤ Real.log n / 2 := by
      rw [Nat.sub_add_cancel hk1]
      calc (2 : ℝ) ^ k * Real.log (2 / a * A) ≤ X * Real.log (2 / a * A) :=
            mul_le_mul_of_nonneg_right hkX hlbA.le
        _ = Real.log n / 2 := by
          rw [hX, div_mul_eq_mul_div, mul_div_mul_right _ _ hlbA.ne']
    have hlt := lt_kreHeight heps hn ha ha1 ht hA hDn hlo hsqrt hcut
    rw [Nat.sub_add_cancel hk1] at hlt
    have hk2 : (k : ℝ) + 1 ≤ reHeight eps p n := by exact_mod_cast hlt
    have := Nat.lt_floor_add_one (Real.logb 2 X)
    linarith

end Run

end

end PGM
