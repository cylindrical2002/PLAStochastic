import PLAStochastic.Index.Algorithm.RankHierarchy
import PLAStochastic.Index.Algorithm.HeightAsymptotics

/-!
# Height of ALG-RE from per-layer count brackets

Deterministic part of `thm:heightRE` (`proofs/proofG_rank_core.tex`).  Write
`N_ℓ = reSize`, `Δ_ℓ = reDelta`, `M_{ℓ+1} = reSegs` and
`mbar_ℓ = N_ℓ / (Δ_ℓ A)` (`reMbar`).  The good event is replaced by its pathwise
content, the count bracket `a mbar_ℓ - t ≤ M_{ℓ+1} ≤ B mbar_ℓ + t` with fixed
constants `0 < a ≤ 1 ≤ B`, `t ≥ 1`; `τ = 4 t / a` is the concentration threshold.

* Compression: if `τ ≤ mbar_ℓ` then `Δ_{ℓ+1} ≤ (2 / a) A Δ_ℓ²`, and if also `4 B ≤ A`,
  `A / (4 B) Δ_ℓ² ≤ Δ_{ℓ+1}`; the layer and its successor are nontrivial.
* Upper bound: `H ≤ log₂ (log n / log (A / (4 B))) + log₂ (2 (B τ + t)) + 4`.
* Lower bound: if `2 ^ (ℓ₀ + 1) log ((2 / a) A) ≤ (log n) / 2` and `τ ≤ √n` then
  `ℓ₀ + 1 < H`; in log form `log₂ (log n / (2 log ((2 / a) A))) < H`.

Nothing here is probabilistic.
-/

namespace PGM

noncomputable section

/-! ## Arithmetic of one compression step -/

/-- In the concentration range `4 t / a ≤ x` the lower bracket `a x - t ≤ M` tightens
    to `a x / 2 ≤ M`, and `3 t ≤ M`. -/
theorem conc_bracket_lo {a t x M : ℝ} (ha : 0 < a) (ht : 0 ≤ t)
    (hx : 4 * t / a ≤ x) (hlo : a * x - t ≤ M) : a * x / 2 ≤ M ∧ 3 * t ≤ M := by
  have h4 : 4 * t ≤ a * x := by
    have := (div_le_iff₀ ha).1 hx
    linarith
  exact ⟨by linarith, by linarith⟩

/-- In the concentration range `4 t / a ≤ x` the upper bracket `M ≤ B x + t` tightens
    to `M ≤ 2 B x`. -/
theorem conc_bracket_up {a B t x M : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B)
    (ht : 0 ≤ t) (hx : 4 * t / a ≤ x) (hup : M ≤ B * x + t) : M ≤ 2 * B * x := by
  have h4 : 4 * t ≤ a * x := by
    have := (div_le_iff₀ ha).1 hx
    linarith
  have hx0 : 0 ≤ x := le_trans (div_nonneg (by linarith) ha.le) hx
  have hax : a * x ≤ B * x := mul_le_mul_of_nonneg_right (by linarith) hx0
  linarith

/-- Upper half of one step: `d = ⌊N / M⌋` with `N = x Δ A` and `a x / 2 ≤ M` has
    `d Δ ≤ (2 / a) A Δ²`. -/
theorem step_mul_le {N M : ℕ} {Δ A a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hΔ : 0 ≤ Δ)
    (hN : (N : ℝ) = x * (Δ * A)) (hM : a * x / 2 ≤ M) :
    ((N / M : ℕ) : ℝ) * Δ ≤ 2 / a * A * Δ ^ 2 := by
  set d : ℝ := ((N / M : ℕ) : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hdM : d * M ≤ N := by
    rw [hd]; exact_mod_cast Nat.div_mul_le_self N M
  have h1 : x * (d * a / 2) ≤ x * (Δ * A) := by
    calc x * (d * a / 2) = d * (a * x / 2) := by ring
      _ ≤ d * M := mul_le_mul_of_nonneg_left hM hd0
      _ ≤ N := hdM
      _ = x * (Δ * A) := hN
  have h2 : d * a / 2 ≤ Δ * A := le_of_mul_le_mul_left h1 hx
  have h3 : d ≤ 2 / a * A * Δ := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ ha]
    linarith
  calc d * Δ ≤ (2 / a * A * Δ) * Δ := mul_le_mul_of_nonneg_right h3 hΔ
    _ = 2 / a * A * Δ ^ 2 := by ring

/-- Lower half of one step: `d = ⌊N / M⌋` with `N = x Δ A`, `M ≤ 2 B x` and
    `4 B ≤ Δ A` has `A / (4 B) Δ² ≤ d Δ`. -/
theorem le_step_mul {N M : ℕ} {Δ A B x : ℝ} (hM0 : 0 < M) (hB : 0 < B) (hx : 0 < x)
    (hΔ : 0 ≤ Δ) (hN : (N : ℝ) = x * (Δ * A)) (hM : (M : ℝ) ≤ 2 * B * x)
    (hΔA : 4 * B ≤ Δ * A) :
    A / (4 * B) * Δ ^ 2 ≤ ((N / M : ℕ) : ℝ) * Δ := by
  set d : ℝ := ((N / M : ℕ) : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hlt : (N : ℝ) < d * M + M := by
    rw [hd]; exact_mod_cast Nat.lt_div_mul_add hM0
  have h1 : x * (Δ * A) < x * (2 * B * d + 2 * B) := by
    calc x * (Δ * A) = N := hN.symm
      _ < d * M + M := hlt
      _ = (d + 1) * M := by ring
      _ ≤ (d + 1) * (2 * B * x) := mul_le_mul_of_nonneg_left hM (by linarith)
      _ = x * (2 * B * d + 2 * B) := by ring
  have h2 : Δ * A < 2 * B * d + 2 * B := lt_of_mul_lt_mul_left h1 hx.le
  have h3 : Δ * A ≤ 4 * B * d := by linarith
  have h4 : A * Δ / (4 * B) ≤ d := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  calc A / (4 * B) * Δ ^ 2 = A * Δ / (4 * B) * Δ := by ring
    _ ≤ d * Δ := mul_le_mul_of_nonneg_right h4 hΔ

/-! ## The mean count of a layer -/

/-- `mbar_ℓ = N_ℓ / (Δ_ℓ A)`, the mean segment count of layer `ℓ` (TeX `\bmean_\ell`). -/
def reMbar (eps : ℝ) (p : ℕ → ℝ) (n : ℕ) (A : ℝ) (ℓ : ℕ) : ℝ :=
  (reSize eps p n ℓ : ℝ) / ((reDelta eps p n ℓ : ℝ) * A)

section Run

variable {eps : ℝ} {p : ℕ → ℝ} {n : ℕ} {A a B t : ℝ}

theorem reMbar_pos (heps : 1 ≤ eps) (hn : 1 ≤ n) (hA : 0 < A) (ℓ : ℕ) :
    0 < reMbar eps p n A ℓ := by
  have h1 : (1 : ℝ) ≤ reSize eps p n ℓ := by exact_mod_cast one_le_reSize heps hn ℓ
  have h2 : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  unfold reMbar
  exact div_pos (by linarith) (mul_pos (by linarith) hA)

theorem reSize_eq_reMbar_mul (heps : 1 ≤ eps) (hn : 1 ≤ n) (hA : 0 < A) (ℓ : ℕ) :
    (reSize eps p n ℓ : ℝ) = reMbar eps p n A ℓ * ((reDelta eps p n ℓ : ℝ) * A) := by
  have h2 : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  unfold reMbar
  rw [div_mul_cancel₀ _ (mul_pos (by linarith) hA).ne']

/-- A singleton layer has `mbar = 1 / (Δ A) ≤ 1`. -/
theorem reMbar_le_one_of_reSize_eq_one (heps : 1 ≤ eps) (hn : 1 ≤ n) (hA : 1 ≤ A) {ℓ : ℕ}
    (h1 : reSize eps p n ℓ = 1) : reMbar eps p n A ℓ ≤ 1 := by
  have h2 : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  have h3 : (1 : ℝ) ≤ (reDelta eps p n ℓ : ℝ) * A := by nlinarith
  unfold reMbar
  rw [h1, Nat.cast_one, div_le_one (by linarith)]
  exact h3

/-! ## Compression while the count is concentrated -/

variable (heps : 1 ≤ eps) (hn : 1 ≤ n)
include heps hn

/-- In the concentration range `4 t / a ≤ mbar_ℓ`, the lower count bound alone gives
    `Δ_{ℓ+1} ≤ (2 / a) A Δ_ℓ²`, and both `N_ℓ` and `N_{ℓ+1}` are at least `3 t ≥ 2`. -/
theorem re_compress_upper (ha : 0 < a) (ht : 1 ≤ t) (hA : 1 ≤ A) {ℓ : ℕ}
    (hlo : a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hτ : 4 * t / a ≤ reMbar eps p n A ℓ) :
    (reDelta eps p n (ℓ + 1) : ℝ) ≤ 2 / a * A * (reDelta eps p n ℓ : ℝ) ^ 2 ∧
      2 ≤ reSize eps p n ℓ ∧ 2 ≤ reSize eps p n (ℓ + 1) := by
  obtain ⟨h1, h3⟩ := conc_bracket_lo ha (by linarith : (0 : ℝ) ≤ t) hτ hlo
  have hM3 : 3 ≤ reSegs eps p n ℓ := by
    have : (3 : ℝ) ≤ reSegs eps p n ℓ := by linarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · rw [reDelta_succ, Nat.cast_mul]
    exact step_mul_le ha (reMbar_pos heps hn (by linarith) ℓ) (Nat.cast_nonneg _)
      (reSize_eq_reMbar_mul heps hn (by linarith) ℓ) h1
  · exact le_trans (by omega) (reSegs_le_reSize heps ℓ)
  · exact le_trans (by omega) (reSize_succ_bounds heps hn ℓ).1

/-- In the concentration range with `4 B ≤ A`, the upper count bound alone gives
    `A / (4 B) Δ_ℓ² ≤ Δ_{ℓ+1}`. -/
theorem re_compress_lower (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hBA : 4 * B ≤ A) {ℓ : ℕ}
    (hup : (reSegs eps p n ℓ : ℝ) ≤ B * reMbar eps p n A ℓ + t)
    (hτ : 4 * t / a ≤ reMbar eps p n A ℓ) :
    A / (4 * B) * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ reDelta eps p n (ℓ + 1) := by
  have hA : 0 < A := by linarith
  have h2 := conc_bracket_up ha ha1 hB (by linarith : (0 : ℝ) ≤ t) hτ hup
  have hΔ : (1 : ℝ) ≤ reDelta eps p n ℓ := by exact_mod_cast one_le_reDelta heps hn ℓ
  rw [reDelta_succ, Nat.cast_mul]
  exact le_step_mul (one_le_reSegs heps hn ℓ) (by linarith) (reMbar_pos heps hn hA ℓ)
    (by linarith) (reSize_eq_reMbar_mul heps hn hA ℓ) h2 (by nlinarith)

/-- **Compression step** (eq:Deltabracket with constants `A / (4 B)` and `2 / a`):
    if `4 t / a ≤ mbar_ℓ` and `4 B ≤ A`, then
    `A / (4 B) Δ_ℓ² ≤ Δ_{ℓ+1} ≤ (2 / a) A Δ_ℓ²` and `2 ≤ N_ℓ`. -/
theorem re_compress (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hBA : 4 * B ≤ A) {ℓ : ℕ}
    (hlo : a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hup : (reSegs eps p n ℓ : ℝ) ≤ B * reMbar eps p n A ℓ + t)
    (hτ : 4 * t / a ≤ reMbar eps p n A ℓ) :
    A / (4 * B) * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ reDelta eps p n (ℓ + 1) ∧
      (reDelta eps p n (ℓ + 1) : ℝ) ≤ 2 / a * A * (reDelta eps p n ℓ : ℝ) ^ 2 ∧
      2 ≤ reSize eps p n ℓ := by
  have hup' := re_compress_upper heps hn ha ht (by linarith) hlo hτ
  exact ⟨re_compress_lower heps hn ha ha1 hB ht hBA hup hτ, hup'.1, hup'.2.1⟩

/-! ## The first cutoff and the upper bound -/

/-- **Upper bound** (eq:re-cutoff-upper and the top layers of `thm:heightRE`).  Under the
    count bracket on every layer, with `1 < A / (4 B) ≤ n`,
    `H ≤ log₂ (log n / log (A / (4 B))) + log₂ (2 (B τ + t)) + 4`, `τ = 4 t / a`. -/
theorem reHeight_le_of_bracket (ha : 0 < a) (ha1 : a ≤ 1) (hB : 1 ≤ B) (ht : 1 ≤ t)
    (hM : ∀ ℓ, a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ ∧
      (reSegs eps p n ℓ : ℝ) ≤ B * reMbar eps p n A ℓ + t)
    (hq : 1 < A / (4 * B)) (hqn : A / (4 * B) ≤ n) :
    (reHeight eps p n : ℝ) ≤ Real.logb 2 (Real.log n / Real.log (A / (4 * B))) +
      Real.logb 2 (2 * (B * (4 * t / a) + t)) + 4 := by
  classical
  have hB0 : 0 < B := by linarith
  have hBA : 4 * B ≤ A := by
    have := (lt_div_iff₀ (by linarith : (0 : ℝ) < 4 * B)).1 hq
    linarith
  have hA : 1 ≤ A := by linarith
  have hτ4 : 4 ≤ 4 * t / a := by
    rw [le_div_iff₀ ha]; linarith
  -- the first cutoff layer `L`
  have hex : ∃ ℓ, reMbar eps p n A ℓ < 4 * t / a :=
    ⟨reHeight eps p n, by
      have := reMbar_le_one_of_reSize_eq_one heps hn hA (reSize_reHeight (p := p) heps hn)
      linarith⟩
  obtain ⟨L, hL, hbefore⟩ : ∃ L, reMbar eps p n A L < 4 * t / a ∧
      ∀ ℓ < L, 4 * t / a ≤ reMbar eps p n A ℓ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun ℓ hℓ => not_lt.1 (Nat.find_min hex hℓ)⟩
  have hlo : ∀ ℓ, ℓ < L →
      A / (4 * B) * 1 * (reDelta eps p n ℓ : ℝ) ^ 2 ≤ reDelta eps p n (ℓ + 1) := by
    intro ℓ hℓ
    rw [mul_one]
    exact re_compress_lower heps hn ha ha1 hB ht hBA (hM ℓ).2 (hbefore ℓ hℓ)
  have hbelow : ∀ ℓ, ℓ < L → (reDelta eps p n ℓ : ℝ) < n := by
    intro ℓ hℓ
    have h2 := (re_compress_upper heps hn ha ht hA (hM ℓ).1 (hbefore ℓ hℓ)).2.1
    exact_mod_cast reDelta_lt heps hn h2
  have hLle := dexp_cutoff_le_logb (Δ := fun ℓ => (reDelta eps p n ℓ : ℝ))
    (a := A / (4 * B)) (A := 1) (by rwa [mul_one]) (by simp) hlo (by rwa [mul_one]) hbelow
  rw [mul_one] at hLle
  -- the top layers: `N_{L+1} ≤ 2 M_{L+1} ≤ 2 (B τ + t)`, then halving
  have hML : (reSegs eps p n L : ℝ) ≤ B * (4 * t / a) + t := by
    have h1 := (hM L).2
    have h2 : B * reMbar eps p n A L ≤ B * (4 * t / a) :=
      mul_le_mul_of_nonneg_left hL.le hB0.le
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

/-! ## Lower bound by the exact lattice count -/

/-- **Bootstrap** (eq:re-bootstrap).  Using only the lower half of the bracket: if
    `2 ^ (ℓ₀ + 1) log ((2 / a) A) ≤ log n / 2` and `τ ≤ √n`, then every layer `ℓ ≤ ℓ₀` is
    in the concentration range `τ ≤ mbar_ℓ`, `τ = 4 t / a`. -/
theorem reMbar_conc_of_bootstrap (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hlo : ∀ ℓ, a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hsqrt : 4 * t / a ≤ Real.sqrt n) {ℓ₀ : ℕ}
    (hcut : 2 ^ (ℓ₀ + 1) * Real.log (2 / a * A) ≤ Real.log n / 2) :
    ∀ ℓ ≤ ℓ₀, 4 * t / a ≤ reMbar eps p n A ℓ := by
  have hb : 1 ≤ 2 / a := by rw [le_div_iff₀ ha]; linarith
  have hbA : 1 ≤ 2 / a * A := one_le_mul_of_one_le_of_one_le hb hA
  have hlogbA : 0 ≤ Real.log (2 / a * A) := Real.log_nonneg hbA
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | _ ℓ ih =>
    intro hℓ
    have hup : ∀ j, j < ℓ →
        (reDelta eps p n (j + 1) : ℝ) ≤ 2 / a * A * (reDelta eps p n j : ℝ) ^ 2 :=
      fun j hj => (re_compress_upper heps hn ha ht hA (hlo j) (ih j hj (by omega))).1
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
    linarith

/-- **Lower bound** (eq:re-cutoff-lower).  Using only the lower half of the bracket: if
    `2 ^ (ℓ₀ + 1) log ((2 / a) A) ≤ log n / 2` and `τ ≤ √n`, then `ℓ₀ + 1 < H`. -/
theorem lt_reHeight_of_bracket (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hlo : ∀ ℓ, a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
    (hsqrt : 4 * t / a ≤ Real.sqrt n) {ℓ₀ : ℕ}
    (hcut : 2 ^ (ℓ₀ + 1) * Real.log (2 / a * A) ≤ Real.log n / 2) :
    ℓ₀ + 1 < reHeight eps p n := by
  have hconc := reMbar_conc_of_bootstrap heps hn ha ha1 ht hA hlo hsqrt hcut ℓ₀ le_rfl
  have h2 := (re_compress_upper heps hn ha ht hA (hlo ℓ₀) hconc).2.2
  exact (lt_reHeight_iff heps hn (by omega)).2 h2

/-- **Lower bound, log form**: under the lower half of the bracket and `τ ≤ √n`,
    `log₂ (log n / (2 log ((2 / a) A))) < H`. -/
theorem logb_lt_reHeight_of_bracket (ha : 0 < a) (ha1 : a ≤ 1) (ht : 1 ≤ t) (hA : 1 ≤ A)
    (hlo : ∀ ℓ, a * reMbar eps p n A ℓ - t ≤ reSegs eps p n ℓ)
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
    have hlt := lt_reHeight_of_bracket heps hn ha ha1 ht hA hlo hsqrt hcut
    rw [Nat.sub_add_cancel hk1] at hlt
    have hk2 : (k : ℝ) + 1 ≤ reHeight eps p n := by exact_mod_cast hlt
    have := Nat.lt_floor_add_one (Real.logb 2 X)
    linarith

end Run

end

end PGM
