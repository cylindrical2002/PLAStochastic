import PLAStochastic.Index.GRE.Exact.GoodEvent
import PLAStochastic.Index.GRE.PreciseHeightDefs

/-!
# Step 5 of `thm:GRE`: the window arithmetic and the growth conditions

With `Λ = log n`, `ℓ = log ε`, `b = μ₀² / σ₀²` and `A = b ε²`, the three `log₂` thresholds of
`reHeight_window_of_greGood` are `log₂ (X' / q' + 1)` with

* `X' = Λ - log τ`, `q' = log ((2 / aRE) A)` (lower side of the cutoff),
* `X' = Λ`, `q' = log (A / 512)` (upper side of the cutoff),
* `X' = Λ + 2 log (2 Λ)`, `q' = log (A / 512)` (the top layer),

and `y = greY c n ε = log₂ (Λ / ρ + 1)` with `ρ = log (c ε²)`.  Each `q' - ρ` is a constant and
each `X' + q' - (Λ + ρ)` is `O(log Λ)`, so `abs_logb_sub_le_of_err` puts every threshold within
`w = greW K n ε = K (1 / ℓ + log Λ / Λ)` of `y`, with the explicit `K = greK μ₀ σ₀ c`.

`GREParams` collects the fixed-parameter hypotheses; `eventually_GREParams` shows that they hold
eventually along `n → ∞`, `ε → ∞`, `log ε = o(log n)`.  `GREParams.window` is the pathwise
statement on `greGood` and `GREParams.integral` the expectation statement, where the height is at
most `log₂ n + 1` off the good event.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ## Comparing `log₂` thresholds -/

/-- `|log₂ (1 + δ)| ≤ 3 |δ|` for `|δ| ≤ 1 / 2`. -/
private theorem abs_logb_one_add_le {δ : ℝ} (hδ : |δ| ≤ 1 / 2) : |Real.logb 2 (1 + δ)| ≤ 3 * |δ| := by
  have hδ1 := neg_abs_le δ
  have hδ2 := le_abs_self δ
  have hpos : 0 < 1 + δ := by linarith
  have hup : Real.log (1 + δ) ≤ |δ| := by
    have := Real.log_le_sub_one_of_pos hpos; linarith
  have hlo : -(2 * |δ|) ≤ Real.log (1 + δ) := by
    have h := Real.one_sub_inv_le_log_of_pos hpos
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    rw [e] at h
    have : -(2 * |δ|) ≤ δ / (1 + δ) := by
      rw [le_div_iff₀ hpos]
      rcases le_or_gt 0 δ with h0 | h0
      · rw [abs_of_nonneg h0]; nlinarith
      · rw [abs_of_neg h0]; nlinarith
    linarith
  have hl2 : 2 / 3 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl0 : 0 < Real.log 2 := by linarith
  have hk : 0 ≤ |δ| * (Real.log 2 - 2 / 3) := mul_nonneg (abs_nonneg δ) (by linarith)
  rw [Real.logb, abs_div, abs_of_pos hl0, div_le_iff₀ hl0, abs_le]
  constructor <;> nlinarith [abs_nonneg δ]

/-- Comparison of two thresholds `log₂ (X / q + 1)`: the difference is at most three times the
relative changes of `X + q` and of `q`. -/
private theorem abs_logb_div_add_one_sub_le {X q X' q' : ℝ} (hX : 0 ≤ X) (hq : 0 < q) (hq' : 0 < q')
    (h1 : |X' + q' - (X + q)| / (X + q) ≤ 1 / 2) (h2 : |q' - q| / q ≤ 1 / 2) :
    |Real.logb 2 (X' / q' + 1) - Real.logb 2 (X / q + 1)| ≤
      3 * (|X' + q' - (X + q)| / (X + q)) + 3 * (|q' - q| / q) := by
  have hXq : 0 < X + q := by linarith
  set δ₁ := (X' + q' - (X + q)) / (X + q) with hδ₁
  set δ₂ := (q' - q) / q with hδ₂
  have hd1 : |δ₁| = |X' + q' - (X + q)| / (X + q) := by rw [hδ₁, abs_div, abs_of_pos hXq]
  have hd2 : |δ₂| = |q' - q| / q := by rw [hδ₂, abs_div, abs_of_pos hq]
  have hb1 := abs_logb_one_add_le (hd1 ▸ h1)
  have hb2 := abs_logb_one_add_le (hd2 ▸ h2)
  have hp1 : 0 < 1 + δ₁ := by have := neg_abs_le δ₁; rw [hd1] at this; linarith
  have hp2 : 0 < 1 + δ₂ := by have := neg_abs_le δ₂; rw [hd2] at this; linarith
  have hXq1 : 0 < X / q + 1 := by positivity
  have e1 : X' / q' + 1 = (X / q + 1) * (1 + δ₁) / (1 + δ₂) := by
    have f1 : 1 + δ₁ = (X' + q') / (X + q) := by rw [hδ₁]; field_simp; ring
    have f2 : 1 + δ₂ = q' / q := by rw [hδ₂]; field_simp; ring
    have f3 : X / q + 1 = (X + q) / q := by field_simp
    rw [f1, f2, f3, div_add_one hq'.ne']
    field_simp
  rw [e1, Real.logb_div (by positivity) hp2.ne', Real.logb_mul hXq1.ne' hp1.ne', ← hd1, ← hd2]
  calc |Real.logb 2 (X / q + 1) + Real.logb 2 (1 + δ₁) - Real.logb 2 (1 + δ₂) -
        Real.logb 2 (X / q + 1)| = |Real.logb 2 (1 + δ₁) - Real.logb 2 (1 + δ₂)| := by
        ring_nf
    _ ≤ |Real.logb 2 (1 + δ₁)| + |Real.logb 2 (1 + δ₂)| := abs_sub _ _
    _ ≤ 3 * |δ₁| + 3 * |δ₂| := add_le_add hb1 hb2

/-- A threshold `log₂ (X' / q' + 1)` is within `w` of `log₂ (Λ / ρ + 1)` when
`|X' + q' - (Λ + ρ)| ≤ e₁ log Λ`, `|q' - ρ| ≤ e₂`, `ℓ ≤ ρ` and
`3 e₁ log Λ / Λ + 3 e₂ / ℓ ≤ w ≤ 3 / 2`. -/
private theorem abs_logb_sub_le_of_err {Λ ρ ℓ X' q' e₁ e₂ w : ℝ} (hΛ : 0 < Λ) (hℓ : 0 < ℓ)
    (hℓρ : ℓ ≤ ρ) (hq' : 0 < q') (he₁ : |X' + q' - (Λ + ρ)| ≤ e₁ * Real.log Λ)
    (he₂ : |q' - ρ| ≤ e₂) (hw : 3 * (e₁ * Real.log Λ / Λ) + 3 * (e₂ / ℓ) ≤ w)
    (hw1 : w ≤ 3 / 2) :
    |Real.logb 2 (X' / q' + 1) - Real.logb 2 (Λ / ρ + 1)| ≤ w := by
  have hρ : 0 < ρ := by linarith
  have hr1 : |X' + q' - (Λ + ρ)| / (Λ + ρ) ≤ e₁ * Real.log Λ / Λ := by
    calc |X' + q' - (Λ + ρ)| / (Λ + ρ) ≤ |X' + q' - (Λ + ρ)| / Λ := by
          gcongr; linarith
      _ ≤ e₁ * Real.log Λ / Λ := by gcongr
  have hr2 : |q' - ρ| / ρ ≤ e₂ / ℓ := by
    calc |q' - ρ| / ρ ≤ |q' - ρ| / ℓ := by gcongr
      _ ≤ e₂ / ℓ := by gcongr
  have h0 : 0 ≤ |X' + q' - (Λ + ρ)| / (Λ + ρ) := by positivity
  have h0' : 0 ≤ |q' - ρ| / ρ := by positivity
  have := abs_logb_div_add_one_sub_le (X' := X') hΛ.le hρ hq' (by linarith) (by linarith)
  linarith

/-! ## The constant and the fixed-parameter hypotheses -/

/-- The window constant `K` of `thm:GRE` for the gap law `(μ, σ)` and the constant `c`:
three times `|d₁| + |d₂| + |log κ_τ| + 4`, where `d₁ = log ((2 / aRE) μ² / σ²) - log c`,
`d₂ = log (μ² / (512 σ²)) - log c` and `τ ≤ κ_τ log n`. -/
def greK (μ σ c : ℝ) : ℝ :=
  3 * (|Real.log (2 / aRE * (μ ^ 2 / σ ^ 2)) - Real.log c| +
    |Real.log (μ ^ 2 / σ ^ 2 / 512) - Real.log c| + |Real.log (4 * (8 / cRE + 2) / aRE)| + 4)

private theorem twelve_le_greK (μ σ c : ℝ) : 12 ≤ greK μ σ c := by
  unfold greK
  have := abs_nonneg (Real.log (2 / aRE * (μ ^ 2 / σ ^ 2)) - Real.log c)
  have := abs_nonneg (Real.log (μ ^ 2 / σ ^ 2 / 512) - Real.log c)
  have := abs_nonneg (Real.log (4 * (8 / cRE + 2) / aRE))
  linarith

/-- The fixed-parameter hypotheses of `thm:GRE`; all hold eventually along HEIGHT
(`eventually_GREParams`). -/
structure GREParams (μ₀ σ₀ κ₀ c K : ℝ) (n : ℕ) (eps : ℝ) : Prop where
  eps0 : epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3) ≤ eps
  n3 : 3 ≤ n
  loglog : 1 ≤ Real.log (Real.log n)
  logeps : 1 + |Real.log c| + |Real.log (2 / aRE * (μ₀ ^ 2 / σ₀ ^ 2))| +
    |Real.log (μ₀ ^ 2 / σ₀ ^ 2 / 512)| ≤ Real.log eps
  K_ge : greK μ₀ σ₀ c ≤ K
  w_le : greW K n eps ≤ 1
  sqrt_ge : 2 * (128 * (4 * (8 / cRE + 2) / aRE) + (8 / cRE + 2)) * Real.log n ^ 2 ≤
    Real.sqrt n
  A_le : 2 * Real.log eps + Real.log (μ₀ ^ 2 / σ₀ ^ 2) ≤ Real.log n

section Params

variable {μ₀ σ₀ κ₀ c K : ℝ} {n : ℕ} {eps : ℝ}

/-- `log (r ε²) = log r + 2 log ε`. -/
private theorem log_mul_sq {r eps : ℝ} (hr : 0 < r) (heps : 0 < eps) :
    Real.log (r * eps ^ 2) = Real.log r + 2 * Real.log eps := by
  rw [Real.log_mul hr.ne' (by positivity), Real.log_pow]
  push_cast
  ring

/-- Elementary consequences of `GREParams`. -/
theorem GREParams.basic (hp : GREParams μ₀ σ₀ κ₀ c K n eps) (hc : 0 < c) :
    1 ≤ eps ∧ (3 : ℝ) ≤ n ∧ 2 ≤ Real.log n ∧ 1 ≤ Real.log eps ∧
      Real.log eps ≤ Real.log (c * eps ^ 2) ∧ Real.log (Real.log n) / Real.log n ≤ 1 := by
  have heps : 1 ≤ eps := le_trans (one_le_epsZero _ _) hp.eps0
  have hN : (3 : ℝ) ≤ n := by exact_mod_cast hp.n3
  have hΛ0 : 0 < Real.log n := Real.log_pos (by linarith)
  have hΛe : Real.exp 1 ≤ Real.log n := by
    rw [← Real.exp_log hΛ0]; exact Real.exp_le_exp.2 hp.loglog
  have hΛ2 : 2 ≤ Real.log n := by have := Real.add_one_le_exp 1; linarith
  have hℓ := hp.logeps
  have a1 := abs_nonneg (Real.log (2 / aRE * (μ₀ ^ 2 / σ₀ ^ 2)))
  have a2 := abs_nonneg (Real.log (μ₀ ^ 2 / σ₀ ^ 2 / 512))
  have a3 := neg_abs_le (Real.log c)
  have a4 := abs_nonneg (Real.log c)
  refine ⟨heps, hN, hΛ2, by linarith, ?_, ?_⟩
  · rw [log_mul_sq hc (by linarith)]; linarith
  · rw [div_le_one hΛ0]
    have := Real.log_le_sub_one_of_pos hΛ0
    linarith

/-- The real arithmetic of Step 5: with `ρ = lc + 2 ℓ`, the three thresholds are within
`w = K (1 / ℓ + log Λ / Λ)` of `log₂ (Λ / ρ + 1)`. -/
private theorem gre_thresholds {Λ ℓ lc l₁ l₂ lτ lκ K w : ℝ} (hΛ : 0 < Λ) (hLL : 1 ≤ Real.log Λ)
    (hℓ : 1 + |lc| + |l₁| + |l₂| ≤ ℓ) (hτ0 : 0 ≤ lτ) (hτ : lτ ≤ |lκ| + Real.log Λ)
    (hK : 3 * (|l₁ - lc| + |l₂ - lc| + |lκ| + 4) ≤ K) (hw : w = K * (1 / ℓ + Real.log Λ / Λ))
    (hw1 : w ≤ 1) :
    |Real.logb 2 ((Λ - lτ) / (l₁ + 2 * ℓ) + 1) - Real.logb 2 (Λ / (lc + 2 * ℓ) + 1)| ≤ w ∧
      |Real.logb 2 (Λ / (l₂ + 2 * ℓ) + 1) - Real.logb 2 (Λ / (lc + 2 * ℓ) + 1)| ≤ w ∧
      |Real.logb 2 ((Λ + 2 * Real.log (2 * Λ)) / (l₂ + 2 * ℓ) + 1) -
        Real.logb 2 (Λ / (lc + 2 * ℓ) + 1)| ≤ w := by
  have hLL0 : 0 ≤ Real.log Λ / Λ := div_nonneg (by linarith) hΛ.le
  have a1 := abs_nonneg lc
  have a2 := abs_nonneg l₁
  have a3 := abs_nonneg l₂
  have b1 := neg_abs_le lc
  have b2 := neg_abs_le l₁
  have b3 := neg_abs_le l₂
  have hℓ0 : 0 < ℓ := by linarith
  have hρ : ℓ ≤ lc + 2 * ℓ := by linarith
  have hq₁ : 0 < l₁ + 2 * ℓ := by linarith
  have hq₂ : 0 < l₂ + 2 * ℓ := by linarith
  have hKLL : ∀ e₁ e₂ : ℝ, 3 * e₁ ≤ K → 3 * e₂ ≤ K →
      3 * (e₁ * Real.log Λ / Λ) + 3 * (e₂ / ℓ) ≤ w := by
    intro e₁ e₂ h1 h2
    rw [hw]
    have i1 : 3 * (e₁ * Real.log Λ / Λ) ≤ K * (Real.log Λ / Λ) := by
      rw [show 3 * (e₁ * Real.log Λ / Λ) = 3 * e₁ * (Real.log Λ / Λ) by ring]
      exact mul_le_mul_of_nonneg_right h1 hLL0
    have i2 : 3 * (e₂ / ℓ) ≤ K * (1 / ℓ) := by
      rw [show 3 * (e₂ / ℓ) = 3 * e₂ * (1 / ℓ) by ring]
      exact mul_le_mul_of_nonneg_right h2 (by positivity)
    calc 3 * (e₁ * Real.log Λ / Λ) + 3 * (e₂ / ℓ) ≤ K * (Real.log Λ / Λ) + K * (1 / ℓ) :=
          add_le_add i1 i2
      _ = K * (1 / ℓ + Real.log Λ / Λ) := by ring
  have hd₁ := abs_nonneg (l₁ - lc)
  have hd₂ := abs_nonneg (l₂ - lc)
  have hκ := abs_nonneg lκ
  have hw' : w ≤ 3 / 2 := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlog20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have m1 : 0 ≤ |l₁ - lc| * (Real.log Λ - 1) := mul_nonneg hd₁ (by linarith)
  have m2 : 0 ≤ |l₂ - lc| * (Real.log Λ - 1) := mul_nonneg hd₂ (by linarith)
  have m3 : 0 ≤ |lκ| * (Real.log Λ - 1) := mul_nonneg hκ (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · refine abs_logb_sub_le_of_err (e₁ := |l₁ - lc| + |lκ| + 1) (e₂ := |l₁ - lc|) hΛ hℓ0 hρ hq₁
      ?_ ?_ (hKLL _ _ (by linarith) (by linarith)) hw'
    · rw [show Λ - lτ + (l₁ + 2 * ℓ) - (Λ + (lc + 2 * ℓ)) = (l₁ - lc) - lτ by ring]
      calc |l₁ - lc - lτ| ≤ |l₁ - lc| + |lτ| := abs_sub _ _
        _ ≤ (|l₁ - lc| + |lκ| + 1) * Real.log Λ := by rw [abs_of_nonneg hτ0]; nlinarith
    · rw [show l₁ + 2 * ℓ - (lc + 2 * ℓ) = l₁ - lc by ring]
  · refine abs_logb_sub_le_of_err (e₁ := |l₂ - lc|) (e₂ := |l₂ - lc|) hΛ hℓ0 hρ hq₂
      ?_ ?_ (hKLL _ _ (by linarith) (by linarith)) hw'
    · rw [show Λ + (l₂ + 2 * ℓ) - (Λ + (lc + 2 * ℓ)) = l₂ - lc by ring]
      nlinarith
    · rw [show l₂ + 2 * ℓ - (lc + 2 * ℓ) = l₂ - lc by ring]
  · refine abs_logb_sub_le_of_err (e₁ := 4 + |l₂ - lc|) (e₂ := |l₂ - lc|) hΛ hℓ0 hρ hq₂
      ?_ ?_ (hKLL _ _ (by linarith) (by linarith)) hw'
    · rw [Real.log_mul (by norm_num) hΛ.ne', show Λ + 2 * (Real.log 2 + Real.log Λ) +
        (l₂ + 2 * ℓ) - (Λ + (lc + 2 * ℓ)) = 2 * Real.log 2 + 2 * Real.log Λ + (l₂ - lc) by ring]
      calc |2 * Real.log 2 + 2 * Real.log Λ + (l₂ - lc)| ≤
          |2 * Real.log 2 + 2 * Real.log Λ| + |l₂ - lc| := abs_add_le _ _
        _ ≤ (4 + |l₂ - lc|) * Real.log Λ := by
          rw [abs_of_nonneg (by linarith)]; nlinarith
    · rw [show l₂ + 2 * ℓ - (lc + 2 * ℓ) = l₂ - lc by ring]

/-- The concentration level `t = tRE (n²) + 1`: `1 ≤ t ≤ (8 / cRE + 2) log n`. -/
private theorem tRE_sq_bounds {n : ℕ} (hn : 1 ≤ n) (hΛ : 1 ≤ Real.log n) :
    1 ≤ (tRE (n ^ 2) : ℝ) + 1 ∧ (tRE (n ^ 2) : ℝ) + 1 ≤ (8 / cRE + 2) * Real.log n := by
  have hcR := cRE_pos
  refine ⟨by have := (Nat.cast_nonneg (tRE (n ^ 2)) : (0 : ℝ) ≤ _); linarith, ?_⟩
  have h1n : (1 : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by omega)
  have h0 : 0 ≤ 4 * Real.log ((n ^ 2 : ℕ) : ℝ) / cRE := by
    have := Real.log_nonneg h1n
    positivity
  have h1 : (tRE (n ^ 2) : ℝ) < 4 * Real.log ((n ^ 2 : ℕ) : ℝ) / cRE + 1 :=
    Nat.ceil_lt_add_one h0
  have e : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * Real.log n := by
    push_cast; rw [Real.log_pow]; push_cast; ring
  rw [e, show 4 * (2 * Real.log n) / cRE = 8 / cRE * Real.log n by ring] at h1
  have h4 : 0 ≤ 8 / cRE := by positivity
  nlinarith

omit mΩ in
/-- **Pathwise window at fixed parameters** (`thm:GRE` (a), (b)) on the good event. -/
theorem GREParams.window (hp : GREParams μ₀ σ₀ κ₀ c K n eps) (hμ : 0 < μ₀) (hσ : 0 < σ₀)
    (hc : 0 < c) {g : ℕ → Ω → ℝ} (x0 : ℝ) {ω : Ω} (hω : ω ∈ greGood eps g μ₀ σ₀ n) :
    (greY c n eps - greW K n eps < reHeight eps (fun s => x0 + ∑ i ∈ range s, g i ω) n ∧
        (reHeight eps (fun s => x0 + ∑ i ∈ range s, g i ω) n : ℝ) ≤
          greY c n eps + 1 + greW K n eps) ∧
      ((∀ m : ℤ, greW K n eps ≤ |greY c n eps - m|) →
        ((reHeight eps (fun s => x0 + ∑ i ∈ range s, g i ω) n : ℕ) : ℤ) =
          ⌈greY c n eps⌉) := by
  obtain ⟨heps, hN, hΛ2, hℓ1, hρℓ, -⟩ := hp.basic hc
  have hn2 : 2 ≤ n := by have := hp.n3; omega
  have heps0 : 0 < eps := by linarith
  have hΛ0 : 0 < Real.log n := by linarith
  have hnR : (0 : ℝ) < n := by linarith
  have ha := aRE_pos
  have hb0 : 0 < μ₀ ^ 2 / σ₀ ^ 2 := by positivity
  have hA : μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 = μ₀ ^ 2 / σ₀ ^ 2 * eps ^ 2 := by ring
  have hA0 : 0 < μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 := by positivity
  have hρ : Real.log (c * eps ^ 2) = Real.log c + 2 * Real.log eps := log_mul_sq hc heps0
  have hqlo : Real.log (2 / aRE * (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2)) =
      Real.log (2 / aRE * (μ₀ ^ 2 / σ₀ ^ 2)) + 2 * Real.log eps := by
    rw [hA, ← mul_assoc, log_mul_sq (r := 2 / aRE * (μ₀ ^ 2 / σ₀ ^ 2)) (by positivity) heps0]
  have hqup : Real.log (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128)) =
      Real.log (μ₀ ^ 2 / σ₀ ^ 2 / 512) + 2 * Real.log eps := by
    rw [hA, show μ₀ ^ 2 / σ₀ ^ 2 * eps ^ 2 / (4 * 128) = μ₀ ^ 2 / σ₀ ^ 2 / 512 * eps ^ 2 by ring,
      log_mul_sq (r := μ₀ ^ 2 / σ₀ ^ 2 / 512) (by positivity) heps0]
  -- the concentration level `t = tRE (n²) + 1` and `τ = 4 t / aRE ≤ κ_τ log n`
  obtain ⟨hT1, hTle⟩ := tRE_sq_bounds (n := n) (by omega) (by linarith)
  have hτ4 : 4 ≤ 4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE := by
    rw [le_div_iff₀ ha]; nlinarith [aRE_le_one]
  have hκτ0 : 0 < 4 * (8 / cRE + 2) / aRE := by have := cRE_pos; positivity
  have hτle : 4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE ≤ 4 * (8 / cRE + 2) / aRE * Real.log n := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right ha]
    linarith
  have hlogτ0 : 0 ≤ Real.log (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE) := Real.log_nonneg (by linarith)
  have hlogτ : Real.log (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE) ≤
      |Real.log (4 * (8 / cRE + 2) / aRE)| + Real.log (Real.log n) := by
    have h := Real.log_le_log (by linarith) hτle
    rw [Real.log_mul hκτ0.ne' hΛ0.ne'] at h
    have := le_abs_self (Real.log (4 * (8 / cRE + 2) / aRE))
    linarith
  -- the three thresholds
  obtain ⟨hE1, hE2, hE3⟩ := gre_thresholds (Λ := Real.log n) (ℓ := Real.log eps)
    (lc := Real.log c) (l₁ := Real.log (2 / aRE * (μ₀ ^ 2 / σ₀ ^ 2)))
    (l₂ := Real.log (μ₀ ^ 2 / σ₀ ^ 2 / 512))
    (lτ := Real.log (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE))
    (lκ := Real.log (4 * (8 / cRE + 2) / aRE)) (w := greW K n eps) hΛ0 hp.loglog hp.logeps
    hlogτ0 hlogτ hp.K_ge rfl hp.w_le
  rw [← hρ, ← hqlo] at hE1
  rw [← hρ, ← hqup] at hE2 hE3
  have hy' : greY c n eps = Real.logb 2 (Real.log n / Real.log (c * eps ^ 2) + 1) := rfl
  rw [← hy'] at hE1 hE2 hE3
  -- `A > 512` and `A ≤ n`
  have hA512 : 4 * 128 < μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 := by
    have hl : 0 < Real.log (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 / (4 * 128)) := by
      rw [hqup]
      have := neg_abs_le (Real.log (μ₀ ^ 2 / σ₀ ^ 2 / 512))
      have := hp.logeps
      have := abs_nonneg (Real.log c)
      have := abs_nonneg (Real.log (2 / aRE * (μ₀ ^ 2 / σ₀ ^ 2)))
      linarith
    have h := (Real.log_pos_iff (by positivity)).1 hl
    rw [lt_div_iff₀ (by norm_num)] at h
    linarith
  have hAn : μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 ≤ n := by
    rw [← Real.log_le_log_iff hA0 hnR, hA, log_mul_sq hb0 heps0]
    have := hp.A_le
    linarith
  -- the Step 1 threshold `θ = √(A n) / log n`
  have hθn : Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) / Real.log n ≤ 2 * n := by
    have h0 : μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n ≤ n * n := mul_le_mul_of_nonneg_right hAn hnR.le
    have h1 : Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) ≤ n :=
      (Real.sqrt_le_sqrt h0).trans_eq (Real.sqrt_mul_self hnR.le)
    rw [div_le_iff₀ hΛ0]
    have h2 : (n : ℝ) * 1 ≤ n * (2 * Real.log n) := mul_le_mul_of_nonneg_left (by linarith) hnR.le
    linarith
  have hθ : 2 * (128 * (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE) + ((tRE (n ^ 2) : ℝ) + 1)) ≤
      Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) / Real.log n := by
    have h1 : Real.sqrt n ≤ Real.sqrt (μ₀ ^ 2 * eps ^ 2 / σ₀ ^ 2 * n) :=
      Real.sqrt_le_sqrt (le_mul_of_one_le_left hnR.le (by linarith))
    have h2 := hp.sqrt_ge
    rw [le_div_iff₀ hΛ0]
    have h3 : 2 * (128 * (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE) + ((tRE (n ^ 2) : ℝ) + 1)) ≤
        2 * (128 * (4 * (8 / cRE + 2) / aRE) + (8 / cRE + 2)) * Real.log n := by
      have : 2 * (128 * (4 * (8 / cRE + 2) / aRE * Real.log n) + (8 / cRE + 2) * Real.log n) =
          2 * (128 * (4 * (8 / cRE + 2) / aRE) + (8 / cRE + 2)) * Real.log n := by ring
      linarith
    calc 2 * (128 * (4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE) + ((tRE (n ^ 2) : ℝ) + 1)) *
          Real.log n ≤
        2 * (128 * (4 * (8 / cRE + 2) / aRE) + (8 / cRE + 2)) * Real.log n * Real.log n :=
          mul_le_mul_of_nonneg_right h3 hΛ0.le
      _ = 2 * (128 * (4 * (8 / cRE + 2) / aRE) + (8 / cRE + 2)) * Real.log n ^ 2 := by ring
      _ ≤ _ := h2.trans h1
  have hτn : 4 * ((tRE (n ^ 2) : ℝ) + 1) / aRE ≤ n := by linarith
  -- `y ≥ 0` and `w > 0`
  have hy : 0 ≤ greY c n eps := by
    rw [hy']
    apply Real.logb_nonneg one_lt_two
    have : 0 ≤ Real.log n / Real.log (c * eps ^ 2) := div_nonneg hΛ0.le (by linarith)
    linarith
  have hw0 : 0 < greW K n eps := by
    have hK := (twelve_le_greK μ₀ σ₀ c).trans hp.K_ge
    have : 0 ≤ Real.log (Real.log n) / Real.log n := div_nonneg (by linarith [hp.loglog]) hΛ0.le
    have : 0 < 1 / Real.log eps := by positivity
    have : 0 < K := by linarith
    unfold greW
    positivity
  exact reHeight_window_of_greGood hμ hσ heps hn2 x0 hω hA512 hθ hθn hτn hy hw0
    (by linarith [(abs_le.1 hE1).1]) (by linarith [(abs_le.1 hE2).2])
    (by linarith [(abs_le.1 hE3).2])

/-- **Expected height at fixed parameters**: the window of `GREParams.window` in expectation,
up to `K / log n` from the complement of the good event. -/
theorem GREParams.integral [IsProbabilityMeasure P] (hp : GREParams μ₀ σ₀ κ₀ c K n eps)
    {g : ℕ → Ω → ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀) {x0 : Ω → ℝ} (hx0 : Measurable x0)
    (hc : 0 < c) :
    greY c n eps - greW K n eps - K / Real.log n ≤
        ∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P ∧
      ∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P ≤
        greY c n eps + 1 + greW K n eps + K / Real.log n ∧
      ((∀ m : ℤ, greW K n eps ≤ |greY c n eps - m|) →
        |∫ ω, (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ) ∂P -
          ⌈greY c n eps⌉| ≤ K / Real.log n) := by
  obtain ⟨heps, hN, hΛ2, hℓ1, hρℓ, -⟩ := hp.basic hc
  have hK12 := twelve_le_greK μ₀ σ₀ c
  have hK := hp.K_ge
  have hn1 : 1 ≤ n := by have := hp.n3; omega
  have hgm := hg.iid.measurable
  set Λ := Real.log n with hΛ
  have hΛ0 : 0 < Λ := by linarith
  set H : Ω → ℝ := fun ω => (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ)
    with hHdef
  have hHm : Measurable H :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
      (measurable_reHeight_partialSum eps n hx0 hgm)
  set E := greGood eps g μ₀ σ₀ n
  have hE : MeasurableSet E := measurableSet_greGood hgm eps μ₀ σ₀ n
  have hδ := measureReal_greGood_compl_le hg hp.eps0 hp.n3
  set δ := 1 / (n : ℝ) ^ 2 + 1 / Λ ^ 2 with hδdef
  have h0 : ∀ ω, 0 ≤ H ω := fun ω => Nat.cast_nonneg _
  have hmax : ∀ ω, H ω ≤ (Nat.log 2 n : ℝ) + 1 := fun ω => by
    simp only [hHdef]
    exact_mod_cast reHeight_le_log (p := fun s => x0 ω + ∑ i ∈ range s, g i ω) heps hn1
  -- `log₂ n + 1 ≤ 3 log n` and `3 log n · δ ≤ 6 / log n`
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hHmax : (Nat.log 2 n : ℝ) + 1 ≤ 3 * Λ := by
    have h1 := Real.natLog_le_logb n 2
    push_cast at h1
    have h2 : Real.logb 2 n ≤ 2 * Λ := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hΛn : Λ ≤ n := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < n by linarith); linarith
  have hδ6 : 3 * Λ * δ ≤ 6 / Λ := by
    rw [hδdef]
    have h1 : Λ / (n : ℝ) ^ 2 ≤ 1 / Λ := by
      rw [div_le_div_iff₀ (by positivity) hΛ0]
      nlinarith
    have h2 : 3 * Λ * (1 / (n : ℝ) ^ 2 + 1 / Λ ^ 2) = 3 * (Λ / (n : ℝ) ^ 2) + 3 / Λ := by
      field_simp
    rw [h2]
    have : 6 / Λ = 3 * (1 / Λ) + 3 / Λ := by ring
    linarith
  have hKΛ : 6 / Λ ≤ K / Λ := by gcongr; linarith
  have hδ0 : 0 ≤ δ := by positivity
  have hwin := fun ω (hω : ω ∈ E) => hp.window hg.mu_pos hg.sigma_pos hc (x0 ω) hω
  -- bounds on `y` and `w`
  have hy0 : 0 ≤ greY c n eps := by
    unfold greY
    apply Real.logb_nonneg one_lt_two
    have : 0 ≤ Λ / Real.log (c * eps ^ 2) := div_nonneg hΛ0.le (by linarith)
    linarith
  have hy2 : greY c n eps ≤ 2 * Λ := by
    unfold greY
    have hρ1 : 1 ≤ Real.log (c * eps ^ 2) := by linarith
    have h1 : Λ / Real.log (c * eps ^ 2) ≤ Λ := div_le_self hΛ0.le hρ1
    have h2 : Real.logb 2 (Λ / Real.log (c * eps ^ 2) + 1) ≤ Real.logb 2 (Λ + 1) :=
      Real.logb_le_logb_of_le one_lt_two (by positivity) (by linarith)
    have h3 : Real.logb 2 (Λ + 1) ≤ 2 * Λ := by
      rw [Real.logb, div_le_iff₀ (by linarith)]
      have := Real.log_le_sub_one_of_pos (show 0 < Λ + 1 by linarith)
      nlinarith
    linarith
  have hw0 : 0 ≤ greW K n eps := by
    unfold greW
    have : 0 ≤ Real.log (Real.log n) / Real.log n := div_nonneg (by linarith [hp.loglog]) hΛ0.le
    have : 0 < 1 / Real.log eps := by positivity
    have : 0 < K := by linarith
    positivity
  have hw1 := hp.w_le
  refine ⟨?_, ?_, ?_⟩
  · have hlo := le_integral_of_event hHm hE h0 hmax hδ (V := greY c n eps - greW K n eps)
      fun ω hω => (hwin ω hω).1.1.le
    have habs : |greY c n eps - greW K n eps| ≤ 3 * Λ := by
      rw [abs_le]; constructor <;> linarith
    have : |greY c n eps - greW K n eps| * δ ≤ 3 * Λ * δ := mul_le_mul_of_nonneg_right habs hδ0
    linarith
  · have hup := integral_le_of_event hHm hE (U := greY c n eps + 1 + greW K n eps)
      (by linarith) (by positivity) h0 hmax hδ fun ω hω => (hwin ω hω).1.2
    have : ((Nat.log 2 n : ℝ) + 1) * δ ≤ 3 * Λ * δ := mul_le_mul_of_nonneg_right hHmax hδ0
    linarith
  · intro hm
    have hex : ∀ ω ∈ E, H ω = ((⌈greY c n eps⌉ : ℤ) : ℝ) := fun ω hω => by
      have := (hwin ω hω).2 hm
      simp only [hHdef]
      exact_mod_cast this
    have hc0 : (0 : ℝ) ≤ ((⌈greY c n eps⌉ : ℤ) : ℝ) := by
      exact_mod_cast (Int.ceil_nonneg hy0)
    have hc3 : ((⌈greY c n eps⌉ : ℤ) : ℝ) ≤ 3 * Λ := by
      have := Int.ceil_lt_add_one (greY c n eps)
      linarith
    have hup := integral_le_of_event hHm hE (U := ((⌈greY c n eps⌉ : ℤ) : ℝ)) hc0
      (by positivity) h0 hmax hδ fun ω hω => (hex ω hω).le
    have hlo := le_integral_of_event hHm hE h0 hmax hδ (V := ((⌈greY c n eps⌉ : ℤ) : ℝ))
      fun ω hω => (hex ω hω).ge
    have i1 : ((Nat.log 2 n : ℝ) + 1) * δ ≤ 3 * Λ * δ := mul_le_mul_of_nonneg_right hHmax hδ0
    have i2 : |((⌈greY c n eps⌉ : ℤ) : ℝ)| * δ ≤ 3 * Λ * δ := by
      rw [abs_of_nonneg hc0]; exact mul_le_mul_of_nonneg_right hc3 hδ0
    rw [abs_le]
    constructor <;> linarith

end Params

/-! ## The growth conditions -/

/-- `greW K n ε → 0` along `n → ∞`, `ε → ∞`. -/
theorem tendsto_greW (K : ℝ) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop) :
    Tendsto (fun k => greW K (n k) (ε k)) atTop (𝓝 0) := by
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLε : Tendsto (fun k => Real.log (ε k)) atTop atTop := Real.tendsto_log_atTop.comp hε
  have h1 : Tendsto (fun k => 1 / Real.log (ε k)) atTop (𝓝 0) :=
    Tendsto.congr (fun k => by simp [one_div]) hLε.inv_tendsto_atTop
  have h2 : Tendsto (fun k => Real.log (Real.log (n k)) / Real.log (n k)) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hL
    simp only [pow_one, one_mul, add_zero] at this
    exact this
  have := (h1.add h2).const_mul K
  simpa [greW] using this

/-- Along `n → ∞`, `ε → ∞`, `log ε = o(log n)`, the hypotheses `GREParams` hold eventually for
every `K ≥ greK μ₀ σ₀ c`. -/
theorem eventually_GREParams {μ₀ σ₀ κ₀ c K : ℝ} (hK : greK μ₀ σ₀ c ≤ K) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    ∀ᶠ k in atTop, GREParams μ₀ σ₀ κ₀ c K (n k) (ε k) := by
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  have hLε : Tendsto (fun k => Real.log (ε k)) atTop atTop := Real.tendsto_log_atTop.comp hε
  have hw := tendsto_greW K hn hε
  -- `κ log² x ≤ √x` eventually
  set κ := 2 * (128 * (4 * (8 / cRE + 2) / aRE) + (8 / cRE + 2)) with hκ
  have hκ0 : 0 < κ := by have := cRE_pos; have := aRE_pos; positivity
  have hsq : ∀ᶠ x : ℝ in atTop, κ * Real.log x ^ 2 ≤ Real.sqrt x := by
    have h := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (inv_pos.2 hκ0)
    filter_upwards [h, eventually_ge_atTop 1] with x hx hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (Real.log x) 2]
    push_cast
    calc κ * Real.log x ^ (2 : ℝ) ≤ κ * (κ⁻¹ * x ^ (1 / 2 : ℝ)) := by gcongr
      _ = x ^ (1 / 2 : ℝ) := by field_simp
  set b := μ₀ ^ 2 / σ₀ ^ 2
  filter_upwards [hε.eventually_ge_atTop (epsZero (σ₀ ^ 2 / μ₀ ^ 2) (2 + κ₀ / σ₀ ^ 3)),
    hn.eventually_ge_atTop 3, hLL.eventually_ge_atTop 1,
    hLε.eventually_ge_atTop (1 + |Real.log c| + |Real.log (2 / aRE * b)| +
      |Real.log (b / 512)|),
    hw.eventually (eventually_le_nhds one_pos), hn.eventually hsq,
    hεn.eventually (eventually_le_nhds (show (0 : ℝ) < 1 / 4 by norm_num)),
    hL.eventually_ge_atTop (2 * |Real.log b|), hL.eventually_gt_atTop 0]
    with k h1 h2 h3 h4 h5 h6 h7 h8 h9
  refine ⟨h1, by exact_mod_cast h2, h3, h4, hK, h5, h6, ?_⟩
  have h7' : Real.log (ε k) ≤ 1 / 4 * Real.log (n k) := (div_le_iff₀ h9).1 h7
  have := le_abs_self (Real.log b)
  linarith

end

end PGM
