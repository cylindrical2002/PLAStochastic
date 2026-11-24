import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Height asymptotics: a constant factor in the compression costs nothing

Deterministic real analysis behind the asymptotic height theorems.

* Part A: first passage through a sequence with a multiplicative ratio bracket
  `Γ / c ≤ m (ℓ + 1) / m ℓ ≤ c * Γ` is sandwiched between
  `log x / log (c * Γ)` and `log x / log (Γ / c) + 1`.
* Part B: along a sequence of models with `Γ = ε ^ 2`, `ε, n → ∞` and
  `log ε / log n → 0`, the first passage through any level `x` with
  `log x / log n → 1` is asymptotic to `log n / (2 * log ε)`; the same holds
  for any `h` squeezed between two such first passages up to an additive constant.
* Part C: the double-exponential recursion `Δ (ℓ + 1) ≍ A * Δ ℓ ^ 2` of the
  rank-equispaced index and the two height consequences used in `thm:heightRE`.
-/

namespace PGM

open Filter Topology

noncomputable section

/-! ## Part A: first passage through a geometric sequence -/

/-- The first index at which the sequence `m` reaches level `x`
    (`0` if it never does; under growth it always does). -/
def firstPassage (m : ℕ → ℝ) (x : ℝ) : ℕ := sInf {ℓ | x ≤ m ℓ}

section Geometric

variable {m : ℕ → ℝ} {Γ c : ℝ}

theorem one_lt_div_of_sq_lt (hc : 1 ≤ c) (hΓ : c ^ 2 < Γ) : 1 < Γ / c := by
  have hc0 : 0 < c := by linarith
  rw [lt_div_iff₀ hc0]
  nlinarith

theorem one_lt_mul_of_sq_lt (hc : 1 ≤ c) (hΓ : c ^ 2 < Γ) : 1 < c * Γ := by
  nlinarith

/-- Positivity propagates along the lower ratio bound. -/
theorem geometric_pos (hq : 0 < Γ / c) (hm0 : m 0 = 1)
    (hlo : ∀ ℓ, Γ / c ≤ m (ℓ + 1) / m ℓ) : ∀ ℓ, 0 < m ℓ := by
  intro ℓ
  induction ℓ with
  | zero => rw [hm0]; exact one_pos
  | succ ℓ ih =>
      have h := hlo ℓ
      rw [le_div_iff₀ ih] at h
      nlinarith

theorem geometric_lower_pow (hq : 0 < Γ / c) (hm0 : m 0 = 1)
    (hlo : ∀ ℓ, Γ / c ≤ m (ℓ + 1) / m ℓ) : ∀ ℓ, (Γ / c) ^ ℓ ≤ m ℓ := by
  have hpos := geometric_pos hq hm0 hlo
  intro ℓ
  induction ℓ with
  | zero => rw [hm0, pow_zero]
  | succ ℓ ih =>
      have h := hlo ℓ
      rw [le_div_iff₀ (hpos ℓ)] at h
      rw [pow_succ]
      nlinarith [pow_pos hq ℓ]

theorem geometric_upper_pow (hq : 0 < Γ / c) (hm0 : m 0 = 1)
    (hlo : ∀ ℓ, Γ / c ≤ m (ℓ + 1) / m ℓ)
    (hup : ∀ ℓ, m (ℓ + 1) / m ℓ ≤ c * Γ) : ∀ ℓ, m ℓ ≤ (c * Γ) ^ ℓ := by
  have hpos := geometric_pos hq hm0 hlo
  intro ℓ
  induction ℓ with
  | zero => rw [hm0, pow_zero]
  | succ ℓ ih =>
      have h := hup ℓ
      rw [div_le_iff₀ (hpos ℓ)] at h
      have hcΓ : 0 ≤ c * Γ := by
        by_contra hneg
        push Not at hneg
        nlinarith [hpos (ℓ + 1), hpos ℓ, mul_neg_of_neg_of_pos hneg (hpos ℓ)]
      rw [pow_succ]
      nlinarith

theorem geometric_exists_ge (hq : 1 < Γ / c) (hm0 : m 0 = 1)
    (hlo : ∀ ℓ, Γ / c ≤ m (ℓ + 1) / m ℓ) (x : ℝ) : ∃ ℓ, x ≤ m ℓ := by
  obtain ⟨ℓ, hℓ⟩ := pow_unbounded_of_one_lt x hq
  exact ⟨ℓ, hℓ.le.trans (geometric_lower_pow (by linarith) hm0 hlo ℓ)⟩

theorem firstPassage_hit {x : ℝ} (h : ∃ ℓ, x ≤ m ℓ) : x ≤ m (firstPassage m x) :=
  Nat.sInf_mem h

theorem firstPassage_le {x : ℝ} {ℓ : ℕ} (h : x ≤ m ℓ) : firstPassage m x ≤ ℓ :=
  Nat.sInf_le h

theorem lt_of_lt_firstPassage {x : ℝ} {j : ℕ} (hj : j < firstPassage m x) : m j < x := by
  have h := Nat.notMem_of_lt_sInf hj
  simp only [Set.mem_ofPred_eq, not_le] at h
  exact h

/-- A1, lower half: `log x / log (c Γ) ≤ ℓ(x)` for every positive level `x`. -/
theorem log_div_le_firstPassage (hc : 1 ≤ c) (hΓ : c ^ 2 < Γ) (hm0 : m 0 = 1)
    (hlo : ∀ ℓ, Γ / c ≤ m (ℓ + 1) / m ℓ) (hup : ∀ ℓ, m (ℓ + 1) / m ℓ ≤ c * Γ)
    {x : ℝ} (hx : 0 < x) :
    Real.log x / Real.log (c * Γ) ≤ firstPassage m x := by
  have hq := one_lt_div_of_sq_lt hc hΓ
  have hhit : x ≤ m (firstPassage m x) :=
    firstPassage_hit (geometric_exists_ge hq hm0 hlo x)
  have hle : x ≤ (c * Γ) ^ firstPassage m x :=
    hhit.trans (geometric_upper_pow (by linarith) hm0 hlo hup _)
  have hlog : Real.log x ≤ (firstPassage m x : ℝ) * Real.log (c * Γ) := by
    rw [← Real.log_pow]
    exact Real.log_le_log hx hle
  rw [div_le_iff₀ (Real.log_pos (one_lt_mul_of_sq_lt hc hΓ))]
  exact hlog

/-- A1, upper half: `ℓ(x) ≤ log x / log (Γ / c) + 1` for every level `x ≥ 1`. -/
theorem firstPassage_le_log_div (hc : 1 ≤ c) (hΓ : c ^ 2 < Γ) (hm0 : m 0 = 1)
    (hlo : ∀ ℓ, Γ / c ≤ m (ℓ + 1) / m ℓ) {x : ℝ} (hx : 1 ≤ x) :
    (firstPassage m x : ℝ) ≤ Real.log x / Real.log (Γ / c) + 1 := by
  have hq := one_lt_div_of_sq_lt hc hΓ
  have hlq := Real.log_pos hq
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  rcases Nat.eq_zero_or_pos (firstPassage m x) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    have : 0 ≤ Real.log x / Real.log (Γ / c) := div_nonneg hlx hlq.le
    linarith
  · obtain ⟨j, hj⟩ : ∃ j, firstPassage m x = j + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hmj : m j < x := lt_of_lt_firstPassage (by omega)
    have h1 : (Γ / c) ^ j < x :=
      (geometric_lower_pow (by linarith) hm0 hlo j).trans_lt hmj
    have h2 : (j : ℝ) * Real.log (Γ / c) < Real.log x := by
      rw [← Real.log_pow]
      exact Real.log_lt_log (pow_pos (by linarith) j) h1
    have h3 : (j : ℝ) < Real.log x / Real.log (Γ / c) := by
      rw [lt_div_iff₀ hlq]
      exact h2
    rw [hj, Nat.cast_succ]
    linarith

end Geometric

/-! ## Part B: the asymptotic height scale `log n / (2 log ε)` -/

section Asymptotic

variable {ε n : ℕ → ℝ} {m : ℕ → ℕ → ℝ} {c : ℝ}

/-- B1. Along a sequence of geometric compressions with ratio bracket
    `ε k ^ 2 / c ≤ m k (ℓ + 1) / m k ℓ ≤ c * ε k ^ 2`, and in the regime
    `ε, n → ∞`, `log ε / log n → 0`, the first passage through any level `x k`
    with `log x / log n → 1` is asymptotic to `log n / (2 log ε)`. -/
theorem firstPassage_div_scale_tendsto (hc : 1 ≤ c)
    (hm0 : ∀ k, m k 0 = 1)
    (hlo : ∀ k ℓ, ε k ^ 2 / c ≤ m k (ℓ + 1) / m k ℓ)
    (hup : ∀ k ℓ, m k (ℓ + 1) / m k ℓ ≤ c * ε k ^ 2)
    (hε : Tendsto ε atTop atTop) (hn : Tendsto n atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {x : ℕ → ℝ} (hx1 : ∀ᶠ k in atTop, 1 ≤ x k)
    (hx : Tendsto (fun k => Real.log (x k) / Real.log (n k)) atTop (𝓝 1)) :
    Tendsto (fun k => (firstPassage (m k) (x k) : ℝ) /
      (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
  have hlε : Tendsto (fun k => Real.log (ε k)) atTop atTop :=
    Real.tendsto_log_atTop.comp hε
  have hlc : Tendsto (fun k => Real.log c / Real.log (ε k)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlε
  have hinv : Tendsto (fun k => 2 * Real.log (ε k) / Real.log (n k)) atTop (𝓝 0) := by
    have h := hεn.const_mul 2
    rw [mul_zero] at h
    refine h.congr (fun k => ?_)
    ring
  have hf : Tendsto (fun k => Real.log (x k) / Real.log (n k) *
      (2 / (2 + Real.log c / Real.log (ε k)))) atTop (𝓝 1) := by
    have h2 : Tendsto (fun k => 2 / (2 + Real.log c / Real.log (ε k))) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (2 : ℝ))).div
        (tendsto_const_nhds.add hlc) (show (2 : ℝ) + 0 ≠ 0 by norm_num)
      norm_num at h
      exact h
    simpa using hx.mul h2
  have hg : Tendsto (fun k => Real.log (x k) / Real.log (n k) *
      (2 / (2 - Real.log c / Real.log (ε k))) +
        2 * Real.log (ε k) / Real.log (n k)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun k => 2 / (2 - Real.log c / Real.log (ε k))) atTop (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (2 : ℝ))).div
        (tendsto_const_nhds.sub hlc) (show (2 : ℝ) - 0 ≠ 0 by norm_num)
      norm_num at h
      exact h
    simpa using (hx.mul h2).add hinv
  have hεc : ∀ᶠ k in atTop, c < ε k := hε.eventually_gt_atTop c
  have hn1 : ∀ᶠ k in atTop, 1 < n k := hn.eventually_gt_atTop 1
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hg ?_ ?_
  · filter_upwards [hεc, hn1, hx1] with k hck hnk hxk
    have hε1 : 1 < ε k := lt_of_le_of_lt hc hck
    have hsq : c ^ 2 < ε k ^ 2 := by nlinarith
    have he : 0 < Real.log (ε k) := Real.log_pos hε1
    have hN : 0 < Real.log (n k) := Real.log_pos hnk
    have hA := log_div_le_firstPassage hc hsq (hm0 k) (hlo k) (hup k)
      (x := x k) (by linarith)
    have hlog : Real.log (c * ε k ^ 2) = Real.log c + 2 * Real.log (ε k) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hlog] at hA
    have hden : 0 < Real.log c + 2 * Real.log (ε k) := by linarith
    have key : Real.log (x k) / Real.log (n k) * (2 / (2 + Real.log c / Real.log (ε k))) =
        Real.log (x k) / (Real.log c + 2 * Real.log (ε k)) *
          (2 * Real.log (ε k) / Real.log (n k)) := by
      field_simp
      ring
    have key2 : (firstPassage (m k) (x k) : ℝ) / (Real.log (n k) / (2 * Real.log (ε k))) =
        (firstPassage (m k) (x k) : ℝ) * (2 * Real.log (ε k) / Real.log (n k)) := by
      field_simp
    rw [key, key2]
    exact mul_le_mul_of_nonneg_right hA (by positivity)
  · filter_upwards [hεc, hn1, hx1] with k hck hnk hxk
    have hε1 : 1 < ε k := lt_of_le_of_lt hc hck
    have hsq : c ^ 2 < ε k ^ 2 := by nlinarith
    have he : 0 < Real.log (ε k) := Real.log_pos hε1
    have hN : 0 < Real.log (n k) := Real.log_pos hnk
    have hA := firstPassage_le_log_div hc hsq (hm0 k) (hlo k) hxk
    have hlog : Real.log (ε k ^ 2 / c) = 2 * Real.log (ε k) - Real.log c := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_pow]
      push_cast
      ring
    have hden : 0 < 2 * Real.log (ε k) - Real.log c := by
      rw [← hlog]
      exact Real.log_pos (one_lt_div_of_sq_lt hc hsq)
    rw [hlog] at hA
    have key : Real.log (x k) / Real.log (n k) * (2 / (2 - Real.log c / Real.log (ε k))) +
        2 * Real.log (ε k) / Real.log (n k) =
        (Real.log (x k) / (2 * Real.log (ε k) - Real.log c) + 1) *
          (2 * Real.log (ε k) / Real.log (n k)) := by
      have hne : 2 * Real.log (ε k) - Real.log c ≠ 0 := hden.ne'
      field_simp
    have key2 : (firstPassage (m k) (x k) : ℝ) / (Real.log (n k) / (2 * Real.log (ε k))) =
        (firstPassage (m k) (x k) : ℝ) * (2 * Real.log (ε k) / Real.log (n k)) := by
      field_simp
    rw [key, key2]
    exact mul_le_mul_of_nonneg_right hA (by positivity)

/-- B2. Any `h` squeezed, up to a fixed additive constant `C`, between the first
    passages through two admissible levels `x` and `y` has the same asymptotics
    `h ~ log n / (2 log ε)`. -/
theorem div_scale_tendsto_of_squeeze (hc : 1 ≤ c)
    (hm0 : ∀ k, m k 0 = 1)
    (hlo : ∀ k ℓ, ε k ^ 2 / c ≤ m k (ℓ + 1) / m k ℓ)
    (hup : ∀ k ℓ, m k (ℓ + 1) / m k ℓ ≤ c * ε k ^ 2)
    (hε : Tendsto ε atTop atTop) (hn : Tendsto n atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {x y h : ℕ → ℝ} (C : ℝ)
    (hx1 : ∀ᶠ k in atTop, 1 ≤ x k)
    (hx : Tendsto (fun k => Real.log (x k) / Real.log (n k)) atTop (𝓝 1))
    (hy1 : ∀ᶠ k in atTop, 1 ≤ y k)
    (hy : Tendsto (fun k => Real.log (y k) / Real.log (n k)) atTop (𝓝 1))
    (hlow : ∀ᶠ k in atTop, (firstPassage (m k) (x k) : ℝ) - C ≤ h k)
    (hhigh : ∀ᶠ k in atTop, h k ≤ (firstPassage (m k) (y k) : ℝ) + C) :
    Tendsto (fun k => h k / (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
  have hX := firstPassage_div_scale_tendsto hc hm0 hlo hup hε hn hεn hx1 hx
  have hY := firstPassage_div_scale_tendsto hc hm0 hlo hup hε hn hεn hy1 hy
  have hC : Tendsto (fun k => C / (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 0) := by
    have h := hεn.const_mul (2 * C)
    rw [mul_zero] at h
    refine h.congr (fun k => ?_)
    rw [div_div_eq_mul_div]
    ring
  have hf : Tendsto (fun k => ((firstPassage (m k) (x k) : ℝ) - C) /
      (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
    have h := hX.sub hC
    rw [sub_zero] at h
    exact h.congr (fun k => (sub_div _ _ _).symm)
  have hg : Tendsto (fun k => ((firstPassage (m k) (y k) : ℝ) + C) /
      (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
    have h := hY.add hC
    rw [add_zero] at h
    exact h.congr (fun k => (add_div _ _ _).symm)
  have hε1 : ∀ᶠ k in atTop, 1 < ε k := hε.eventually_gt_atTop 1
  have hn1 : ∀ᶠ k in atTop, 1 < n k := hn.eventually_gt_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hg ?_ ?_
  · filter_upwards [hε1, hn1, hlow] with k hk1 hnk hk
    have : 0 < Real.log (n k) / (2 * Real.log (ε k)) := by
      have := Real.log_pos hk1
      have := Real.log_pos hnk
      positivity
    gcongr
  · filter_upwards [hε1, hn1, hhigh] with k hk1 hnk hk
    have : 0 < Real.log (n k) / (2 * Real.log (ε k)) := by
      have := Real.log_pos hk1
      have := Real.log_pos hnk
      positivity
    gcongr

/-- A level comparable to `n` up to fixed positive factors has `log x / log n → 1`. -/
theorem tendsto_log_div_log_of_comparable {x : ℕ → ℝ} (hn : Tendsto n atTop atTop)
    {a b : ℝ} (ha : 0 < a)
    (hax : ∀ᶠ k in atTop, a * n k ≤ x k) (hxb : ∀ᶠ k in atTop, x k ≤ b * n k) :
    Tendsto (fun k => Real.log (x k) / Real.log (n k)) atTop (𝓝 1) := by
  have hln : Tendsto (fun k => Real.log (n k)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hf : Tendsto (fun k => 1 + Real.log a / Real.log (n k)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hln)
  have hg : Tendsto (fun k => 1 + Real.log b / Real.log (n k)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hln)
  have hn1 : ∀ᶠ k in atTop, 1 < n k := hn.eventually_gt_atTop 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hg ?_ ?_
  · filter_upwards [hn1, hax] with k hnk hk
    have hN : 0 < Real.log (n k) := Real.log_pos hnk
    have hlog : Real.log a + Real.log (n k) ≤ Real.log (x k) := by
      rw [← Real.log_mul ha.ne' (by linarith)]
      exact Real.log_le_log (by positivity) hk
    rw [le_div_iff₀ hN, add_mul, one_mul, div_mul_cancel₀ _ hN.ne']
    linarith
  · filter_upwards [hn1, hax, hxb] with k hnk hk hk'
    have hN : 0 < Real.log (n k) := Real.log_pos hnk
    have hb : 0 < b := by nlinarith
    have hlog : Real.log (x k) ≤ Real.log b + Real.log (n k) := by
      rw [← Real.log_mul hb.ne' (by linarith)]
      exact Real.log_le_log (by nlinarith) hk'
    rw [div_le_iff₀ hN, add_mul, one_mul, div_mul_cancel₀ _ hN.ne']
    linarith

/-- B3. The level `x = n` is admissible in B1. -/
theorem level_self (hn : Tendsto n atTop atTop) :
    (∀ᶠ k in atTop, 1 ≤ n k) ∧
      Tendsto (fun k => Real.log (n k) / Real.log (n k)) atTop (𝓝 1) :=
  ⟨hn.eventually_ge_atTop 1, tendsto_log_div_log_of_comparable hn one_pos
    (Eventually.of_forall fun k => by rw [one_mul])
    (Eventually.of_forall fun k => by rw [one_mul])⟩

/-- B3. The level `x = 2 n` is admissible in B1. -/
theorem level_two_mul (hn : Tendsto n atTop atTop) :
    (∀ᶠ k in atTop, 1 ≤ 2 * n k) ∧
      Tendsto (fun k => Real.log (2 * n k) / Real.log (n k)) atTop (𝓝 1) := by
  refine ⟨?_, tendsto_log_div_log_of_comparable hn two_pos
    (Eventually.of_forall fun k => le_rfl) (Eventually.of_forall fun k => le_rfl)⟩
  filter_upwards [hn.eventually_ge_atTop 1] with k hk
  linarith

/-- B3. The level `x = n - 1` is admissible in B1. -/
theorem level_sub_one (hn : Tendsto n atTop atTop) :
    (∀ᶠ k in atTop, 1 ≤ n k - 1) ∧
      Tendsto (fun k => Real.log (n k - 1) / Real.log (n k)) atTop (𝓝 1) := by
  have h2 : ∀ᶠ k in atTop, 2 ≤ n k := hn.eventually_ge_atTop 2
  refine ⟨?_, tendsto_log_div_log_of_comparable hn (a := 1 / 2) (b := 1) (by norm_num)
    ?_ ?_⟩
  · filter_upwards [h2] with k hk
    linarith
  · filter_upwards [h2] with k hk
    linarith
  · exact Eventually.of_forall fun k => by linarith

end Asymptotic

/-! ## Part C: the double-exponential recursion of the rank-equispaced index -/

section Recursion

variable {Δ : ℕ → ℝ} {A a b : ℝ} {L : ℕ}

/-- C1, lower half: `(a A) ^ (2 ^ ℓ - 1) ≤ Δ ℓ` for `ℓ ≤ L`. -/
theorem dexp_lower (haA : 0 ≤ a * A) (hΔ0 : Δ 0 = 1)
    (hlo : ∀ ℓ, ℓ < L → a * A * Δ ℓ ^ 2 ≤ Δ (ℓ + 1)) :
    ∀ ℓ, ℓ ≤ L → (a * A) ^ (2 ^ ℓ - 1) ≤ Δ ℓ := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [hΔ0]
  | succ ℓ ih =>
      have hpow : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      calc
        (a * A) ^ (2 ^ (ℓ + 1) - 1) = a * A * ((a * A) ^ (2 ^ ℓ - 1)) ^ 2 := by
          rw [show 2 ^ (ℓ + 1) - 1 = 1 + 2 * (2 ^ ℓ - 1) by omega, pow_add, pow_mul,
            pow_one]
          ring
        _ ≤ a * A * Δ ℓ ^ 2 :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (pow_nonneg haA _) (ih (by omega)) 2) haA
        _ ≤ Δ (ℓ + 1) := hlo ℓ (by omega)

/-- C1, upper half: `Δ ℓ ≤ (b A) ^ (2 ^ ℓ - 1)` for `ℓ ≤ L`. -/
theorem dexp_upper (haA : 0 ≤ a * A) (hbA : 0 ≤ b * A) (hΔ0 : Δ 0 = 1)
    (hlo : ∀ ℓ, ℓ < L → a * A * Δ ℓ ^ 2 ≤ Δ (ℓ + 1))
    (hup : ∀ ℓ, ℓ < L → Δ (ℓ + 1) ≤ b * A * Δ ℓ ^ 2) :
    ∀ ℓ, ℓ ≤ L → Δ ℓ ≤ (b * A) ^ (2 ^ ℓ - 1) := by
  intro ℓ hℓ
  induction ℓ with
  | zero => simp [hΔ0]
  | succ ℓ ih =>
      have hpow : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
      have hΔnn : 0 ≤ Δ ℓ :=
        (pow_nonneg haA _).trans (dexp_lower haA hΔ0 hlo ℓ (by omega))
      calc
        Δ (ℓ + 1) ≤ b * A * Δ ℓ ^ 2 := hup ℓ (by omega)
        _ ≤ b * A * ((b * A) ^ (2 ^ ℓ - 1)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΔnn (ih (by omega)) 2) hbA
        _ = (b * A) ^ (2 ^ (ℓ + 1) - 1) := by
          rw [show 2 ^ (ℓ + 1) - 1 = 1 + 2 * (2 ^ ℓ - 1) by omega, pow_add, pow_mul,
            pow_one]
          ring

/-- C2, the cutoff upper bound: if every layer before `L` still has `Δ ℓ < n`,
    then `L ≤ log₂ (log n / log (a A)) + 2`. -/
theorem dexp_cutoff_le_logb (haA : 1 < a * A) (hΔ0 : Δ 0 = 1)
    (hlo : ∀ ℓ, ℓ < L → a * A * Δ ℓ ^ 2 ≤ Δ (ℓ + 1)) {n : ℝ} (hn : a * A ≤ n)
    (hbelow : ∀ ℓ, ℓ < L → Δ ℓ < n) :
    (L : ℝ) ≤ Real.logb 2 (Real.log n / Real.log (a * A)) + 2 := by
  have hq : 0 < Real.log (a * A) := Real.log_pos haA
  have hR1 : 1 ≤ Real.log n / Real.log (a * A) := by
    rw [le_div_iff₀ hq, one_mul]
    exact Real.log_le_log (by linarith) hn
  have hlogb : 0 ≤ Real.logb 2 (Real.log n / Real.log (a * A)) :=
    Real.logb_nonneg one_lt_two hR1
  rcases Nat.lt_or_ge L 2 with hL | hL
  · have : (L : ℝ) ≤ 2 := by exact_mod_cast hL.le
    linarith
  · obtain ⟨j, rfl⟩ : ∃ j, L = j + 2 := ⟨L - 2, by omega⟩
    have hlow := dexp_lower (by linarith) hΔ0 hlo (j + 1) (by omega)
    have hlt : (a * A) ^ (2 ^ (j + 1) - 1) < n := hlow.trans_lt (hbelow (j + 1) (by omega))
    have hpow : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    have h1 : ((2 : ℝ) ^ (j + 1) - 1) * Real.log (a * A) < Real.log n := by
      have h := Real.log_lt_log (pow_pos (by linarith) _) hlt
      rw [Real.log_pow, Nat.cast_sub hpow] at h
      push_cast at h
      exact h
    have h2 : (2 : ℝ) ^ j < Real.log n / Real.log (a * A) := by
      rw [lt_div_iff₀ hq]
      have h3 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (j + 1) - 1 := by
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        rw [pow_succ]
        linarith
      nlinarith
    have h4 : (j : ℝ) < Real.logb 2 (Real.log n / Real.log (a * A)) := by
      rw [Real.lt_logb_iff_rpow_lt one_lt_two (by linarith), Real.rpow_natCast]
      exact h2
    push_cast
    linarith

/-- C3, the bootstrap for the lower bound: as long as
    `2 ^ (ℓ + 1) * log (b A) ≤ (1 / 2) * log n`, the layer `ℓ ≤ L` still has
    `A * Δ ℓ ^ 2 ≤ n ^ (1 / 2)`. -/
theorem dexp_mul_sq_le_sqrt (ha : 0 ≤ a) (hA : 1 ≤ A) (hb : 1 ≤ b) (hΔ0 : Δ 0 = 1)
    (hlo : ∀ ℓ, ℓ < L → a * A * Δ ℓ ^ 2 ≤ Δ (ℓ + 1))
    (hup : ∀ ℓ, ℓ < L → Δ (ℓ + 1) ≤ b * A * Δ ℓ ^ 2)
    {n : ℝ} (hn : 0 < n) {ℓ : ℕ} (hℓ : ℓ ≤ L)
    (hcut : 2 ^ (ℓ + 1) * Real.log (b * A) ≤ 1 / 2 * Real.log n) :
    A * Δ ℓ ^ 2 ≤ n ^ ((1 : ℝ) / 2) := by
  have haA : 0 ≤ a * A := mul_nonneg ha (by linarith)
  have hbA : 1 ≤ b * A := by nlinarith
  have hΔnn : 0 ≤ Δ ℓ := (pow_nonneg haA _).trans (dexp_lower haA hΔ0 hlo ℓ hℓ)
  have hΔu := dexp_upper haA (by linarith) hΔ0 hlo hup ℓ hℓ
  have hpow : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
  have step1 : A * Δ ℓ ^ 2 ≤ (b * A) ^ (2 ^ (ℓ + 1)) := by
    calc
      A * Δ ℓ ^ 2 ≤ (b * A) * ((b * A) ^ (2 ^ ℓ - 1)) ^ 2 :=
        mul_le_mul (by nlinarith) (pow_le_pow_left₀ hΔnn hΔu 2) (by positivity)
          (by linarith)
      _ = (b * A) ^ (2 ^ (ℓ + 1) - 1) := by
        rw [show 2 ^ (ℓ + 1) - 1 = 1 + 2 * (2 ^ ℓ - 1) by omega, pow_add, pow_mul,
          pow_one]
        ring
      _ ≤ (b * A) ^ (2 ^ (ℓ + 1)) := pow_le_pow_right₀ hbA (by omega)
  have step2 : (b * A) ^ (2 ^ (ℓ + 1)) ≤ n ^ ((1 : ℝ) / 2) := by
    rw [← Real.log_le_log_iff (pow_pos (by linarith) _) (Real.rpow_pos_of_pos hn _),
      Real.log_pow, Real.log_rpow hn]
    push_cast
    linarith
  exact step1.trans step2

end Recursion

end

end PGM
