import PLAStochastic.Index.GEP.Kernel.Row.Pin

/-!
# WP4 kernel rows: Green sums

Source: `influence-lipschitz.md` §3, displays (row) and (pin), for the band `[0, w]`, the slope
window `|a - 1| ≤ A/w`, and boundary points `b, b' ∈ {0, w}`, in either direction:

* `sum_krSurv_bdry_le` / `tsum_krSurv_bdry_le`: `O_b^± = ∑_{n ≥ 0} s_n(b) ≤ C_O (1 + A) w`;
* `sum_krDens_bdry_row_le` / `tsum_krDens_bdry_row_le`:
  `‖∑_{n ≥ 1} q_n(b, ·)‖_∞ ≤ C_G (1 + A) (1 + log w)` (pointwise in `z`, uniformly);
* `sum_krDens_bdry_pin_le` / `tsum_krDens_bdry_pin_le`: for `b ≠ b'` and `A ≤ w`,
  `∑_{n ≥ 1} q_n(b, b') ≤ C_P (1 + A)² w^{-1/2}`;
* `sum_weighted_krDens_bdry_pin_le` / `tsum_weighted_krDens_bdry_pin_le`:
  `∑_{n ≥ 1} (n + w) q_n(b, b') ≤ C_B (1 + A)² w`, which bounds `B_↑ + B_↓` since
  `|n - w| ≤ n + w`.

The time scale is `T = ⌈w²/2⌉` (`krT`), so that `1 ≤ T ≤ w² ≤ 2T`; the medium-time bounds are
used for `n < 2T` and the large-time bounds (killed `L²` gap, rate `√λ`) for `n ≥ 2T`.  All
constants are explicit functions of the class parameters and of the interface constants `K, L`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Elementary sums -/

/-- Splitting a partial sum of a nonnegative sequence at `N₀`. -/
theorem kr_sum_split {F : ℕ → ℝ} (hF : ∀ n, 0 ≤ F n) (N₀ M : ℕ) :
    ∑ n ∈ Finset.range M, F n ≤
      ∑ n ∈ Finset.range N₀, F n + ∑ j ∈ Finset.range (M - N₀), F (N₀ + j) := by
  rcases le_or_gt M N₀ with h | h
  · rw [Nat.sub_eq_zero_of_le h, Finset.sum_range_zero, add_zero]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono h) fun i _ _ => hF i
  · have e : M = N₀ + (M - N₀) := by omega
    conv_lhs => rw [e]
    rw [Finset.sum_range_add]

theorem kr_telescope_sqrt {u v : ℝ} (hv : 0 < v) (h : v ^ 2 - u ^ 2 = 1) :
    1 / v ≤ 2 * (v - u) := by
  rw [div_le_iff₀ hv]
  nlinarith [sq_nonneg (v - u)]

theorem kr_telescope_pow32 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (h : v ^ 2 - u ^ 2 = 1) :
    1 / (v ^ 2 * v) ≤ 2 / u - 2 / v := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h1 : (v - u) * (v + u) = 1 := by nlinarith
  have h2 : u * (v + u) ≤ 2 * v ^ 2 := by nlinarith
  have key : u * v ≤ (2 * v - u * 2) * (v ^ 2 * v) := by
    calc u * v = u * v * ((v - u) * (v + u)) := by rw [h1, mul_one]
      _ = (v - u) * v * (u * (v + u)) := by ring
      _ ≤ (v - u) * v * (2 * v ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (sub_nonneg.2 huv) hv.le)
      _ = (2 * v - u * 2) * (v ^ 2 * v) := by ring
  rw [div_sub_div _ _ hu.ne' hv.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- `∑_{i < N} 1/√(i+1) ≤ 2 √N`. -/
theorem kr_sum_inv_sqrt_le (N : ℕ) :
    ∑ i ∈ Finset.range N, 1 / Real.sqrt ((i : ℝ) + 1) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hv : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
    have h := kr_telescope_sqrt (u := Real.sqrt (N : ℝ)) hv
      (by rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (Nat.cast_nonneg _)]; ring)
    push_cast
    linarith

/-- `∑_{i < N} 1/(i+1) ≤ 1 + log N` for `N ≥ 1`. -/
theorem kr_sum_inv_le_log {N : ℕ} (hN : 1 ≤ N) :
    ∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1) ≤ 1 + Real.log N := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · simp
    · rw [Finset.sum_range_succ]
      have hN0 : (0 : ℝ) < N := by exact_mod_cast hpos
      have h := Real.log_le_sub_one_of_pos (x := (N : ℝ) / (N + 1)) (by positivity)
      rw [Real.log_div hN0.ne' (by positivity)] at h
      have e : (N : ℝ) / (N + 1) - 1 = -(1 / ((N : ℝ) + 1)) := by
        rw [div_sub_one (by positivity : ((N : ℝ) + 1) ≠ 0)]
        ring
      have := ih hpos
      push_cast
      linarith

/-- Tail telescoping: `∑_{j < M} 1/((N₀+j+1)^{3/2}) ≤ 2/√N₀ - 2/√(N₀+M)` for `N₀ ≥ 1`. -/
theorem kr_sum_inv_pow32_tail {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (M : ℕ) :
    ∑ j ∈ Finset.range M,
        1 / ((((N₀ + j : ℕ) : ℝ) + 1) * Real.sqrt (((N₀ + j : ℕ) : ℝ) + 1)) ≤
      2 / Real.sqrt N₀ - 2 / Real.sqrt ((N₀ + M : ℕ) : ℝ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hn0 : (0 : ℝ) < ((N₀ + M : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N₀ + M)
    have hu : 0 < Real.sqrt ((N₀ + M : ℕ) : ℝ) := Real.sqrt_pos.2 hn0
    have huv : Real.sqrt ((N₀ + M : ℕ) : ℝ) ≤ Real.sqrt (((N₀ + M : ℕ) : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have h := kr_telescope_pow32 hu huv
      (by rw [Real.sq_sqrt (by positivity), Real.sq_sqrt hn0.le]; ring)
    rw [Real.sq_sqrt (by positivity)] at h
    have e : ((N₀ + (M + 1) : ℕ) : ℝ) = ((N₀ + M : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e]
    linarith

theorem kr_sum_inv_pow32_tail_le {N₀ : ℕ} (hN₀ : 1 ≤ N₀) (M : ℕ) :
    ∑ j ∈ Finset.range M,
        1 / ((((N₀ + j : ℕ) : ℝ) + 1) * Real.sqrt (((N₀ + j : ℕ) : ℝ) + 1)) ≤
      2 / Real.sqrt N₀ := by
  refine (kr_sum_inv_pow32_tail hN₀ M).trans ?_
  have : 0 ≤ 2 / Real.sqrt ((N₀ + M : ℕ) : ℝ) := by positivity
  linarith

/-- `∑_{i < M} 1/((i+1)^{3/2}) ≤ 3`. -/
theorem kr_sum_inv_pow32_le (M : ℕ) :
    ∑ i ∈ Finset.range M, 1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1)) ≤ 3 := by
  cases M with
  | zero => simp
  | succ M =>
    rw [Finset.sum_range_succ']
    have h := kr_sum_inv_pow32_tail_le (N₀ := 1) le_rfl M
    have e : ∀ j : ℕ, (((1 + j : ℕ) : ℝ) + 1) = (((j + 1 : ℕ) : ℝ) + 1) := by
      intro j; push_cast; ring
    simp only [e, Nat.cast_one, Real.sqrt_one, div_one] at h
    simp only [Nat.cast_zero, zero_add, Real.sqrt_one, mul_one, div_one]
    linarith

/-- Geometric partial sums: `∑_{j < N} r^j ≤ 1/(1 - r)`. -/
theorem kr_geom_sum_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, r ^ j ≤ 1 / (1 - r) := by
  rw [one_div, ← tsum_geometric_of_lt_one h0 h1]
  exact (summable_geometric_of_lt_one h0 h1).sum_le_tsum _ fun j _ => pow_nonneg h0 j

/-- `∑_{j < N} j r^j ≤ 1/(1 - r)²`. -/
theorem kr_geom_sum_mul_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (N : ℕ) :
    ∑ j ∈ Finset.range N, (j : ℝ) * r ^ j ≤ 1 / (1 - r) ^ 2 := by
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := r)
    (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  refine (sum_le_hasSum (Finset.range N)
    (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_nonneg h0 j)) hs).trans ?_
  exact div_le_div_of_nonneg_right h1.le (by positivity)

/-- `e^{-c w} ≤ 2 / (c w)²` for `c, w > 0`. -/
theorem kr_exp_neg_le {c w : ℝ} (hc : 0 < c) (hw : 0 < w) :
    Real.exp (-(c * w)) ≤ 2 / (c * w) ^ 2 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  have := Real.quadratic_le_exp_of_nonneg (x := c * w) (by positivity)
  nlinarith [mul_pos hc hw]

/-! ## The time scale `T = ⌈w²/2⌉` -/

/-- The time scale `T = ⌈w²/2⌉`. -/
def krT (w : ℝ) : ℕ := ⌈w ^ 2 / 2⌉₊

theorem krT_pos {w : ℝ} (hw : 1 ≤ w) : 1 ≤ krT w := by
  have hw0 : 0 < w := lt_of_lt_of_le one_pos hw
  exact Nat.ceil_pos.2 (by positivity)

theorem krT_le {w : ℝ} (hw : 1 ≤ w) : (krT w : ℝ) ≤ w ^ 2 := by
  unfold krT
  rcases le_or_gt 2 (w ^ 2) with h | h
  · have := Nat.ceil_lt_add_one (R := ℝ) (a := w ^ 2 / 2) (by positivity)
    linarith
  · have h1 : ⌈w ^ 2 / 2⌉₊ ≤ 1 := Nat.ceil_le.2 (by push_cast; linarith)
    have h1' : ((⌈w ^ 2 / 2⌉₊ : ℕ) : ℝ) ≤ 1 := by exact_mod_cast h1
    nlinarith

theorem krT_ge (w : ℝ) : w ^ 2 ≤ 2 * (krT w : ℝ) := by
  have := Nat.le_ceil (w ^ 2 / 2)
  unfold krT
  linarith

/-! ## The geometric tail in `√λ` -/

namespace KrBand

variable {ν} {θ vlo vhi K L w A a' : ℝ}

theorem sqrt_lam_nonneg (_H : KrBand D θ vlo vhi K L ν f w A a β a') :
    0 ≤ Real.sqrt (krLam D vlo vhi w) := Real.sqrt_nonneg _

theorem one_sub_sqrt_lam (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    krKappa D vlo vhi / (2 * w ^ 2) ≤ 1 - Real.sqrt (krLam D vlo vhi w) :=
  one_sub_sqrt_krLam_ge H.hD H.hθ H.hvlo H.hvhi H.hν H.hw

theorem sqrt_lam_lt_one (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    Real.sqrt (krLam D vlo vhi w) < 1 := by
  have h := H.one_sub_sqrt_lam
  have hκ := H.kappa_pos
  have hw0 := H.hw0
  have : 0 < krKappa D vlo vhi / (2 * w ^ 2) := by positivity
  linarith

/-- `1/(1 - √λ) ≤ 2 w²/κ`. -/
theorem inv_one_sub_sqrt_lam (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    1 / (1 - Real.sqrt (krLam D vlo vhi w)) ≤ 2 * w ^ 2 / krKappa D vlo vhi := by
  have h := H.one_sub_sqrt_lam
  have hκ := H.kappa_pos
  have hw0 := H.hw0
  have h1 : 0 < 1 - Real.sqrt (krLam D vlo vhi w) := by linarith [H.sqrt_lam_lt_one]
  rw [div_le_div_iff₀ h1 hκ]
  have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * w ^ 2)).1 h
  linarith

theorem geom_tail (H : KrBand D θ vlo vhi K L ν f w A a β a') (N : ℕ) :
    ∑ j ∈ Finset.range N, Real.sqrt (krLam D vlo vhi w) ^ j ≤ 2 * w ^ 2 / krKappa D vlo vhi :=
  (kr_geom_sum_le H.sqrt_lam_nonneg H.sqrt_lam_lt_one N).trans H.inv_one_sub_sqrt_lam

theorem geom_tail_mul (H : KrBand D θ vlo vhi K L ν f w A a β a') (N : ℕ) :
    ∑ j ∈ Finset.range N, (j : ℝ) * Real.sqrt (krLam D vlo vhi w) ^ j ≤
      (2 * w ^ 2 / krKappa D vlo vhi) ^ 2 := by
  refine (kr_geom_sum_mul_le H.sqrt_lam_nonneg H.sqrt_lam_lt_one N).trans ?_
  rw [one_div, ← inv_pow, ← one_div]
  exact pow_le_pow_left₀ (div_nonneg zero_le_one (by linarith [H.sqrt_lam_lt_one]))
    H.inv_one_sub_sqrt_lam 2

theorem hT1 (H : KrBand D θ vlo vhi K L ν f w A a β a') : 1 ≤ krT w := krT_pos H.hw

theorem hTw (H : KrBand D θ vlo vhi K L ν f w A a β a') : (krT w : ℝ) ≤ w ^ 2 := krT_le H.hw

theorem hwT (_H : KrBand D θ vlo vhi K L ν f w A a β a') : w ^ 2 ≤ 2 * (krT w : ℝ) := krT_ge w

end KrBand

/-! ## `O_b^±`: the Green survival sum -/

/-- Green survival constant `C_O = 1 + 2K + 2 C₃/κ`. -/
def krCO (D K L vlo vhi : ℝ) : ℝ := 1 + 2 * K + 2 * krC₃ D K L / krKappa D vlo vhi

/-- **(row), first half**: `∑_{n < N} s_n(b) ≤ C_O (1 + A) w` for every `N`. -/
theorem sum_krSurv_bdry_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (N : ℕ) :
    ∑ n ∈ Finset.range N, krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤
      krCO D K L vlo vhi * (1 + A) * w := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hK := H.hK
  have hκ := H.kappa_pos
  have hC₃ : 0 ≤ krC₃ D K L := Real.sqrt_nonneg _
  set T := krT w with hTdef
  have hT1 := H.hT1
  have hTw := H.hTw
  have hwT := H.hwT
  have hF : ∀ n, 0 ≤ krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b :=
    fun n => krSurv_nonneg H.hJ ν β a' n b
  refine (kr_sum_split hF T N).trans ?_
  -- medium block
  have h1 : ∑ n ∈ Finset.range T, krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤
      1 + 2 * K * (1 + A) * w := by
    obtain ⟨T', hT'⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
    rw [hT', Finset.sum_range_succ']
    have h2 : ∑ i ∈ Finset.range T', krSurv (Icc 0 w) (ν : Measure ℝ) β a' (i + 1) b ≤
        ∑ i ∈ Finset.range T', K * (1 + A) * (1 / Real.sqrt ((i : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi' : ((i + 1 : ℕ) : ℝ) ≤ w ^ 2 := by
        have : ((i + 1 : ℕ) : ℝ) ≤ (T : ℝ) := by
          exact_mod_cast (by rw [hT']; exact Nat.succ_le_succ (Finset.mem_range.1 hi).le)
        linarith
      have := H.krSurv_medium hb (n := i + 1) (by omega) hi'
      rw [div_eq_mul_one_div] at this
      push_cast at this
      exact this
    rw [← Finset.mul_sum] at h2
    have h3 := kr_sum_inv_sqrt_le T'
    have hsT' : Real.sqrt (T' : ℝ) ≤ w := by
      rw [Real.sqrt_le_left hw0.le]
      have : (T' : ℝ) ≤ T := by exact_mod_cast (by omega : T' ≤ T)
      linarith
    have h4 : K * (1 + A) * ∑ i ∈ Finset.range T', 1 / Real.sqrt ((i : ℝ) + 1) ≤
        K * (1 + A) * (2 * w) :=
      mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
    have h5 := krSurv_le_one H.hJ ν β a' 0 b
    linarith
  -- large block
  have h6 : ∑ j ∈ Finset.range (N - T), krSurv (Icc 0 w) (ν : Measure ℝ) β a' (T + j) b ≤
      2 * krC₃ D K L / krKappa D vlo vhi * (1 + A) * w := by
    have h7 : ∀ j, krSurv (Icc 0 w) (ν : Measure ℝ) β a' (T + j) b ≤
        krC₃ D K L * (1 + A) / w * Real.sqrt (krLam D vlo vhi w) ^ j := fun j => by
      refine (krSurv_bdry_large ν H hb hT1 hTw hwT j).trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum fun j _ => h7 j).trans ?_
    rw [← Finset.mul_sum]
    calc krC₃ D K L * (1 + A) / w * ∑ j ∈ Finset.range (N - T), Real.sqrt (krLam D vlo vhi w) ^ j
        ≤ krC₃ D K L * (1 + A) / w * (2 * w ^ 2 / krKappa D vlo vhi) :=
          mul_le_mul_of_nonneg_left (H.geom_tail _) (by positivity)
      _ = 2 * krC₃ D K L / krKappa D vlo vhi * (1 + A) * w := by
          field_simp
  have h8 : 1 ≤ (1 + A) * w := by nlinarith
  unfold krCO
  nlinarith

theorem summable_krSurv_bdry {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) :
    Summable fun n => krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b :=
  summable_of_sum_range_le (fun n => krSurv_nonneg H.hJ ν β a' n b) (sum_krSurv_bdry_le ν H hb)

/-- **(row), first half**: `O_b^± = ∑_{n ≥ 0} s_n(b) ≤ C_O (1 + A) w`. -/
theorem tsum_krSurv_bdry_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) :
    ∑' n, krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ krCO D K L vlo vhi * (1 + A) * w :=
  Real.tsum_le_of_sum_range_le (fun n => krSurv_nonneg H.hJ ν β a' n b)
    (sum_krSurv_bdry_le ν H hb)

/-! ## The Green row sup -/

/-- Green row constant `C_G = 2 C₁ + 2 C₄/κ`. -/
def krCG (D K L vlo vhi : ℝ) : ℝ := 2 * krC₁ D K L + 2 * krC₄ D K L / krKappa D vlo vhi

/-- **(row), second half**: `∑_{n < N} q_{n+1}(b, z) ≤ C_G (1 + A) (1 + log w)` for all `N, z`. -/
theorem sum_krDens_bdry_row_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (z : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
      krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC₁ := krC₁_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hC₄ : 0 ≤ krC₄ D K L := Real.sqrt_nonneg _
  have hlogw : 0 ≤ Real.log w := Real.log_nonneg hw
  set T := krT w with hTdef
  have hT1 := H.hT1
  have hTw := H.hTw
  have hwT := H.hwT
  have hF : ∀ n, 0 ≤ krDens (Icc 0 w) ν f β a' (n + 1) b z :=
    fun n => krDens_nonneg ν H.hf0 _ _ _
  set M := 2 * T - 1 with hMdef
  have hM : M + 1 = 2 * T := by omega
  have hM1 : 1 ≤ M := by omega
  have hMr : (M : ℝ) + 1 = 2 * T := by exact_mod_cast hM
  refine (kr_sum_split hF M N).trans ?_
  -- medium block: n + 1 ≤ M ≤ 2 w²
  have h1 : ∑ n ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
      krC₁ D K L * (1 + A) * (2 + 2 * Real.log w) := by
    have h2 : ∑ n ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
        ∑ n ∈ Finset.range M, krC₁ D K L * (1 + A) * (1 / ((n : ℝ) + 1)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ 2 * w ^ 2 := by
        have : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hn)
        linarith
      have := krDens_bdry_medium ν H hb (n := n + 1) (by omega) hn' z
      rw [div_eq_mul_one_div] at this
      push_cast at this
      exact this
    rw [← Finset.mul_sum] at h2
    have h3 := kr_sum_inv_le_log hM1
    have hlog : Real.log (M : ℝ) ≤ 1 + 2 * Real.log w := by
      have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
      calc Real.log (M : ℝ) ≤ Real.log (2 * w ^ 2) := Real.log_le_log hM0 (by linarith)
        _ = Real.log 2 + 2 * Real.log w := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
            push_cast
            ring
        _ ≤ 1 + 2 * Real.log w := by
            have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
            linarith
    have h4 : krC₁ D K L * (1 + A) * ∑ n ∈ Finset.range M, 1 / ((n : ℝ) + 1) ≤
        krC₁ D K L * (1 + A) * (2 + 2 * Real.log w) :=
      mul_le_mul_of_nonneg_left (h3.trans (by linarith)) (by positivity)
    linarith
  -- large block: n = M + j, n + 1 = T + j + T
  have h5 : ∑ j ∈ Finset.range (N - M), krDens (Icc 0 w) ν f β a' (M + j + 1) b z ≤
      2 * krC₄ D K L / krKappa D vlo vhi * (1 + A) := by
    have h6 : ∀ j, krDens (Icc 0 w) ν f β a' (M + j + 1) b z ≤
        krC₄ D K L * (1 + A) / w ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j := fun j => by
      have e : M + j + 1 = T + j + T := by omega
      rw [e]
      refine (krDens_bdry_row_large ν H hb hT1 hTw hwT j z).trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum fun j _ => h6 j).trans ?_
    rw [← Finset.mul_sum]
    calc krC₄ D K L * (1 + A) / w ^ 2 *
          ∑ j ∈ Finset.range (N - M), Real.sqrt (krLam D vlo vhi w) ^ j
        ≤ krC₄ D K L * (1 + A) / w ^ 2 * (2 * w ^ 2 / krKappa D vlo vhi) :=
          mul_le_mul_of_nonneg_left (H.geom_tail _) (by positivity)
      _ = 2 * krC₄ D K L / krKappa D vlo vhi * (1 + A) := by
          field_simp
  have h7 : 0 ≤ 2 * krC₄ D K L / krKappa D vlo vhi * (1 + A) * Real.log w := by positivity
  unfold krCG
  nlinarith

theorem summable_krDens_bdry_row {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (z : ℝ) :
    Summable fun n => krDens (Icc 0 w) ν f β a' (n + 1) b z :=
  summable_of_sum_range_le (fun n => krDens_nonneg ν H.hf0 (n + 1) b z)
    (sum_krDens_bdry_row_le ν H hb z)

/-- **(row), second half**: `∑_{n ≥ 1} q_n(b, z) ≤ C_G (1 + A) (1 + log w)`, uniformly in `z`. -/
theorem tsum_krDens_bdry_row_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) (z : ℝ) :
    ∑' n, krDens (Icc 0 w) ν f β a' (n + 1) b z ≤
      krCG D K L vlo vhi * (1 + A) * (1 + Real.log w) :=
  Real.tsum_le_of_sum_range_le (fun n => krDens_nonneg ν H.hf0 (n + 1) b z)
    (sum_krDens_bdry_row_le ν H hb z)

/-! ## The opposite-side pin sum -/

/-- Pin-sum constant `C_P = 3D/c₀² + 9 C_pin + 6 C₂/κ`. -/
def krCP (D θ K L vlo vhi : ℝ) : ℝ :=
  3 * D / krC₀ D θ ^ 2 + 9 * krCpin D K L + 6 * krC₂ D K L / krKappa D vlo vhi

/-- The medium part of the pin sum, `∑_{n < M} q_{n+1}(b, b')` with `M ≤ 2 w²`, is at most
`(3D/c₀² + 9 C_pin) (1 + A)² / √w` when `b ≠ b'` and `A ≤ w`. -/
theorem sum_krDens_bdry_pin_medium_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b') {M : ℕ} (hMw : (M : ℝ) ≤ 2 * w ^ 2) :
    ∑ n ∈ Finset.range M, krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      (3 * D / krC₀ D θ ^ 2 + 9 * krCpin D K L) * (1 + A) ^ 2 / Real.sqrt w := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hD0 := H.hD0
  have hc₀ := krC₀_pos H.hD H.hθ
  have hCpin := krCpin_nonneg (K := K) H.hD0 H.hL0.le
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw0
  have hsw1 : Real.sqrt w ≤ w := by rw [Real.sqrt_le_left hw0.le]; nlinarith
  have hA1 : 1 ≤ (1 + A) ^ 2 := one_le_pow₀ (by linarith)
  have hF : ∀ n, 0 ≤ krDens (Icc 0 w) ν f β a' (n + 1) b b' :=
    fun n => krDens_nonneg ν H.hf0 _ _ _
  set N₀ := ⌊w / 4⌋₊ with hN₀def
  have hN₀w : (N₀ : ℝ) ≤ w / 4 := Nat.floor_le (by positivity)
  have hN₀w' : w / 4 < (N₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine (kr_sum_split hF N₀ M).trans ?_
  -- short block
  have h1 : ∑ n ∈ Finset.range N₀, krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      3 * D / krC₀ D θ ^ 2 / Real.sqrt w := by
    have h2 : ∑ n ∈ Finset.range N₀, krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
        ∑ _n ∈ Finset.range N₀, 6 * D * Real.exp (-(krC₀ D θ * w)) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ w / 4 := by
        have : ((n + 1 : ℕ) : ℝ) ≤ (N₀ : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hn)
        linarith
      exact krDens_bdry_pin_short ν H hAw hb hb' hbb (by omega) hn'
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have he := kr_exp_neg_le hc₀ hw0
    have h3 : (N₀ : ℝ) * (6 * D * Real.exp (-(krC₀ D θ * w))) ≤
        w / 4 * (6 * D * (2 / (krC₀ D θ * w) ^ 2)) :=
      mul_le_mul hN₀w (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
        (by positivity)
    have h4 : w / 4 * (6 * D * (2 / (krC₀ D θ * w) ^ 2)) = 3 * D / krC₀ D θ ^ 2 / w := by
      field_simp
      ring
    have h5 : 3 * D / krC₀ D θ ^ 2 / w ≤ 3 * D / krC₀ D θ ^ 2 / Real.sqrt w :=
      div_le_div_of_nonneg_left (by positivity) hsw hsw1
    linarith
  -- medium block: n = N₀ + j, N₀ + j + 1 ≤ M ≤ 2 w²
  have h6 : ∑ j ∈ Finset.range (M - N₀), krDens (Icc 0 w) ν f β a' (N₀ + j + 1) b b' ≤
      9 * krCpin D K L * (1 + A) ^ 2 / Real.sqrt w := by
    have h7 : ∑ j ∈ Finset.range (M - N₀), krDens (Icc 0 w) ν f β a' (N₀ + j + 1) b b' ≤
        ∑ j ∈ Finset.range (M - N₀), krCpin D K L * (1 + A) ^ 2 *
          (1 / ((((N₀ + j : ℕ) : ℝ) + 1) * Real.sqrt (((N₀ + j : ℕ) : ℝ) + 1))) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : ((N₀ + j + 1 : ℕ) : ℝ) ≤ 2 * w ^ 2 := by
        have : ((N₀ + j + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast (by have := Finset.mem_range.1 hj; omega : N₀ + j + 1 ≤ M)
        linarith
      have := krDens_bdry_pin_medium ν H hb hb' (n := N₀ + j + 1) (by omega) hj'
      rw [div_eq_mul_one_div] at this
      have e : ((N₀ + j + 1 : ℕ) : ℝ) = ((N₀ + j : ℕ) : ℝ) + 1 := by push_cast; ring
      rw [e] at this
      exact this
    rw [← Finset.mul_sum] at h7
    refine h7.trans ?_
    -- the telescoping sum is at most `9/√w`
    have h8 : ∑ j ∈ Finset.range (M - N₀),
        1 / ((((N₀ + j : ℕ) : ℝ) + 1) * Real.sqrt (((N₀ + j : ℕ) : ℝ) + 1)) ≤
        9 / Real.sqrt w := by
      rcases le_or_gt 8 w with h8w | h8w
      · have hN₀1 : 1 ≤ N₀ := by
          have h0 : (0 : ℝ) < (N₀ : ℝ) := by linarith
          have : 0 < N₀ := Nat.cast_pos.1 h0
          omega
        refine (kr_sum_inv_pow32_tail_le hN₀1 _).trans ?_
        have hN₀' : w / 8 ≤ (N₀ : ℝ) := by linarith
        have hsN : 0 < Real.sqrt (N₀ : ℝ) := Real.sqrt_pos.2 (by linarith)
        have hs3 : Real.sqrt w ≤ 3 * Real.sqrt (N₀ : ℝ) := by
          rw [Real.sqrt_le_left (by positivity), mul_pow, Real.sq_sqrt (by linarith)]
          linarith
        rw [div_le_div_iff₀ hsN hsw]
        linarith
      · -- `w < 8`: the whole sum is at most `3 ≤ 9/√w`
        have h9 : ∑ j ∈ Finset.range (M - N₀),
            1 / ((((N₀ + j : ℕ) : ℝ) + 1) * Real.sqrt (((N₀ + j : ℕ) : ℝ) + 1)) ≤
            ∑ i ∈ Finset.range (N₀ + (M - N₀)),
              1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1)) := by
          rw [Finset.sum_range_add]
          have : 0 ≤ ∑ i ∈ Finset.range N₀, 1 / (((i : ℝ) + 1) * Real.sqrt ((i : ℝ) + 1)) :=
            Finset.sum_nonneg fun i _ => by positivity
          linarith
        refine (h9.trans (kr_sum_inv_pow32_le _)).trans ?_
        rw [le_div_iff₀ hsw]
        have : Real.sqrt w < 3 := by
          rw [Real.sqrt_lt' (by norm_num)]
          linarith
        linarith
    calc krCpin D K L * (1 + A) ^ 2 * ∑ j ∈ Finset.range (M - N₀),
          1 / ((((N₀ + j : ℕ) : ℝ) + 1) * Real.sqrt (((N₀ + j : ℕ) : ℝ) + 1))
        ≤ krCpin D K L * (1 + A) ^ 2 * (9 / Real.sqrt w) :=
          mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = 9 * krCpin D K L * (1 + A) ^ 2 / Real.sqrt w := by ring
  have h10 : 3 * D / krC₀ D θ ^ 2 / Real.sqrt w ≤
      3 * D / krC₀ D θ ^ 2 * (1 + A) ^ 2 / Real.sqrt w := by
    rw [div_le_div_iff_of_pos_right hsw]
    have : 0 ≤ 3 * D / krC₀ D θ ^ 2 := by positivity
    nlinarith
  have e : (3 * D / krC₀ D θ ^ 2 + 9 * krCpin D K L) * (1 + A) ^ 2 / Real.sqrt w =
      3 * D / krC₀ D θ ^ 2 * (1 + A) ^ 2 / Real.sqrt w +
        9 * krCpin D K L * (1 + A) ^ 2 / Real.sqrt w := by ring
  rw [e]
  linarith

/-- **(pin), second display**: `∑_{n < N} q_{n+1}(b, b') ≤ C_P (1 + A)² / √w` for `b ≠ b'`,
`A ≤ w`, every `N`. -/
theorem sum_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b') (N : ℕ) :
    ∑ n ∈ Finset.range N, krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC₂ := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.2 hw0
  have hsw1 : Real.sqrt w ≤ w := by rw [Real.sqrt_le_left hw0.le]; nlinarith
  set T := krT w with hTdef
  have hT1 := H.hT1
  have hTw := H.hTw
  have hwT := H.hwT
  have hF : ∀ n, 0 ≤ krDens (Icc 0 w) ν f β a' (n + 1) b b' :=
    fun n => krDens_nonneg ν H.hf0 _ _ _
  set M := 2 * T - 1 with hMdef
  have hM : M + 1 = 2 * T := by omega
  have hMr : (M : ℝ) + 1 = 2 * T := by exact_mod_cast hM
  refine (kr_sum_split hF M N).trans ?_
  have h1 := sum_krDens_bdry_pin_medium_le ν H hAw hb hb' hbb (M := M) (by linarith)
  -- large block
  have h5 : ∑ j ∈ Finset.range (N - M), krDens (Icc 0 w) ν f β a' (M + j + 1) b b' ≤
      6 * krC₂ D K L / krKappa D vlo vhi * (1 + A) ^ 2 / Real.sqrt w := by
    have h6 : ∀ j, krDens (Icc 0 w) ν f β a' (M + j + 1) b b' ≤
        3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 * Real.sqrt (krLam D vlo vhi w) ^ j := fun j => by
      have e : M + j + 1 = T + j + T := by omega
      rw [e]
      refine (krDens_bdry_pin_large ν H hb hb' hT1 hTw hwT j).trans (le_of_eq ?_)
      ring
    refine (Finset.sum_le_sum fun j _ => h6 j).trans ?_
    rw [← Finset.mul_sum]
    calc 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 *
          ∑ j ∈ Finset.range (N - M), Real.sqrt (krLam D vlo vhi w) ^ j
        ≤ 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 * (2 * w ^ 2 / krKappa D vlo vhi) :=
          mul_le_mul_of_nonneg_left (H.geom_tail _) (by positivity)
      _ = 6 * krC₂ D K L / krKappa D vlo vhi * (1 + A) ^ 2 / w := by
          field_simp
          ring
      _ ≤ 6 * krC₂ D K L / krKappa D vlo vhi * (1 + A) ^ 2 / Real.sqrt w :=
          div_le_div_of_nonneg_left (by positivity) hsw hsw1
  have e : krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w =
      (3 * D / krC₀ D θ ^ 2 + 9 * krCpin D K L) * (1 + A) ^ 2 / Real.sqrt w +
        6 * krC₂ D K L / krKappa D vlo vhi * (1 + A) ^ 2 / Real.sqrt w := by
    unfold krCP
    ring
  rw [e]
  linarith

theorem summable_krDens_bdry_pin {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b') :
    Summable fun n => krDens (Icc 0 w) ν f β a' (n + 1) b b' :=
  summable_of_sum_range_le (fun n => krDens_nonneg ν H.hf0 (n + 1) b b')
    (sum_krDens_bdry_pin_le ν H hAw hb hb' hbb)

/-- **(pin), second display**: `∑_{n ≥ 1} q_n(b, b') ≤ C_P (1 + A)² w^{-1/2}` for `b ≠ b'`. -/
theorem tsum_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b') :
    ∑' n, krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      krCP D θ K L vlo vhi * (1 + A) ^ 2 / Real.sqrt w :=
  Real.tsum_le_of_sum_range_le (fun n => krDens_nonneg ν H.hf0 (n + 1) b b')
    (sum_krDens_bdry_pin_le ν H hAw hb hb' hbb)

/-! ## The weighted pin sums `B_↑ + B_↓` -/

/-- Weighted pin constant `C_B = 6 C_pin + 18 C₂/κ + 12 C₂/κ²`. -/
def krCB (D K L vlo vhi : ℝ) : ℝ :=
  6 * krCpin D K L + 18 * krC₂ D K L / krKappa D vlo vhi +
    12 * krC₂ D K L / krKappa D vlo vhi ^ 2

/-- **(pin), first display**: `∑_{n < N} (n + 1 + w) q_{n+1}(b, b') ≤ C_B (1 + A)² w` for boundary
`b, b'` and every `N`.  Since `|n - w| ≤ n + w`, this bounds `B_↑` and `B_↓`. -/
theorem sum_weighted_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      krCB D K L vlo vhi * (1 + A) ^ 2 * w := by
  have hw0 := H.hw0
  have hw := H.hw
  have hA := H.hA
  have hκ := H.kappa_pos
  have hC₂ := krC₂_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hCpin := krCpin_nonneg (K := K) H.hD0 H.hL0.le
  set T := krT w with hTdef
  have hT1 := H.hT1
  have hTw := H.hTw
  have hwT := H.hwT
  have hF : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' :=
    fun n => mul_nonneg (by positivity) (krDens_nonneg ν H.hf0 _ _ _)
  set M := 2 * T - 1 with hMdef
  have hM : M + 1 = 2 * T := by omega
  have hMr : (M : ℝ) + 1 = 2 * T := by exact_mod_cast hM
  refine (kr_sum_split hF M N).trans ?_
  -- medium block
  have h1 : ∑ n ∈ Finset.range M, ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      6 * krCpin D K L * (1 + A) ^ 2 * w := by
    have h2 : ∑ n ∈ Finset.range M,
        ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
        ∑ n ∈ Finset.range M, krCpin D K L * (1 + A) ^ 2 *
          (1 / Real.sqrt ((n : ℝ) + 1) + w * (1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)))) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn' : ((n + 1 : ℕ) : ℝ) ≤ 2 * w ^ 2 := by
        have : ((n + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hn)
        linarith
      have hq := krDens_bdry_pin_medium ν H hb hb' (n := n + 1) (by omega) hn'
      push_cast at hq
      have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      calc ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b'
          ≤ ((n : ℝ) + 1 + w) *
              (krCpin D K L * (1 + A) ^ 2 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ = krCpin D K L * (1 + A) ^ 2 *
              (1 / Real.sqrt ((n : ℝ) + 1) +
                w * (1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)))) := by
            field_simp
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum] at h2
    have h3 := kr_sum_inv_sqrt_le M
    have h4 := kr_sum_inv_pow32_le M
    have hsM : Real.sqrt (M : ℝ) ≤ 3 / 2 * w := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith
    have h5 : ∑ n ∈ Finset.range M, 1 / Real.sqrt ((n : ℝ) + 1) +
        w * ∑ n ∈ Finset.range M, 1 / (((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1)) ≤ 6 * w := by
      have := mul_le_mul_of_nonneg_left h4 hw0.le
      linarith
    calc _ ≤ _ := h2
      _ ≤ krCpin D K L * (1 + A) ^ 2 * (6 * w) :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = 6 * krCpin D K L * (1 + A) ^ 2 * w := by ring
  -- large block: n = M + j, weight ≤ 3 w² + j
  have h6 : ∑ j ∈ Finset.range (N - M),
      (((M + j : ℕ) : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (M + j + 1) b b' ≤
      (18 * krC₂ D K L / krKappa D vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi ^ 2) *
        (1 + A) ^ 2 * w := by
    have h7 : ∀ j, (((M + j : ℕ) : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (M + j + 1) b b' ≤
        3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 *
          (3 * w ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j +
            (j : ℝ) * Real.sqrt (krLam D vlo vhi w) ^ j) := fun j => by
      have e : M + j + 1 = T + j + T := by omega
      rw [e]
      have hq := krDens_bdry_pin_large ν H hb hb' hT1 hTw hwT j
      have hwt : ((M + j : ℕ) : ℝ) + 1 + w ≤ 3 * w ^ 2 + j := by
        push_cast
        nlinarith
      have hr := H.sqrt_lam_nonneg
      calc (((M + j : ℕ) : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (T + j + T) b b'
          ≤ (3 * w ^ 2 + j) *
              (3 * krC₂ D K L * (1 + A) ^ 2 * Real.sqrt (krLam D vlo vhi w) ^ j / w ^ 3) :=
            mul_le_mul hwt hq (krDens_nonneg ν H.hf0 _ _ _) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum fun j _ => h7 j).trans ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hg1 := H.geom_tail (N - M)
    have hg2 := H.geom_tail_mul (N - M)
    have hbd : 3 * w ^ 2 * ∑ j ∈ Finset.range (N - M), Real.sqrt (krLam D vlo vhi w) ^ j +
        ∑ j ∈ Finset.range (N - M), (j : ℝ) * Real.sqrt (krLam D vlo vhi w) ^ j ≤
        3 * w ^ 2 * (2 * w ^ 2 / krKappa D vlo vhi) + (2 * w ^ 2 / krKappa D vlo vhi) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hg1 (by positivity : (0 : ℝ) ≤ 3 * w ^ 2)
      linarith
    calc _ ≤ 3 * krC₂ D K L * (1 + A) ^ 2 / w ^ 3 *
          (3 * w ^ 2 * (2 * w ^ 2 / krKappa D vlo vhi) + (2 * w ^ 2 / krKappa D vlo vhi) ^ 2) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = (18 * krC₂ D K L / krKappa D vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi ^ 2) *
          (1 + A) ^ 2 * w := by
          field_simp
          ring
  have e : krCB D K L vlo vhi * (1 + A) ^ 2 * w =
      6 * krCpin D K L * (1 + A) ^ 2 * w +
        (18 * krC₂ D K L / krKappa D vlo vhi + 12 * krC₂ D K L / krKappa D vlo vhi ^ 2) *
          (1 + A) ^ 2 * w := by
    unfold krCB
    ring
  rw [e]
  linarith

theorem summable_weighted_krDens_bdry_pin {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) :
    Summable fun n : ℕ => ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' :=
  summable_of_sum_range_le
    (fun n => mul_nonneg (by linarith [H.hw0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (krDens_nonneg ν H.hf0 (n + 1) b b'))
    (sum_weighted_krDens_bdry_pin_le ν H hb hb')

/-- **(pin), first display**: `∑_{n ≥ 1} (n + w) q_n(b, b') ≤ C_B (1 + A)² w`. -/
theorem tsum_weighted_krDens_bdry_pin_le {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) :
    ∑' n : ℕ, ((n : ℝ) + 1 + w) * krDens (Icc 0 w) ν f β a' (n + 1) b b' ≤
      krCB D K L vlo vhi * (1 + A) ^ 2 * w :=
  Real.tsum_le_of_sum_range_le
    (fun n => mul_nonneg (by linarith [H.hw0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      (krDens_nonneg ν H.hf0 (n + 1) b b'))
    (sum_weighted_krDens_bdry_pin_le ν H hb hb')

end

end PGM
