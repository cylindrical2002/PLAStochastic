import PLAStochastic.Index.OneLayer.ThresholdMargin

/-!
# WP3 tree switch: the deterministic comparison of two ALG-OPT stops

Source: `research/2026-09-28-gep-closure/memory-route.md` §6, deterministic part of the proof of
(tree-prob).  Following `research/2026-09-29-lean-gep-shadow-defects/README.md` (line B), the
full-scale margin of the source is replaced by the near-tie event (`nearTie`,
`PLAStochastic/Index/OneLayer/ThresholdMargin.lean`) of the passive path at its own stop, and the small-sum event of the source
is replaced by the first passive gap: every key `y_k`, `k ≥ 1`, is at least `y_1 = Y_0`.

* `abs_slope_mul_le`: a line whose rank error is at most `e` at the key `z_0 = 0` and at the
  key `z_k ≥ 0` has `|a| z_k ≤ k + 2e`.
* `abs_rank_err_of_close`: moving a key by at most `h` changes the rank error of a line of
  slope `a` by at most `|a| h`.
* `gapSegLen_eq_of_close`: let the passive gaps `gy` be nonnegative with `gy 0 ≥ s`, let the
  passive stop be `t ≤ R` with no near-tie of tolerance `u` for `t` or `t + 1` keys, and let
  the key paths be `h`-close up to `R`.  If `2 h ≤ s` and `2 (R + 2 eps) h ≤ u s`, the active
  stop equals `t`.
-/

namespace PGM

theorem prefixAffineFeasible_mono_level {e e' : ℝ} {p : ℕ → ℝ} {n : ℕ}
    (h : prefixAffineFeasible e p n) (he : e ≤ e') : prefixAffineFeasible e' p n := by
  obtain ⟨a, b, hab⟩ := h
  exact ⟨a, b, fun i hi => (hab i hi).trans he⟩

/-- **Slope bound**: rank error at most `e` at `z_0 = 0` and at `z_k ≥ 0` forces
`|a| z_k ≤ k + 2e`. -/
theorem abs_slope_mul_le {e a b : ℝ} {z : ℕ → ℝ} {k : ℕ} (hz0 : z 0 = 0) (hzk : 0 ≤ z k)
    (h0 : |((0 : ℕ) : ℝ) - (a * z 0 + b)| ≤ e) (hk : |(k : ℝ) - (a * z k + b)| ≤ e) :
    |a| * z k ≤ k + 2 * e := by
  rw [hz0, mul_zero, zero_add, Nat.cast_zero, zero_sub, abs_neg] at h0
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 := abs_le.mp h0
  have h2 := abs_le.mp hk
  have e1 : |a| * z k = |a * z k| := by rw [abs_mul, abs_of_nonneg hzk]
  rw [e1, abs_le]
  constructor <;> linarith

/-- **Perturbation**: moving a key by at most `h` changes the rank error by at most `|a| h`. -/
theorem abs_rank_err_of_close {e a b h x y : ℝ} {i : ℕ} (hy : |(i : ℝ) - (a * y + b)| ≤ e)
    (hxy : |x - y| ≤ h) : |(i : ℝ) - (a * x + b)| ≤ e + |a| * h := by
  have e1 : (i : ℝ) - (a * x + b) = ((i : ℝ) - (a * y + b)) + (-(a * (x - y))) := by ring
  rw [e1]
  calc |((i : ℝ) - (a * y + b)) + (-(a * (x - y)))|
      ≤ |(i : ℝ) - (a * y + b)| + |-(a * (x - y))| := abs_add_le _ _
    _ = |(i : ℝ) - (a * y + b)| + |a| * |x - y| := by rw [abs_neg, abs_mul]
    _ ≤ e + |a| * h := add_le_add hy (mul_le_mul_of_nonneg_left hxy (abs_nonneg a))

theorem gapKeys_mono_of_nonneg {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) {j k : ℕ} (hjk : j ≤ k) :
    gapKeys g j ≤ gapKeys g k :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk) fun i _ _ => hg i

theorem le_gapKeys_of_nonneg {g : ℕ → ℝ} (hg : ∀ i, 0 ≤ g i) {k : ℕ} (hk : 1 ≤ k) :
    g 0 ≤ gapKeys g k := by
  have e1 : gapKeys g 1 = g 0 := by simp [gapKeys]
  rw [← e1]
  exact gapKeys_mono_of_nonneg hg hk

/-- The residual between two key paths is at most the sum of the absolute gap differences. -/
theorem abs_gapKeys_sub_le (gx gy : ℕ → ℝ) {k R : ℕ} (hk : k ≤ R) :
    |gapKeys gx k - gapKeys gy k| ≤ ∑ j ∈ Finset.range R, |gx j - gy j| := by
  have e1 : gapKeys gx k - gapKeys gy k = ∑ j ∈ Finset.range k, (gx j - gy j) := by
    simp only [gapKeys, Finset.sum_sub_distrib]
  rw [e1]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk) fun j _ _ => abs_nonneg _)

/-- **Deterministic tree switch.**  Without a near-tie of the passive path at its stop `t ≤ R`,
two `h`-close key paths have the same ALG-OPT stop. -/
theorem gapSegLen_eq_of_close {eps s h u : ℝ} {R t : ℕ} {gx gy : ℕ → ℝ}
    (heps : 1 ≤ eps) (hs : 0 < s) (hh : 0 ≤ h) (hhs : 2 * h ≤ s)
    (hu : 2 * ((R : ℝ) + 2 * eps) * h ≤ u * s)
    (hy : ∀ i, 0 ≤ gy i) (hy0 : s ≤ gy 0)
    (hres : ∀ k ≤ R, |gapKeys gx k - gapKeys gy k| ≤ h)
    (hT : gapSegLen eps gy = t) (htR : t ≤ R)
    (hnt : ¬ nearTie eps u (gapKeys gy) t) (hnt' : ¬ nearTie eps u (gapKeys gy) (t + 1)) :
    gapSegLen eps gx = t := by
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  have hu0 : 0 ≤ u := by
    have h1 : 0 ≤ u * s := le_trans (by positivity) hu
    by_contra hneg
    push Not at hneg
    have : u * s < 0 := mul_neg_of_neg_of_pos hneg hs
    linarith
  have ht3 : 3 ≤ t := by
    have C := ConstantLineLengthCertificate.of_nonneg (by linarith : (0 : ℝ) ≤ eps)
    have h1 := constantLine_le_segLen C (gapKeys gy)
    have h2 := C.q_ge_three heps
    change (C.q : ℕ∞) ≤ gapSegLen eps gy at h1
    rw [hT] at h1
    have : C.q ≤ t := by exact_mod_cast h1
    omega
  obtain ⟨hfy, hnfy⟩ := (firstFailureAt_iff_segLen_eq (eps := eps) (p := gapKeys gy)).mpr hT
  -- (i) the passive line at level `eps - u` is an active line at level `eps`
  have hfy' : prefixAffineFeasible (eps - u) (gapKeys gy) t := by
    by_contra hc
    exact hnt ⟨prefixAffineFeasible_mono_level hfy (by linarith), hc⟩
  have hfx : prefixAffineFeasible eps (gapKeys gx) t := by
    obtain ⟨a, b, hab⟩ := hfy'
    have hk := hab (t - 1) (by omega)
    have h0 := hab 0 (by omega)
    have hyk : s ≤ gapKeys gy (t - 1) := hy0.trans (le_gapKeys_of_nonneg hy (by omega))
    have hslope := abs_slope_mul_le (gapKeys_zero gy) (by linarith) h0 hk
    have hcast : ((t - 1 : ℕ) : ℝ) ≤ R := by exact_mod_cast (by omega : t - 1 ≤ R)
    have has : |a| * s ≤ R + 2 * eps := by
      calc |a| * s ≤ |a| * gapKeys gy (t - 1) := mul_le_mul_of_nonneg_left hyk (abs_nonneg a)
        _ ≤ ((t - 1 : ℕ) : ℝ) + 2 * (eps - u) := hslope
        _ ≤ R + 2 * eps := by linarith
    have hah : |a| * h ≤ u / 2 := by
      have h1 := mul_le_mul_of_nonneg_right has hh
      have h2 : |a| * h * s ≤ u / 2 * s := by nlinarith
      exact le_of_mul_le_mul_right h2 hs
    refine ⟨a, b, fun i hi => ?_⟩
    have h1 := abs_rank_err_of_close (hab i hi) (hres i (by omega))
    linarith
  -- (ii) an active line for `t + 1` keys would be a passive line at level `eps + u`
  have hnfx : ¬ prefixAffineFeasible eps (gapKeys gx) (t + 1) := by
    rintro ⟨a, b, hab⟩
    have hk := hab t (by omega)
    have h0 := hab 0 (by omega)
    have hyt : s ≤ gapKeys gy t := hy0.trans (le_gapKeys_of_nonneg hy (by omega))
    have hxt : s / 2 ≤ gapKeys gx t := by
      have := abs_le.mp (hres t htR)
      linarith
    have hslope := abs_slope_mul_le (gapKeys_zero gx) (by linarith) h0 hk
    have hcast : (t : ℝ) ≤ R := by exact_mod_cast htR
    have has : |a| * (s / 2) ≤ R + 2 * eps := by
      calc |a| * (s / 2) ≤ |a| * gapKeys gx t := mul_le_mul_of_nonneg_left hxt (abs_nonneg a)
        _ ≤ (t : ℝ) + 2 * eps := hslope
        _ ≤ R + 2 * eps := by linarith
    have hah : |a| * h ≤ u := by
      have h1 := mul_le_mul_of_nonneg_right has hh
      have h2 : |a| * h * s ≤ u * s := by nlinarith
      exact le_of_mul_le_mul_right h2 hs
    have hfy2 : prefixAffineFeasible (eps + u) (gapKeys gy) (t + 1) := by
      refine ⟨a, b, fun i hi => ?_⟩
      have hxy : |gapKeys gy i - gapKeys gx i| ≤ h := by
        rw [abs_sub_comm]; exact hres i (by omega)
      have h1 := abs_rank_err_of_close (hab i hi) hxy
      linarith
    have hfy3 : prefixAffineFeasible (eps - u) (gapKeys gy) (t + 1) := by
      by_contra hc
      exact hnt' ⟨hfy2, hc⟩
    exact hnfy (prefixAffineFeasible_mono_level hfy3 (by linarith))
  exact (firstFailureAt_iff_segLen_eq (eps := eps) (p := gapKeys gx)).mp ⟨hfx, hnfx⟩

end PGM
