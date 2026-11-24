import PLAStochastic.Index.GEP.SurvivalBound.Certificate.Geometry
import PLAStochastic.Index.GEP.SurvivalBound.KilledRow.Defs

/-!
# WP4 `SurvivalBound`: the three-block form of a certificate

Source: `research/2026-09-28-gep-closure/analytic-response.md` §3 (AR (6)–(7)); task P1, target 4
of `research/2026-09-30-lean-gep-direct-term/task-cert.md`.

For keys `p = gapKeys g` (so `p_t = g 0 + ⋯ + g (t-1)`), a slope `a` and a pair `i ≤ j ≤ k`, the
band condition `certBand eps a p k i` (`0 ≤ r_t(a) - r_i(a) ≤ 2ε` for `t ≤ k`, `r_t(a) = t - a p_t`)
splits into three walks in `J = [0, 2ε]`, written with `kWalk` (`PLAStochastic/Index/GEP/SurvivalBound/KilledRow/Defs.lean`,
`kWalk y₀ β a h l = y₀ + l β - a (h 0 + ⋯ + h (l-1))`) on shifted or reversed gap sequences:

* **prefix** `u_l = r_{i-l} - r_i = kWalk 0 (-1) (-a) (fun m => g (i - 1 - m)) l`, `l ≤ i`: the
  reversed walk over `g (i-1), …, g 0` with step `a x - 1`, started at `0`;
* **middle** `y_{i+l} = r_{i+l} - r_i = kWalk 0 1 a (fun m => g (i + m)) l`, `l ≤ j - i`: the forward
  walk over `g i, …, g (j-1)` with step `1 - a x`, started at `0`;
* **suffix** `y_{j+l} = r_{j+l} - r_i = kWalk y_j 1 a (fun m => g (j + m)) l`, `l ≤ k - j`: the forward
  walk over `g j, …, g (k-1)`, started at the middle end `y_j`
  (`cert_kWalk_rev`, `cert_kWalk_fwd`, `cert_kWalk_suffix`; `cert_band_iff_blocks`).

At the certificate slope `a = certSlope eps p i j` the middle walk ends at `y_j = 2ε`
(`cert_middle_end`), so the suffix starts at `2ε` (`certOK_iff_blocks`), and for every `a ≠ 0` the
last key is read off the two outer ends, `p_k = (k + u_i - w) / a` with `u_i` the prefix end and
`w = y_k` the suffix end (`cert_gapKeys_eq_ends`, `cert_gapKeys_eq_ends_certSlope`, AR (6)).  The
indicator of a certificate is the product of the three block indicators
(`cert_indicator_certOK_eq_prod`), the form consumed by the word expansion of `kRow`.
-/

namespace PGM

noncomputable section

open Finset

/-! ## Walks along shifted and reversed gap blocks -/

theorem cert_gapKeys_succ (g : ℕ → ℝ) (t : ℕ) : gapKeys g (t + 1) = gapKeys g t + g t :=
  Finset.sum_range_succ _ _

/-- The keys of the reversed block `g (s-1), g (s-2), …`: for `l ≤ s`,
`g (s-1) + ⋯ + g (s-l) = p_s - p_{s-l}`. -/
theorem cert_gapKeys_rev (g : ℕ → ℝ) {s : ℕ} :
    ∀ l ≤ s, gapKeys (fun m => g (s - 1 - m)) l = gapKeys g s - gapKeys g (s - l)
  | 0, _ => by simp [gapKeys_zero]
  | l + 1, hl => by
    rw [cert_gapKeys_succ, cert_gapKeys_rev g l (by omega)]
    have e : s - l = (s - (l + 1)) + 1 := by omega
    have e' : s - 1 - l = s - (l + 1) := by omega
    rw [e, cert_gapKeys_succ, e']
    ring

/-- **Forward block walk.**  Over the gaps `g s, g (s+1), …` the walk with step `1 - a x` from `y`
is `y` plus the residual rise from `s`: `kWalk y 1 a (g (s + ·)) l = y + r_{s+l}(a) - r_s(a)`. -/
theorem cert_kWalk_fwd (y a : ℝ) (g : ℕ → ℝ) (s l : ℕ) :
    kWalk y 1 a (fun m => g (s + m)) l =
      y + (certResid a (gapKeys g) (s + l) - certResid a (gapKeys g) s) := by
  simp only [kWalk, gapKeys_shift, certResid]
  push_cast
  ring

/-- **Reversed block walk.**  Over the gaps `g (s-1), g (s-2), …` the walk with step `a x - 1`
from `y` is `y` plus the residual change back to `s - l`:
`kWalk y (-1) (-a) (g (s - 1 - ·)) l = y + r_{s-l}(a) - r_s(a)` for `l ≤ s`. -/
theorem cert_kWalk_rev (y a : ℝ) (g : ℕ → ℝ) {s l : ℕ} (hl : l ≤ s) :
    kWalk y (-1) (-a) (fun m => g (s - 1 - m)) l =
      y + (certResid a (gapKeys g) (s - l) - certResid a (gapKeys g) s) := by
  simp only [kWalk, cert_gapKeys_rev g l hl, certResid]
  rw [Nat.cast_sub hl]
  ring

/-- The suffix walk from the middle end: `r_{j+l}(a) - r_i(a)`. -/
theorem cert_kWalk_suffix (a : ℝ) (g : ℕ → ℝ) {i j : ℕ} (hij : i ≤ j) (l : ℕ) :
    kWalk (kWalk 0 1 a (fun m => g (i + m)) (j - i)) 1 a (fun m => g (j + m)) l =
      certResid a (gapKeys g) (j + l) - certResid a (gapKeys g) i := by
  rw [cert_kWalk_fwd, cert_kWalk_fwd, Nat.add_sub_of_le hij]
  ring

/-! ## The three-block form -/

/-- **Three-block form of the band condition** (arbitrary slope `a`, `i ≤ j ≤ k`, keys
`gapKeys g`).  The residuals `r_t(a) - r_i(a)`, `t ≤ k`, stay in `[0, 2ε]` iff the reversed prefix
walk (step `a x - 1`, `i` steps from `0`), the middle walk (step `1 - a x`, `j - i` steps from `0`)
and the suffix walk (step `1 - a x`, `k - j` steps from the middle end) all stay in `[0, 2ε]`. -/
theorem cert_band_iff_blocks {eps a : ℝ} {g : ℕ → ℝ} {k i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    certBand eps a (gapKeys g) k i ↔
      (∀ l ≤ i, kWalk 0 (-1) (-a) (fun m => g (i - 1 - m)) l ∈ Set.Icc 0 (2 * eps)) ∧
      (∀ l ≤ j - i, kWalk 0 1 a (fun m => g (i + m)) l ∈ Set.Icc 0 (2 * eps)) ∧
      (∀ l ≤ k - j, kWalk (kWalk 0 1 a (fun m => g (i + m)) (j - i)) 1 a (fun m => g (j + m)) l ∈
        Set.Icc 0 (2 * eps)) := by
  have hpre : ∀ l ≤ i, kWalk 0 (-1) (-a) (fun m => g (i - 1 - m)) l =
      certResid a (gapKeys g) (i - l) - certResid a (gapKeys g) i := fun l hl => by
    rw [cert_kWalk_rev 0 a g hl, zero_add]
  have hmid : ∀ l, kWalk 0 1 a (fun m => g (i + m)) l =
      certResid a (gapKeys g) (i + l) - certResid a (gapKeys g) i := fun l => by
    rw [cert_kWalk_fwd, zero_add]
  constructor
  · intro h
    refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
    · rw [hpre l hl]
      exact h (i - l) (by omega)
    · rw [hmid]
      exact h (i + l) (by omega)
    · rw [cert_kWalk_suffix a g hij]
      exact h (j + l) (by omega)
  · rintro ⟨h1, h2, h3⟩ t ht
    rcases le_or_gt t i with hti | hit
    · have := h1 (i - t) (by omega)
      rwa [hpre _ (by omega), Nat.sub_sub_self hti] at this
    · rcases le_or_gt t j with htj | hjt
      · have := h2 (t - i) (by omega)
        rwa [hmid, Nat.add_sub_of_le hit.le] at this
      · have := h3 (t - j) (by omega)
        rwa [cert_kWalk_suffix a g hij, Nat.add_sub_of_le hjt.le] at this

/-- At the certificate slope the middle walk ends at `y_j = 2ε`. -/
theorem cert_middle_end {eps : ℝ} {g : ℕ → ℝ} {i j : ℕ} (hij : i ≤ j)
    (hne : gapKeys g i ≠ gapKeys g j) :
    kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun m => g (i + m)) (j - i) = 2 * eps := by
  rw [cert_kWalk_fwd, zero_add, Nat.add_sub_of_le hij, certResid_sub_certSlope hne]

/-- **Three-block form of a certificate** (`i ≤ j ≤ k`, `p_i ≠ p_j`, `a = certSlope eps p i j`,
`p = gapKeys g`): the prefix walk `kWalk 0 (-1) (-a)` over `g (i-1), …, g 0`, the middle walk
`kWalk 0 1 a` over `g i, …, g (j-1)` and the suffix walk `kWalk (2ε) 1 a` over
`g j, …, g (k-1)` stay in `[0, 2ε]`. -/
theorem certOK_iff_blocks {eps : ℝ} {g : ℕ → ℝ} {k i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k)
    (hne : gapKeys g i ≠ gapKeys g j) :
    certOK eps (gapKeys g) k i j ↔
      (∀ l ≤ i, kWalk 0 (-1) (-certSlope eps (gapKeys g) i j) (fun m => g (i - 1 - m)) l ∈
        Set.Icc 0 (2 * eps)) ∧
      (∀ l ≤ j - i, kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun m => g (i + m)) l ∈
        Set.Icc 0 (2 * eps)) ∧
      (∀ l ≤ k - j, kWalk (2 * eps) 1 (certSlope eps (gapKeys g) i j) (fun m => g (j + m)) l ∈
        Set.Icc 0 (2 * eps)) := by
  rw [certOK, cert_band_iff_blocks hij hjk, cert_middle_end hij hne]

/-- **The last key from the two outer ends** (AR (6)).  For `a ≠ 0` and `i ≤ j ≤ k`, with the
prefix end `u_i = kWalk 0 (-1) (-a) (g (i - 1 - ·)) i = a p_i - i` and the suffix end
`w = y_k = r_k(a) - r_i(a)`, one has `p_k = (k + u_i - w) / a`. -/
theorem cert_gapKeys_eq_ends {a : ℝ} (ha : a ≠ 0) {g : ℕ → ℝ} {k i j : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) :
    gapKeys g k = ((k : ℝ) + kWalk 0 (-1) (-a) (fun m => g (i - 1 - m)) i -
      kWalk (kWalk 0 1 a (fun m => g (i + m)) (j - i)) 1 a (fun m => g (j + m)) (k - j)) / a := by
  rw [eq_div_iff ha, cert_kWalk_rev 0 a g le_rfl, cert_kWalk_suffix a g hij, Nat.sub_self,
    Nat.add_sub_of_le hjk]
  simp only [certResid, gapKeys_zero, Nat.cast_zero]
  ring

/-- The last key at the certificate slope: `p_k = (k + u_i - w) / a` with the suffix started at
`2ε`. -/
theorem cert_gapKeys_eq_ends_certSlope {eps : ℝ} {g : ℕ → ℝ} {k i j : ℕ} (hij : i ≤ j)
    (hjk : j ≤ k) (hne : gapKeys g i ≠ gapKeys g j) (ha : certSlope eps (gapKeys g) i j ≠ 0) :
    gapKeys g k = ((k : ℝ) +
      kWalk 0 (-1) (-certSlope eps (gapKeys g) i j) (fun m => g (i - 1 - m)) i -
      kWalk (2 * eps) 1 (certSlope eps (gapKeys g) i j) (fun m => g (j + m)) (k - j)) /
        certSlope eps (gapKeys g) i j := by
  rw [cert_gapKeys_eq_ends ha hij hjk, cert_middle_end hij hne]

/-! ## Indicator form -/

/-- A three-fold conjunction as a product of Boolean indicators. -/
theorem cert_ite_and_three {R : Type*} [MulZeroOneClass R] (A B C : Prop) {_ : Decidable A}
    {_ : Decidable B} {_ : Decidable C} {_ : Decidable (A ∧ B ∧ C)} :
    (if A ∧ B ∧ C then (1 : R) else 0) =
      (if A then 1 else 0) * (if B then 1 else 0) * (if C then 1 else 0) := by
  by_cases h1 : A
  · by_cases h2 : B
    · by_cases h3 : C
      · rw [if_pos ⟨h1, h2, h3⟩, if_pos h1, if_pos h2, if_pos h3, one_mul, one_mul]
      · rw [if_neg (fun h => h3 h.2.2), if_neg h3, mul_zero]
    · rw [if_neg (fun h => h2 h.2.1), if_neg h2, mul_zero, zero_mul]
  · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul, zero_mul]

open Classical in
/-- The indicator that a walk stays in `J` for `l ≤ n` is the product of the pointwise
indicators. -/
theorem cert_prod_indicator {R : Type*} [CommMonoidWithZero R] (J : Set ℝ) (x : ℕ → ℝ) (n : ℕ) :
    ∏ l ∈ range (n + 1), J.indicator (fun _ => (1 : R)) (x l) =
      if ∀ l ≤ n, x l ∈ J then 1 else 0 := by
  classical
  simp only [Set.indicator_apply]
  rw [Finset.prod_boole]
  have e : (∀ l ∈ range (n + 1), x l ∈ J) ↔ ∀ l ≤ n, x l ∈ J := by
    simp only [mem_range, Nat.lt_succ_iff]
  by_cases h : ∀ l ≤ n, x l ∈ J
  · rw [if_pos (e.2 h), if_pos h]
  · rw [if_neg (mt e.1 h), if_neg h]

/-- **Indicator of a certificate as a product of three block indicators** (`i ≤ j ≤ k`,
`p_i ≠ p_j`, `a = certSlope eps (gapKeys g) i j`, `J = [0, 2ε]`). -/
theorem cert_indicator_certOK_eq_prod {R : Type*} [CommMonoidWithZero R] {eps : ℝ}
    {g : ℕ → ℝ} {k i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (hne : gapKeys g i ≠ gapKeys g j) :
    {g' : ℕ → ℝ | certOK eps (gapKeys g') k i j}.indicator (fun _ => (1 : R)) g =
      (∏ l ∈ range (i + 1), (Set.Icc 0 (2 * eps)).indicator (fun _ => (1 : R))
          (kWalk 0 (-1) (-certSlope eps (gapKeys g) i j) (fun m => g (i - 1 - m)) l)) *
        (∏ l ∈ range (j - i + 1), (Set.Icc 0 (2 * eps)).indicator (fun _ => (1 : R))
          (kWalk 0 1 (certSlope eps (gapKeys g) i j) (fun m => g (i + m)) l)) *
        (∏ l ∈ range (k - j + 1), (Set.Icc 0 (2 * eps)).indicator (fun _ => (1 : R))
          (kWalk (2 * eps) 1 (certSlope eps (gapKeys g) i j) (fun m => g (j + m)) l)) := by
  classical
  rw [cert_prod_indicator, cert_prod_indicator, cert_prod_indicator, Set.indicator_apply]
  simp only [Set.mem_ofPred_eq]
  simp only [certOK_iff_blocks hij hjk hne]
  exact cert_ite_and_three _ _ _

end

end PGM
