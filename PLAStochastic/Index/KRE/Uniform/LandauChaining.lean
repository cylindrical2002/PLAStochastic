import PLAStochastic.Index.Algorithm.SlopeTransfer
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Landau chaining bound

Deterministic core of `lem:curv`(a) ("One segment", "Chaining") in
`research/2026-09-24-re-curvature-uniform/tex/main.tex` and of `lem:landau` in
`research/2026-09-24-height-precision-ceiling/tex/main.tex`.

* `landau_chain`: let `G'` be a `Λ`-Lipschitz derivative of `G` on `[0, 1]`, and let the
  keys `x 0 < ⋯ < x (K - 1)` in `[0, 1]` have mesh `≤ h` and be split into `M` consecutive
  windows on which `G (x j)` is within `θ i` of a line. Then `G'` varies by at most
  `∑ i, 4 √((θ i + Λ h²) Λ) + M Λ h` over `[x 0, x (K - 1)]`;
* `sum_rpow_quarter_le`: `∑ i < M, τ i ^ (1/4) ≤ M ^ (3/4) (∑ i < M, τ i) ^ (1/4)`.

Each window interval has oscillation `≤ 4 √(ϑ Λ)` with `ϑ = θ i + Λ h²` (`chord_bound`,
`landau_osc`, `window_osc`); prefixing the gap to the previous key costs `Λ h`, and the
extended windows chain (`oscLe_chain`).
-/

noncomputable section

namespace PGM
open Finset

/-- `f` varies by at most `A` on `[u, v]`. -/
private def OscLe (f : ℝ → ℝ) (u v A : ℝ) : Prop :=
  ∀ s ∈ Set.Icc u v, ∀ t ∈ Set.Icc u v, |f t - f s| ≤ A

/-- Oscillation bounds add over two abutting intervals. -/
private theorem OscLe.union {f : ℝ → ℝ} {u m v A B : ℝ} (h1 : OscLe f u m A)
    (h2 : OscLe f m v B) (hA : 0 ≤ A) (hB : 0 ≤ B) : OscLe f u v (A + B) := by
  intro s hs t ht
  rcases le_total s m with hsm | hms <;> rcases le_total t m with htm | hmt
  · linarith [h1 s ⟨hs.1, hsm⟩ t ⟨ht.1, htm⟩]
  · linarith [abs_sub_le (f t) (f m) (f s), h2 m ⟨le_rfl, hmt.trans ht.2⟩ t ⟨hmt, ht.2⟩,
      h1 s ⟨hs.1, hsm⟩ m ⟨hs.1.trans hsm, le_rfl⟩]
  · linarith [abs_sub_le (f t) (f m) (f s), h1 m ⟨ht.1.trans htm, le_rfl⟩ t ⟨ht.1, htm⟩,
      h2 s ⟨hms, hs.2⟩ m ⟨le_rfl, hms.trans hs.2⟩]
  · linarith [h2 s ⟨hms, hs.2⟩ t ⟨hmt, ht.2⟩]

/-- Oscillation bounds add along a chain of abutting intervals `[p i, p (i + 1)]`. -/
private theorem oscLe_chain {f : ℝ → ℝ} {p e : ℕ → ℝ} :
    ∀ M : ℕ, (∀ i < M, 0 ≤ e i) → (∀ i < M, OscLe f (p i) (p (i + 1)) (e i)) →
      OscLe f (p 0) (p M) (∑ i ∈ range M, e i)
  | 0, _, _ => by
    intro s hs t ht
    have hst : s = t := le_antisymm (hs.2.trans ht.1) (ht.2.trans hs.1)
    simp [hst]
  | M + 1, he, hosc => by
    rw [sum_range_succ]
    exact (oscLe_chain M (fun i hi => he i (by omega)) (fun i hi => hosc i (by omega))).union
      (hosc M (by omega)) (sum_nonneg fun i hi => he i (by simp at hi; omega)) (he M (by omega))

/-- A `Λ`-Lipschitz function varies by at most `Λ (v - u)` on `[u, v] ⊆ [0, 1]`. -/
private theorem oscLe_of_lip {G' : ℝ → ℝ} {Λ u v : ℝ}
    (hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |G' y - G' z| ≤ Λ * |y - z|)
    (hΛ : 0 ≤ Λ) (hu : 0 ≤ u) (hv : v ≤ 1) : OscLe G' u v (Λ * (v - u)) := by
  intro s hs t ht
  refine (hlip t ⟨hu.trans ht.1, ht.2.trans hv⟩ s ⟨hu.trans hs.1, hs.2.trans hv⟩).trans ?_
  exact mul_le_mul_of_nonneg_left
    (abs_sub_le_iff.mpr ⟨by linarith [ht.2, hs.1], by linarith [hs.2, ht.1]⟩) hΛ

/-- **Chord bound.** Between two points where `G` is within `θ` of a line, `G` stays within
`θ + Λ / 2 (q - p)²` of it. -/
private theorem chord_bound {G G' : ℝ → ℝ} {Λ θ α β p q y : ℝ}
    (hderiv : ∀ y ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' y) (Set.Icc 0 1) y)
    (hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |G' y - G' z| ≤ Λ * |y - z|)
    (hΛ : 0 ≤ Λ) (hp0 : 0 ≤ p) (hq1 : q ≤ 1) (hpq : p < q)
    (hp : |G p - (α * p + β)| ≤ θ) (hq : |G q - (α * q + β)| ≤ θ) (hy : y ∈ Set.Icc p q) :
    |G y - (α * y + β)| ≤ θ + Λ / 2 * (q - p) ^ 2 := by
  have hI : (Set.Icc (0 : ℝ) 1).OrdConnected := Set.ordConnected_Icc
  have hy01 : y ∈ Set.Icc (0 : ℝ) 1 := ⟨hp0.trans hy.1, hy.2.trans hq1⟩
  have h1 := abs_le.mp <| abs_taylor_remainder_le hI hderiv hlip hy01 ⟨hp0, hpq.le.trans hq1⟩
  have h2 := abs_le.mp <| abs_taylor_remainder_le hI hderiv hlip hy01 ⟨hp0.trans hpq.le, hq1⟩
  have hψp := abs_le.mp hp
  have hψq := abs_le.mp hq
  have ha : 0 ≤ q - y := by linarith [hy.2]
  have hb : 0 ≤ y - p := by linarith [hy.1]
  have hqp : 0 < q - p := sub_pos.mpr hpq
  have hprod : Λ / 2 * (q - p) * ((q - y) * (y - p)) ≤ Λ / 2 * (q - p) * (q - p) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  -- `(q - p) ψ(y) = (q - y) ψ(p) + (y - p) ψ(q) - (q - y) T₁ - (y - p) T₂` with Taylor
  -- remainders `T₁, T₂` at `y`
  refine abs_le.mpr ⟨le_of_mul_le_mul_left ?_ hqp, le_of_mul_le_mul_left ?_ hqp⟩
  · nlinarith [mul_le_mul_of_nonneg_left hψp.1 ha, mul_le_mul_of_nonneg_left hψq.1 hb,
      mul_le_mul_of_nonneg_left h1.2 ha, mul_le_mul_of_nonneg_left h2.2 hb]
  · nlinarith [mul_le_mul_of_nonneg_left hψp.2 ha, mul_le_mul_of_nonneg_left hψq.2 hb,
      mul_le_mul_of_nonneg_left h1.1 ha, mul_le_mul_of_nonneg_left h2.1 hb]

/-- **Landau inequality.** If `G` is within `ϑ > 0` of a line on `[u, v] ⊆ [0, 1]` and `G'`
is `Λ`-Lipschitz with `Λ > 0`, then `G'` varies by at most `4 √(ϑ Λ)` on `[u, v]`. -/
private theorem landau_osc {G G' : ℝ → ℝ} {Λ ϑ α β u v : ℝ}
    (hderiv : ∀ y ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' y) (Set.Icc 0 1) y)
    (hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |G' y - G' z| ≤ Λ * |y - z|)
    (hΛ : 0 < Λ) (hϑ : 0 < ϑ) (hu : 0 ≤ u) (hv : v ≤ 1)
    (hψ : ∀ y ∈ Set.Icc u v, |G y - (α * y + β)| ≤ ϑ) :
    OscLe G' u v (4 * Real.sqrt (ϑ * Λ)) := by
  rw [Real.sqrt_mul hϑ.le]
  set σ := Real.sqrt ϑ with hσ
  set l := Real.sqrt Λ with hl
  have hσ0 : 0 < σ := Real.sqrt_pos.mpr hϑ
  have hl0 : 0 < l := Real.sqrt_pos.mpr hΛ
  have hσσ : σ ^ 2 = ϑ := Real.sq_sqrt hϑ.le
  have hll : l ^ 2 = Λ := Real.sq_sqrt hΛ.le
  set r := 2 * σ / l with hr
  have hr0 : 0 < r := by positivity
  have hlr : l * r = 2 * σ := by rw [hr]; field_simp
  by_cases hlen : v - u < 2 * r
  · -- short interval: Lipschitz bound
    intro s hs t ht
    calc |G' t - G' s| ≤ Λ * (v - u) := oscLe_of_lip hlip hΛ.le hu hv s hs t ht
      _ ≤ Λ * (2 * r) := mul_le_mul_of_nonneg_left hlen.le hΛ.le
      _ = 4 * (σ * l) := by rw [← hll]; linear_combination (2 * l) * hlr
  · -- long interval: `|G' s - α| ≤ 2 √(ϑ Λ)` from a step of length `r`
    rw [not_lt] at hlen
    have hbound : ∀ s ∈ Set.Icc u v, |G' s - α| ≤ 2 * (σ * l) := by
      intro s hs
      obtain ⟨y, hy, hyr⟩ : ∃ y ∈ Set.Icc u v, |y - s| = r := by
        by_cases h : s + r ≤ v
        · exact ⟨s + r, ⟨by linarith [hs.1], h⟩, by rw [add_sub_cancel_left, abs_of_pos hr0]⟩
        · exact ⟨s - r, ⟨by linarith, by linarith [hs.2]⟩,
            by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hr0]⟩
      have hys : (y - s) ^ 2 = r ^ 2 := by rw [← sq_abs, hyr]
      have hT := abs_taylor_remainder_le Set.ordConnected_Icc hderiv hlip
        ⟨hu.trans hs.1, hs.2.trans hv⟩ ⟨hu.trans hy.1, hy.2.trans hv⟩
      rw [hys] at hT
      have hmain : |G' s - α| * r ≤ 2 * (σ * l) * r := by
        calc |G' s - α| * r = |(G y - (α * y + β)) - (G s - (α * s + β)) -
              (G y - G s - G' s * (y - s))| := by
                rw [← hyr, ← abs_mul]; congr 1; ring
          _ ≤ ϑ + ϑ + Λ / 2 * r ^ 2 := by
                linarith [abs_sub (G y - (α * y + β) - (G s - (α * s + β)))
                  (G y - G s - G' s * (y - s)),
                  abs_sub (G y - (α * y + β)) (G s - (α * s + β)), hψ y hy, hψ s hs]
          _ = 2 * (σ * l) * r := by
                rw [← hσσ, ← hll]; linear_combination ((l * r + 2 * σ) / 2 - 2 * σ) * hlr
      exact le_of_mul_le_mul_right hmain hr0
    intro s hs t ht
    linarith [abs_sub_le (G' t) α (G' s), abs_sub_comm (G' s) α, hbound s hs, hbound t ht]

/-- A point of `[x m, x n]` is `x m` or lies between consecutive keys `x j`, `x (j + 1)`
with `m ≤ j < n`. -/
private theorem bracket (x : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) {y : ℝ}
    (hy : y ∈ Set.Icc (x m) (x n)) :
    y = x m ∨ ∃ j, m ≤ j ∧ j < n ∧ x j ≤ y ∧ y ≤ x (j + 1) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Or.inl (le_antisymm hy.2 hy.1)
  | succ n hmn ih =>
    by_cases hyn : y ≤ x n
    · rcases ih ⟨hy.1, hyn⟩ with h | ⟨j, h1, h2, h3, h4⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, h1, by omega, h3, h4⟩
    · exact Or.inr ⟨n, hmn, by omega, (not_le.mp hyn).le, hy.2⟩

/-- **One window.** If `G (x j)` is within `θ` of a line for the keys `m ≤ j ≤ n`, then `G'`
varies by at most `4 √((θ + Λ h²) Λ)` on `[x m, x n]`. -/
private theorem window_osc {G G' : ℝ → ℝ} {Λ h θ α β : ℝ} {x : ℕ → ℝ} {K m n : ℕ}
    (hderiv : ∀ y ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' y) (Set.Icc 0 1) y)
    (hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |G' y - G' z| ≤ Λ * |y - z|)
    (hΛ : 0 ≤ Λ) (hmono : ∀ j, j + 1 < K → x j < x (j + 1))
    (hmem : ∀ j < K, x j ∈ Set.Icc (0 : ℝ) 1)
    (hmesh : ∀ j, j + 1 < K → x (j + 1) - x j ≤ h) (hmn : m ≤ n) (hnK : n < K)
    (hfit : ∀ j, m ≤ j → j ≤ n → |G (x j) - (α * x j + β)| ≤ θ) (hθ : 0 ≤ θ) :
    OscLe G' (x m) (x n) (4 * Real.sqrt ((θ + Λ * h ^ 2) * Λ)) := by
  have hm01 := hmem m (by omega)
  have hn01 := hmem n hnK
  rcases hΛ.lt_or_eq with hΛ0 | hΛ0
  swap
  · intro s hs t ht
    calc |G' t - G' s| ≤ Λ * (x n - x m) := oscLe_of_lip hlip hΛ hm01.1 hn01.2 s hs t ht
      _ = 0 := by rw [← hΛ0, zero_mul]
      _ ≤ _ := by positivity
  rcases hmn.lt_or_eq with hlt | rfl
  swap
  · intro s hs t ht
    rw [le_antisymm (hs.2.trans ht.1) (ht.2.trans hs.1), sub_self, abs_zero]
    positivity
  have hh : 0 < h := by linarith [hmono m (by omega), hmesh m (by omega)]
  refine landau_osc (α := α) (β := β) hderiv hlip hΛ0 (by positivity) hm01.1 hn01.2 fun y hy => ?_
  rcases bracket x hlt.le hy with rfl | ⟨j, hmj, hjn, hxy, hyx⟩
  · exact (hfit m le_rfl hlt.le).trans (by nlinarith)
  · have hc := chord_bound hderiv hlip hΛ (hmem j (by omega)).1 (hmem (j + 1) (by omega)).2
      (hmono j (by omega)) (hfit j hmj (by omega)) (hfit (j + 1) (by omega) (by omega))
      ⟨hxy, hyx⟩
    have hd : (x (j + 1) - x j) ^ 2 ≤ h ^ 2 :=
      pow_le_pow_left₀ (by linarith [hmono j (by omega)]) (hmesh j (by omega)) 2
    nlinarith [mul_le_mul_of_nonneg_left hd hΛ, mul_nonneg hΛ (sq_nonneg h)]

/-- **Landau chaining bound.** Let `G'` be a `Λ`-Lipschitz derivative of `G` on `[0, 1]`, and
let the keys `x 0 < ⋯ < x (K - 1)` in `[0, 1]`, of mesh `≤ h`, be split into the `M` windows
`c i ≤ j < c (i + 1)`, on each of which `G (x j)` is within `θ i` of a line. Then for
`x 0 ≤ a ≤ b ≤ x (K - 1)`, `|G' b - G' a| ≤ ∑ i, 4 √((θ i + Λ h²) Λ) + M Λ h`. -/
theorem landau_chain {G G' : ℝ → ℝ} {Λ h : ℝ} {x : ℕ → ℝ} {K M : ℕ} {c : ℕ → ℕ}
    {θ : ℕ → ℝ} {a b : ℝ}
    (hderiv : ∀ y ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt G (G' y) (Set.Icc 0 1) y)
    (hlip : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |G' y - G' z| ≤ Λ * |y - z|)
    (hh : 0 ≤ h)
    (hmono : ∀ j, j + 1 < K → x j < x (j + 1))
    (hmem : ∀ j < K, x j ∈ Set.Icc (0 : ℝ) 1)
    (hmesh : ∀ j, j + 1 < K → x (j + 1) - x j ≤ h)
    (hc0 : c 0 = 0) (hcM : c M = K) (hcstep : ∀ i < M, c i < c (i + 1))
    (hfit : ∀ i < M, ∃ α β : ℝ, ∀ j, c i ≤ j → j < c (i + 1) →
      |G (x j) - (α * x j + β)| ≤ θ i)
    (hθ : ∀ i < M, 0 ≤ θ i)
    (ha : x 0 ≤ a) (hab : a ≤ b) (hb : b ≤ x (K - 1)) :
    |G' b - G' a| ≤ ∑ i ∈ range M, 4 * Real.sqrt ((θ i + Λ * h ^ 2) * Λ) + M * Λ * h := by
  have hΛ : 0 ≤ Λ := by
    have h01 := hlip 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    norm_num at h01
    exact (abs_nonneg _).trans h01
  have hcmono : ∀ i j, i ≤ j → j ≤ M → c i ≤ c j := by
    intro i j hij hjM
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hcstep j (by omega)).le
  -- extended window `i`: the gap from the last key of window `i - 1`, then window `i`
  have hext : ∀ i < M, OscLe G' (x (c i - 1)) (x (c (i + 1) - 1))
      (4 * Real.sqrt ((θ i + Λ * h ^ 2) * Λ) + Λ * h) := by
    intro i hi
    have h1 := hcstep i hi
    have h2 : c (i + 1) ≤ K := hcM ▸ hcmono (i + 1) M hi le_rfl
    obtain ⟨α, β, hαβ⟩ := hfit i hi
    have hw := window_osc (m := c i) (n := c (i + 1) - 1) hderiv hlip hΛ hmono hmem hmesh
      (by omega) (by omega) (fun j hj1 hj2 => hαβ j hj1 (by omega)) (hθ i hi)
    have hd : x (c i) - x (c i - 1) ≤ h := by
      rcases Nat.eq_zero_or_pos (c i) with h0 | h0
      · rw [h0, Nat.zero_sub, sub_self]; exact hh
      · have := hmesh (c i - 1) (by omega)
        rwa [Nat.sub_add_cancel h0] at this
    have hgap : OscLe G' (x (c i - 1)) (x (c i)) (Λ * h) := fun s hs t ht =>
      (oscLe_of_lip hlip hΛ (hmem (c i - 1) (by omega)).1 (hmem (c i) (by omega)).2
        s hs t ht).trans (mul_le_mul_of_nonneg_left hd hΛ)
    have hu := hgap.union hw (mul_nonneg hΛ hh) (by positivity)
    rwa [add_comm (Λ * h)] at hu
  have hchain := oscLe_chain (p := fun i => x (c i - 1)) M
    (fun i _ => add_nonneg (by positivity) (mul_nonneg hΛ hh)) hext
  simp only [hc0, hcM, Nat.zero_sub] at hchain
  have hfin := hchain a ⟨ha, hab.trans hb⟩ b ⟨ha.trans hab, hb⟩
  rw [sum_add_distrib, sum_const, card_range, nsmul_eq_mul] at hfin
  rw [mul_assoc]
  exact hfin

/-- **Hölder for quarter powers.** For `τ i ≥ 0`,
`∑ i < M, τ i ^ (1/4) ≤ M ^ (3/4) (∑ i < M, τ i) ^ (1/4)`. -/
theorem sum_rpow_quarter_le (M : ℕ) (τ : ℕ → ℝ) (hτ : ∀ i < M, 0 ≤ τ i) :
    ∑ i ∈ range M, τ i ^ (1 / 4 : ℝ) ≤
      (M : ℝ) ^ (3 / 4 : ℝ) * (∑ i ∈ range M, τ i) ^ (1 / 4 : ℝ) := by
  have hq : (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  have hf : ∀ i ∈ range M, 0 ≤ τ i ^ (1 / 4 : ℝ) := fun i hi =>
    Real.rpow_nonneg (hτ i (mem_range.mp hi)) _
  have hf4 : ∀ i ∈ range M, (τ i ^ (1 / 4 : ℝ)) ^ 4 = τ i := fun i hi => by
    rw [hq]; exact Real.rpow_inv_natCast_pow (hτ i (mem_range.mp hi)) (by norm_num)
  have hJ : (∑ i ∈ range M, τ i ^ (1 / 4 : ℝ)) ^ 4 ≤ (M : ℝ) ^ 3 * ∑ i ∈ range M, τ i := by
    have := pow_sum_le_card_mul_sum_pow hf 3
    rwa [card_range, sum_congr rfl hf4] at this
  have hS : 0 ≤ ∑ i ∈ range M, τ i ^ (1 / 4 : ℝ) := sum_nonneg hf
  have hT : 0 ≤ ∑ i ∈ range M, τ i := sum_nonneg fun i hi => hτ i (mem_range.mp hi)
  have hroot : ∀ z : ℝ, 0 ≤ z → (z ^ 4) ^ (1 / 4 : ℝ) = z := fun z hz => by
    rw [hq]; exact Real.pow_rpow_inv_natCast hz (by norm_num)
  calc ∑ i ∈ range M, τ i ^ (1 / 4 : ℝ)
      = ((∑ i ∈ range M, τ i ^ (1 / 4 : ℝ)) ^ 4) ^ (1 / 4 : ℝ) := by
        rw [hroot _ hS]
    _ ≤ ((M : ℝ) ^ 3 * ∑ i ∈ range M, τ i) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hJ (by norm_num)
    _ = ((M : ℝ) ^ 3) ^ (1 / 4 : ℝ) * (∑ i ∈ range M, τ i) ^ (1 / 4 : ℝ) :=
        Real.mul_rpow (by positivity) hT
    _ = (M : ℝ) ^ (3 / 4 : ℝ) * (∑ i ∈ range M, τ i) ^ (1 / 4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg M)]
        norm_num

end PGM
