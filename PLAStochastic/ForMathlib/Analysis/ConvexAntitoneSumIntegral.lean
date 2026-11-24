import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Analytic lemmas for the overshoot-mean Lipschitz bound

Two self-contained real-analysis facts used by Appendix I (`ROADMAP-I1-44.md`, 1.1(d)(e)):

* **Telescoping.**  A one-sided local bound `f y - f x ≤ (y - x)(q + C (y - x))`
  on every subinterval integrates to the global bound `f c - f a ≤ q (c - a)`.
  This replaces the paper's derivative computation `1/2 ≤ β' ≤ 3/4` by two-sided
  finite differences, which is how the argmax envelope of `M_a` is naturally
  stated.
* **Series–integral comparison for a convex antitone function.**
  `∫₀^∞ g - g(0)/2 ≤ ∑_{n≥1} g(n) ≤ ∫₀^∞ g`.  With `g(x) = Φ(-a√x)` this is the
  bound `1/(2a²) - 1/4 ≤ ∑ Φ(-a√n) ≤ 1/(2a²)`; the Gaussian inputs
  (convexity and the value of the integral) are supplied separately.
-/
noncomputable section
open MeasureTheory Set Filter Finset
open scoped Topology
namespace SwingRepair
namespace Fluctuation

/-! ### Telescoping -/

/-- Local one-sided bounds with quadratic error telescope to a global bound. -/
theorem sub_le_of_local_quadratic_bound {f : ℝ → ℝ} {a c q C : ℝ} (hac : a ≤ c) (hC : 0 ≤ C)
    (h : ∀ x y, a ≤ x → x ≤ y → y ≤ c → f y - f x ≤ (y - x) * (q + C * (y - x))) :
    f c - f a ≤ q * (c - a) := by
  have key : ∀ N : ℕ, 0 < N → f c - f a ≤ q * (c - a) + C * (c - a) ^ 2 / N := by
    intro N hN
    have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    set δ := (c - a) / N with hδ
    have hδ0 : 0 ≤ δ := div_nonneg (by linarith) hNr.le
    have hNδ : (N : ℝ) * δ = c - a := by rw [hδ]; field_simp
    set x : ℕ → ℝ := fun i => a + i * δ with hx
    have hx0 : x 0 = a := by simp [hx]
    have hxN : x N = c := by simp only [hx]; rw [hNδ]; ring
    have htel : f c - f a = ∑ i ∈ range N, (f (x (i + 1)) - f (x i)) := by
      rw [Finset.sum_range_sub (fun i => f (x i)), hxN, hx0]
    have hstep : ∀ i ∈ range N, f (x (i + 1)) - f (x i) ≤ δ * (q + C * δ) := by
      intro i hi
      have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
      have h1 : a ≤ x i := by
        simp only [hx]
        nlinarith [Nat.cast_nonneg (α := ℝ) i]
      have h2 : x i ≤ x (i + 1) := by
        simp only [hx]; push_cast; nlinarith
      have h3 : x (i + 1) ≤ c := by
        simp only [hx]; push_cast
        have := mul_le_mul_of_nonneg_right hi' hδ0
        linarith
      have hd : x (i + 1) - x i = δ := by simp only [hx]; push_cast; ring
      have := h (x i) (x (i + 1)) h1 h2 h3
      rwa [hd] at this
    calc f c - f a = ∑ i ∈ range N, (f (x (i + 1)) - f (x i)) := htel
      _ ≤ ∑ _i ∈ range N, δ * (q + C * δ) := Finset.sum_le_sum hstep
      _ = N * (δ * (q + C * δ)) := by simp
      _ = q * (c - a) + C * (c - a) ^ 2 / N := by
          rw [hδ]; field_simp
  by_contra hlt
  push Not at hlt
  set ε := f c - f a - q * (c - a) with hε
  have hε0 : 0 < ε := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (C * (c - a) ^ 2 / ε)
  have hnn : 0 ≤ C * (c - a) ^ 2 / ε := div_nonneg (mul_nonneg hC (sq_nonneg _)) hε0.le
  have hNpos : 0 < N := by exact_mod_cast lt_of_le_of_lt hnn hN
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hlt' : C * (c - a) ^ 2 / N < ε := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hε0] at hN
    linarith
  have := key N hNpos
  linarith

/-- The two-sided version: a local lower bound with quadratic error gives a
global lower bound. -/
theorem le_sub_of_local_quadratic_bound {f : ℝ → ℝ} {a c q C : ℝ} (hac : a ≤ c) (hC : 0 ≤ C)
    (h : ∀ x y, a ≤ x → x ≤ y → y ≤ c → (y - x) * (q - C * (y - x)) ≤ f y - f x) :
    q * (c - a) ≤ f c - f a := by
  have := sub_le_of_local_quadratic_bound (f := fun t => -f t) (q := -q) hac hC
    (fun x y hx hxy hy => by
      have := h x y hx hxy hy
      nlinarith)
  linarith

/-! ### Trapezoid bound for convex functions -/

/-- On a unit interval a convex function lies below its chord, so its integral is
at most the trapezoid value. -/
theorem integral_le_trapezoid_of_convexOn {g : ℝ → ℝ} {x : ℝ}
    (hg : ConvexOn ℝ (Icc x (x + 1)) g) (hint : IntervalIntegrable g volume x (x + 1)) :
    ∫ t in x..x + 1, g t ≤ (g x + g (x + 1)) / 2 := by
  have hchord : ∀ t ∈ Icc x (x + 1), g t ≤ (x + 1 - t) * g x + (t - x) * g (x + 1) := by
    intro t ht
    have h := hg.2 (show x ∈ Icc x (x + 1) from ⟨le_rfl, by linarith⟩)
      (show x + 1 ∈ Icc x (x + 1) from ⟨by linarith, le_rfl⟩)
      (show 0 ≤ x + 1 - t by linarith [ht.2]) (show 0 ≤ t - x by linarith [ht.1]) (by ring)
    simp only [smul_eq_mul] at h
    have : (x + 1 - t) * x + (t - x) * (x + 1) = t := by ring
    rwa [this] at h
  have hchord_int : IntervalIntegrable (fun t => (x + 1 - t) * g x + (t - x) * g (x + 1))
      volume x (x + 1) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h1 : ∫ t in x..x + 1, g t ≤ ∫ t in x..x + 1, ((x + 1 - t) * g x + (t - x) * g (x + 1)) :=
    intervalIntegral.integral_mono_on (by linarith) hint hchord_int hchord
  have h2 : ∫ t in x..x + 1, ((x + 1 - t) * g x + (t - x) * g (x + 1)) =
      (g x + g (x + 1)) / 2 := by
    have e : (fun t : ℝ => (x + 1 - t) * g x + (t - x) * g (x + 1)) =
        fun t : ℝ => ((x + 1) * g x - x * g (x + 1)) + (g (x + 1) - g x) * t := by
      funext t; ring
    have hc1 : IntervalIntegrable (fun _ : ℝ => (x + 1) * g x - x * g (x + 1)) volume x (x + 1) :=
      continuous_const.intervalIntegrable _ _
    have hc2 : IntervalIntegrable (fun t : ℝ => (g (x + 1) - g x) * t) volume x (x + 1) :=
      (continuous_const.mul continuous_id).intervalIntegrable _ _
    rw [e, intervalIntegral.integral_add hc1 hc2,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
    simp only [smul_eq_mul]
    ring
  linarith

/-! ### Series–integral comparison -/

/-- `∑_{i<N} g(i) ≤ g(0) + ∑_{i<N} g(i+1)` for nonnegative `g`. -/
theorem sum_range_le_head_add_sum_range_succ {g : ℕ → ℝ} (hnn : ∀ n, 0 ≤ g n) (N : ℕ) :
    ∑ i ∈ range N, g i ≤ g 0 + ∑ i ∈ range N, g (i + 1) := by
  cases N with
  | zero => simp [hnn 0]
  | succ M =>
    rw [Finset.sum_range_succ' (fun i => g i), Finset.sum_range_succ (fun i => g (i + 1))]
    have := hnn (M + 1)
    linarith

/-- **Lower bound.**  For a convex, antitone, nonnegative, integrable `g` on
`[0,∞)`, `∫₀^∞ g ≤ ∑_{n≥1} g(n) + g(0)/2`. -/
theorem integral_Ioi_le_tsum_add_half {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) g)
    (hanti : AntitoneOn g (Ici 0)) (hnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ g t)
    (hint : IntegrableOn g (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), g t ≤ (∑' n : ℕ, g (n + 1 : ℕ)) + g 0 / 2 := by
  have hnn' : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := fun t ht => hnn t (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht)))
  have hsum : Summable fun n : ℕ => g n :=
    hanti.summable_of_integrableOn_Ioi_zero hint hnn'
  have hsum1 : Summable fun n : ℕ => g (n + 1 : ℕ) := (summable_nat_add_iff 1).mpr hsum
  have hgN : ∀ N : ℕ, 0 ≤ g N := fun N => hnn _ (Set.mem_Ici.mpr (Nat.cast_nonneg N))
  -- partial integrals are bounded by the tail sums
  have hpartial : ∀ N : ℕ, ∫ t in (0 : ℝ)..N, g t ≤ (∑' n : ℕ, g (n + 1 : ℕ)) + g 0 / 2 := by
    intro N
    have hII : ∀ k < N, IntervalIntegrable g volume ((k : ℕ) : ℝ) ((k + 1 : ℕ) : ℝ) := by
      intro k _
      rw [intervalIntegrable_iff, uIoc_of_le (by push_cast; linarith)]
      refine hint.mono_set fun t ht => ?_
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact lt_of_le_of_lt this ht.1
    have hsplit : ∫ t in (0 : ℝ)..N, g t = ∑ k ∈ range N, ∫ t in ((k : ℕ) : ℝ)..((k + 1 : ℕ) : ℝ), g t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => (k : ℝ)) hII]
      simp
    have htrap : ∀ k ∈ range N,
        ∫ t in ((k : ℕ) : ℝ)..((k + 1 : ℕ) : ℝ), g t ≤ (g k + g ((k : ℝ) + 1)) / 2 := by
      intro k hk
      have hconvk : ConvexOn ℝ (Icc (k : ℝ) ((k : ℝ) + 1)) g :=
        hconv.subset (fun t ht => le_trans (Nat.cast_nonneg k) ht.1) (convex_Icc _ _)
      have hIk : IntervalIntegrable g volume (k : ℝ) ((k : ℝ) + 1) := by
        have := hII k (Finset.mem_range.mp hk)
        push_cast at this
        exact this
      have := integral_le_trapezoid_of_convexOn hconvk hIk
      push_cast
      exact this
    have hcast : ∀ k : ℕ, g ((k : ℝ) + 1) = g ((k + 1 : ℕ) : ℝ) := fun k => by push_cast; rfl
    calc ∫ t in (0 : ℝ)..N, g t
        = ∑ k ∈ range N, ∫ t in ((k : ℕ) : ℝ)..((k + 1 : ℕ) : ℝ), g t := hsplit
      _ ≤ ∑ k ∈ range N, (g k + g ((k : ℝ) + 1)) / 2 := Finset.sum_le_sum htrap
      _ = ((∑ k ∈ range N, g k) + ∑ k ∈ range N, g ((k + 1 : ℕ) : ℝ)) / 2 := by
          simp_rw [hcast]
          rw [← Finset.sum_add_distrib, Finset.sum_div]
      _ ≤ (g 0 + 2 * ∑ k ∈ range N, g ((k + 1 : ℕ) : ℝ)) / 2 := by
          have := sum_range_le_head_add_sum_range_succ (g := fun n : ℕ => g n) hgN N
          simp only [Nat.cast_zero] at this
          linarith
      _ = g 0 / 2 + ∑ k ∈ range N, g ((k + 1 : ℕ) : ℝ) := by ring
      _ ≤ g 0 / 2 + ∑' n : ℕ, g (n + 1 : ℕ) := by
          have := hsum1.sum_le_tsum (range N) (fun n _ => hgN (n + 1))
          linarith
      _ = (∑' n : ℕ, g (n + 1 : ℕ)) + g 0 / 2 := by ring
  have hlim : Tendsto (fun N : ℕ => ∫ t in (0 : ℝ)..N, g t) atTop (𝓝 (∫ t in Ioi (0 : ℝ), g t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop
  exact le_of_tendsto' hlim hpartial

/-- **Two-sided bound.**  `∫₀^∞ g - g(0)/2 ≤ ∑_{n≥1} g(n) ≤ ∫₀^∞ g`. -/
theorem tsum_add_one_bounds_of_convex_antitone {g : ℝ → ℝ} (hconv : ConvexOn ℝ (Ici 0) g)
    (hanti : AntitoneOn g (Ici 0)) (hnn : ∀ t ∈ Ici (0 : ℝ), 0 ≤ g t)
    (hint : IntegrableOn g (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), g t) - g 0 / 2 ≤ ∑' n : ℕ, g (n + 1 : ℕ) ∧
      ∑' n : ℕ, g (n + 1 : ℕ) ≤ ∫ t in Ioi (0 : ℝ), g t := by
  refine ⟨by linarith [integral_Ioi_le_tsum_add_half hconv hanti hnn hint], ?_⟩
  exact hanti.tsum_add_one_le_integral hint fun t ht => hnn t (Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp ht)))

end Fluctuation
end SwingRepair
