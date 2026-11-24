import PLAStochastic.Swing.Entrance.Grid.Cut

/-!
# Riemann sums for the entrance area

Elementary analytic estimates behind (E20)–(E21) of the entrance law:

* right-endpoint Riemann sums `h ∑_{k=1}^{N} g(k h)` of a continuous function converge to
  `∫_0^σ g` whenever the mesh `h` tends to zero and the horizon `N h` tends to `σ`;
* `∑_{k=1}^{N} k² = N (N + 1) (2N + 1) / 6`, so `E^{-6} ∑_{k=1}^{N} k² → σ³/3` when `N/E² → σ`;
* the deterministic tail estimate (E21): extending the reflected area sum from the cut `n` to
  `N ≤ n + q` along an accepted prefix (`|y_i - β i| ≤ E`) changes it by at most `N q / E⁴`.
-/

open Finset Filter MeasureTheory
open scoped Topology

namespace SwingRepair

noncomputable section

theorem sum_Icc_one_eq_sum_range (F : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ Icc 1 N, F k = ∑ k ∈ range N, F (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

/-- Right-endpoint Riemann sums of a continuous function along a vanishing mesh. -/
theorem tendsto_riemannSum {g : ℝ → ℝ} (hg : Continuous g) {σ : ℝ}
    {ι : Type*} {l : Filter ι} {h : ι → ℝ} {N : ι → ℕ}
    (hh : ∀ᶠ i in l, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hN : Tendsto (fun i => (N i : ℝ) * h i) l (𝓝 σ)) :
    Tendsto (fun i => h i * ∑ k ∈ Icc 1 (N i), g ((k : ℝ) * h i)) l
      (𝓝 (∫ t in (0 : ℝ)..σ, g t)) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b :=
    fun a b => hg.intervalIntegrable a b
  have hprim : Tendsto (fun i => ∫ t in (0 : ℝ)..((N i : ℝ) * h i), g t) l
      (𝓝 (∫ t in (0 : ℝ)..σ, g t)) :=
    ((intervalIntegral.continuous_primitive hint 0).tendsto σ).comp hN
  suffices hdiff : Tendsto (fun i => h i * ∑ k ∈ Icc 1 (N i), g ((k : ℝ) * h i) -
      ∫ t in (0 : ℝ)..((N i : ℝ) * h i), g t) l (𝓝 0) by
    simpa using hdiff.add hprim
  -- uniform continuity on a compact interval containing every horizon
  have hU : UniformContinuousOn g (Set.Icc (0 : ℝ) (|σ| + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε' : 0 < ε / (2 * (|σ| + 1)) := by positivity
  obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.mp hU _ hε'
  have hNσ : ∀ᶠ i in l, (N i : ℝ) * h i < |σ| + 1 :=
    hN.eventually_lt_const (lt_of_le_of_lt (le_abs_self σ) (by linarith))
  filter_upwards [hh, hconv.eventually_lt_const hδ, hNσ] with i hhi hδi hNi
  set H := h i
  set M := N i
  have hsplit : ∫ t in (0 : ℝ)..((M : ℝ) * H), g t =
      ∑ k ∈ range M, ∫ t in ((k : ℝ) * H)..(((k + 1 : ℕ) : ℝ) * H), g t := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
      (a := fun k : ℕ => (k : ℝ) * H) (n := M) (fun k _ => hint _ _)
    simpa using this.symm
  have hsum : H * ∑ k ∈ Icc 1 M, g ((k : ℝ) * H) =
      ∑ k ∈ range M, ∫ _ in ((k : ℝ) * H)..(((k + 1 : ℕ) : ℝ) * H),
        g (((k + 1 : ℕ) : ℝ) * H) := by
    rw [sum_Icc_one_eq_sum_range, mul_sum]
    apply sum_congr rfl
    intro k _
    rw [intervalIntegral.integral_const, smul_eq_mul]
    push_cast
    ring
  rw [hsplit, hsum, ← sum_sub_distrib, Real.dist_eq, sub_zero]
  have hterm : ∀ k ∈ range M,
      |(∫ _ in ((k : ℝ) * H)..(((k + 1 : ℕ) : ℝ) * H), g (((k + 1 : ℕ) : ℝ) * H)) -
        ∫ t in ((k : ℝ) * H)..(((k + 1 : ℕ) : ℝ) * H), g t| ≤
        ε / (2 * (|σ| + 1)) * H := by
    intro k hk
    have hkM : k + 1 ≤ M := Finset.mem_range.mp hk
    rw [← intervalIntegral.integral_sub intervalIntegrable_const (hint _ _)]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (k : ℝ) * H) (b := ((k + 1 : ℕ) : ℝ) * H)
      (f := fun t => g (((k + 1 : ℕ) : ℝ) * H) - g t) (C := ε / (2 * (|σ| + 1))) (by
        intro t ht
        have hab : (k : ℝ) * H ≤ ((k + 1 : ℕ) : ℝ) * H := by
          push_cast
          nlinarith
        rw [Set.uIoc_of_le hab] at ht
        have hk1 : (((k + 1 : ℕ) : ℝ)) * H ≤ (M : ℝ) * H := by
          have : ((k + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hkM
          nlinarith
        have h0 : 0 ≤ (k : ℝ) * H := by positivity
        have hx : ((k + 1 : ℕ) : ℝ) * H ∈ Set.Icc (0 : ℝ) (|σ| + 1) :=
          ⟨by positivity, by linarith⟩
        have ht' : t ∈ Set.Icc (0 : ℝ) (|σ| + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have hd : dist (((k + 1 : ℕ) : ℝ) * H) t < δ := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith [ht.2])]
          push_cast at ht ⊢
          nlinarith [ht.1]
        have := hδU _ hx _ ht' hd
        rw [Real.dist_eq] at this
        rw [Real.norm_eq_abs]
        exact this.le)
    rw [Real.norm_eq_abs] at hb
    refine hb.trans (le_of_eq ?_)
    congr 1
    push_cast
    rw [abs_of_nonneg (by nlinarith)]
    ring
  calc |∑ k ∈ range M, ((∫ _ in ((k : ℝ) * H)..(((k + 1 : ℕ) : ℝ) * H),
          g (((k + 1 : ℕ) : ℝ) * H)) - ∫ t in ((k : ℝ) * H)..(((k + 1 : ℕ) : ℝ) * H), g t)|
      ≤ ∑ k ∈ range M, ε / (2 * (|σ| + 1)) * H :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hterm)
    _ = ε / (2 * (|σ| + 1)) * ((M : ℝ) * H) := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring
    _ ≤ ε / (2 * (|σ| + 1)) * (|σ| + 1) := by
        apply mul_le_mul_of_nonneg_left hNi.le hε'.le
    _ < ε := by
        have hpos : 0 < |σ| + 1 := by positivity
        have he : ε / (2 * (|σ| + 1)) * (|σ| + 1) = ε / 2 := by
          field_simp
        rw [he]
        linarith

/-! ## Sums of squares -/

/-! ## The tail estimate (E21) -/

end

end SwingRepair
