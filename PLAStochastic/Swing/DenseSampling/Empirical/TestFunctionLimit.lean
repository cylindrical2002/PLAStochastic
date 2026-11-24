import PLAStochastic.Swing.DenseSampling.Empirical.SignBalance

/-! # Test-function limit of the actual completed native errors -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def nativeNormalizedRecordingError (t y : ℕ → ℝ) (ε : ℝ)
    (segs : List NativeSegment) (k : ℕ) : ℝ :=
  (nativeSegmentEndpoint t (nativeSegmentAt segs k) - y (nativeSegmentAt segs k).finish) / ε

def nativeCompletedTestAverage (t y : ℕ → ℝ) (ε : ℝ)
    (segs : List NativeSegment) (φ : ℝ → ℝ) : ℝ :=
  (∑ k ∈ Finset.range (segs.length - 1), φ (nativeNormalizedRecordingError t y ε segs k)) /
    ((segs.length - 1 : ℕ) : ℝ)

theorem abs_average_sub_le {n : ℕ} {a b : ℕ → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hab : ∀ k < n, |a k - b k| ≤ r) :
    |(∑ k ∈ Finset.range n, a k) / n - (∑ k ∈ Finset.range n, b k) / n| ≤ r := by
  by_cases hn : n = 0
  · simp [hn, hr]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div]
  rw [abs_of_nonneg (show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  calc
    |∑ k ∈ Finset.range n, (a k - b k)| / n ≤
        (∑ _k ∈ Finset.range n, r) / n :=
      div_le_div_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun k hk => hab k (Finset.mem_range.mp hk))) (Nat.cast_nonneg n)
    _ = r := by simp [Finset.card_range, hn0]

theorem test_at_polarity (φ : ℝ → ℝ) (x : ℝ) :
    φ (nativePolarity x) = (φ 1 + φ (-1)) / 2 +
      ((φ 1 - φ (-1)) / 2) * nativePolarity x := by
  rcases nativePolarity_values x with hp | hn
  · rw [hp]; ring
  · rw [hn]; ring

/-- Continuous tests of a point and its nearest signed boundary value become
uniformly close when their separation becomes uniformly small. -/
theorem exists_uniform_native_test_rounding (f φ : C(ℝ, ℝ)) {T ε r : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ → ∀ N : ℕ, (N : ℝ) * h ≤ T →
      ∀ k : ℕ, k < nativeCompletedCount (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ε N →
      let x := nativeNormalizedRecordingError (fun j => (j : ℝ) * h)
        (fun j => f ((j : ℝ) * h)) ε
        (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε N) k
      |φ x - φ (nativePolarity x)| < r := by
  obtain ⟨d₁, hd₁, h₁⟩ := Metric.continuousAt_iff.mp (φ.continuous.continuousAt (x := 1)) r hr
  obtain ⟨d₂, hd₂, h₂⟩ := Metric.continuousAt_iff.mp (φ.continuous.continuousAt (x := -1)) r hr
  obtain ⟨δ, hδ, hround⟩ := exists_uniform_native_rounding f hT hε (lt_min hd₁ hd₂)
  refine ⟨δ, hδ, ?_⟩
  intro h hh hhδ N hN k hk
  dsimp only
  let x := nativeNormalizedRecordingError (fun j => (j : ℝ) * h)
    (fun j => f ((j : ℝ) * h)) ε
    (nativeStream (fun j => (j : ℝ) * h) (fun j => f ((j : ℝ) * h)) ε N) k
  have hx : |x - nativePolarity x| < min d₁ d₂ := hround h hh hhδ N hN k hk
  change |φ x - φ (nativePolarity x)| < r
  rcases nativePolarity_values x with hp | hn
  · rw [hp] at hx ⊢
    exact h₁ (by simpa only [Real.dist_eq] using hx.trans_le (min_le_left _ _))
  · rw [hn] at hx ⊢
    exact h₂ (by simpa only [Real.dist_eq] using hx.trans_le (min_le_right _ _))

/-- Every continuous test of all completed native recording errors converges to
the equally weighted signed-boundary average. The count hypothesis is supplied
by the proved Brownian fixed-index degeneration theorem. -/
theorem native_completed_test_average_tendsto (f φ : C(ℝ, ℝ)) {T ε : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) {ι : Type*} {l : Filter ι}
    {h : ι → ℝ} {N : ι → ℕ} (hh : ∀ i, 0 < h i) (hconv : Tendsto h l (𝓝 0))
    (hN : ∀ i, (N i : ℝ) * h i ≤ T)
    (hcount : Tendsto (fun i => nativeCompletedCount (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε (N i)) l atTop) :
    Tendsto (fun i => nativeCompletedTestAverage (fun j => (j : ℝ) * h i)
      (fun j => f ((j : ℝ) * h i)) ε
      (nativeStream (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε (N i)) φ)
      l (𝓝 ((φ 1 + φ (-1)) / 2)) := by
  let segs i := nativeStream (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) ε (N i)
  let R i := (segs i).length - 1
  let x i k := nativeNormalizedRecordingError (fun j => (j : ℝ) * h i)
    (fun j => f ((j : ℝ) * h i)) ε (segs i) k
  let A i := nativeCompletedTestAverage (fun j => (j : ℝ) * h i)
    (fun j => f ((j : ℝ) * h i)) ε (segs i) φ
  let P i := (∑ k ∈ Finset.range (R i), φ (nativePolarity (x i k))) / (R i : ℝ)
  have hdiff : Tendsto (fun i => A i - P i) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro r hr
    obtain ⟨δ, hδ, hround⟩ := exists_uniform_native_test_rounding f φ hT hε (half_pos hr)
    filter_upwards [hconv.eventually_lt_const hδ] with i hi
    have hab := abs_average_sub_le (a := fun k => φ (x i k))
      (b := fun k => φ (nativePolarity (x i k))) (half_pos hr).le
      (fun k hk => (hround (h i) (hh i) hi (N i) (hN i) k hk).le)
    simpa only [A, P, R, segs, nativeCompletedTestAverage, nativeCompletedCount, Real.dist_eq, sub_zero]
      using hab.trans_lt (half_lt_self hr)
  have hsign := native_sign_average_tendsto_zero f hT hε hh hconv hN hcount
  have hP : Tendsto P l (𝓝 ((φ 1 + φ (-1)) / 2)) := by
    have hm := (hsign.const_mul ((φ 1 - φ (-1)) / 2)).const_add ((φ 1 + φ (-1)) / 2)
    simp only [mul_zero, add_zero] at hm
    apply hm.congr'
    filter_upwards [hcount.eventually (eventually_gt_atTop 0)] with i hi
    have hR : (R i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi)
    change (φ 1 + φ (-1)) / 2 + ((φ 1 - φ (-1)) / 2) *
      (nativeCompletedSignSum (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i))
        (segs i) / (R i : ℝ)) = P i
    dsimp only [P]
    have heq : (∑ k ∈ Finset.range (R i), φ (nativePolarity (x i k))) =
        ∑ k ∈ Finset.range (R i), ((φ 1 + φ (-1)) / 2 +
          ((φ 1 - φ (-1)) / 2) * nativePolarity (x i k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact test_at_polarity φ (x i k)
    rw [heq]
    simp only [x, nativeNormalizedRecordingError, nativePolarity_div_pos _ hε]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    change _ = ((R i : ℝ) * ((φ 1 + φ (-1)) / 2) +
      ((φ 1 - φ (-1)) / 2) * nativeCompletedSignSum
        (fun j => (j : ℝ) * h i) (fun j => f ((j : ℝ) * h i)) (segs i)) / (R i : ℝ)
    field_simp
    simp only [mul_comm]
  have ht := hdiff.add hP
  simpa only [sub_add_cancel, zero_add] using ht

end SwingRepair
