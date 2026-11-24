import PLAStochastic.ForMathlib.Probability.StoppedSum.GeometricTailMoments

/-!
# Linear active mass and cubic square-root tail budgets

Geometric stopping blocks pay the active-step count by one block length.
The squared time weight with the square root of the true stopping probability
is paid by the cube of that length. These are separate costs in a stopped
Hellinger chain, so the constant perturbation retains its linear horizon cost.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {T : Ω → ℕ∞} {L : ℕ} {r : ℝ}

theorem sum_stopping_tail_le_geometric_blocks (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {w | ((j * L : ℕ) : ℕ∞) < T w} ≤ r ^ j) (N : ℕ) :
    ∑ i ∈ range N, P.real {w | (i : ℕ∞) < T w} ≤ (L : ℝ) / (1 - r) := by
  let p : ℕ → ℝ := fun i => P.real {w | (i : ℕ∞) < T w}
  have hp : ∀ i, 0 ≤ p i := fun _ => measureReal_nonneg
  have hblock (j i : ℕ) : p (j * L + i) ≤ r ^ j := by
    exact (measureReal_mono (fun w hw =>
      (ENat.natCast_le_natCast.mpr (Nat.le_add_right (j * L) i)).trans_lt hw)).trans (htail j)
  have hs : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  calc
    _ ≤ ∑ i ∈ range (N * L), p i :=
      sum_le_sum_of_subset_of_nonneg
        (range_subset_range.mpr (Nat.le_mul_of_pos_right N hL)) (fun i _ _ => hp i)
    _ = ∑ j ∈ range N, ∑ i ∈ range L, p (j * L + i) := sum_range_mul_eq_sum_sum p N L
    _ ≤ ∑ j ∈ range N, ∑ _i ∈ range L, r ^ j :=
      sum_le_sum (fun j _ => sum_le_sum (fun i _ => hblock j i))
    _ = (L : ℝ) * ∑ j ∈ range N, r ^ j := by
      simp only [sum_const, card_range, nsmul_eq_mul, mul_sum]
    _ ≤ (L : ℝ) * (1 / (1 - r) ^ (0 + 1)) := by
      gcongr
      simpa only [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul] using
        sum_le_hasSum (range N) (fun j _ => by positivity)
          (hasSum_choose_mul_geometric_of_norm_lt_one 0 hs)
    _ = _ := by rw [zero_add, pow_one, mul_one_div]

theorem tsum_sq_mul_sqrt_tail_le (hL : 1 ≤ L) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {w | ((j * L : ℕ) : ℕ∞) < T w} ≤ r ^ j) :
    Summable (fun i : ℕ => (i : ℝ) ^ 2 * Real.sqrt (P.real {w | (i : ℕ∞) < T w})) ∧
      ∑' i : ℕ, (i : ℝ) ^ 2 * Real.sqrt (P.real {w | (i : ℕ∞) < T w}) ≤
        2 / (1 - Real.sqrt r) ^ 3 * (L : ℝ) ^ 3 := by
  let f : ℕ → ℝ := fun i => (i : ℝ) ^ 2 * Real.sqrt (P.real {w | (i : ℕ∞) < T w})
  let s := Real.sqrt r
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hs1 : s < 1 := (Real.sqrt_lt' one_pos).mpr (by simpa using hr1)
  have hs : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
  have hf : ∀ i, 0 ≤ f i := fun _ => mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hblock (j i : ℕ) (hi : i < L) :
      f (j * L + i) ≤ 2 * (((j + 2).choose 2 : ℕ) : ℝ) * (L : ℝ) ^ 2 * s ^ j := by
    have ht : Real.sqrt (P.real {w | ((j * L + i : ℕ) : ℕ∞) < T w}) ≤ s ^ j := by
      calc
        _ ≤ Real.sqrt (r ^ j) := Real.sqrt_le_sqrt
          ((measureReal_mono (fun w hw =>
            (ENat.natCast_le_natCast.mpr (Nat.le_add_right (j * L) i)).trans_lt hw)).trans (htail j))
        _ = _ := by
          have hsquare : s ^ 2 = r := Real.sq_sqrt hr0
          rw [show r ^ j = (s ^ j) ^ 2 by
            rw [← pow_mul, mul_comm, pow_mul, hsquare]]
          exact Real.sqrt_sq (pow_nonneg hs0 j)
    have htime : ((j * L + i : ℕ) : ℝ) ≤ ((j : ℝ) + 1) * L := by
      have ht' : j * L + i ≤ (j + 1) * L := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left hi.le _
      exact_mod_cast ht'
    have hc : ((j : ℝ) + 1) ^ 2 ≤ 2 * (((j + 2).choose 2 : ℕ) : ℝ) := by
      have h := tail_pow_le_sum_choose (j + 1) 1
      rw [Nat.sum_range_add_choose] at h
      norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.mul_one, Nat.add_assoc] at h
      exact_mod_cast h
    have hpoly : (((j * L + i : ℕ) : ℝ) ^ 2) ≤
        2 * (((j + 2).choose 2 : ℕ) : ℝ) * (L : ℝ) ^ 2 := by
      calc
        _ ≤ (((j : ℝ) + 1) * L) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) htime 2
        _ = ((j : ℝ) + 1) ^ 2 * (L : ℝ) ^ 2 := mul_pow _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    exact mul_le_mul hpoly ht (Real.sqrt_nonneg _) (by positivity)
  have hpartial (N : ℕ) : ∑ i ∈ range N, f i ≤ 2 / (1 - s) ^ 3 * (L : ℝ) ^ 3 := by
    calc
      _ ≤ ∑ i ∈ range (N * L), f i :=
        sum_le_sum_of_subset_of_nonneg
          (range_subset_range.mpr (Nat.le_mul_of_pos_right N hL)) (fun i _ _ => hf i)
      _ = ∑ j ∈ range N, ∑ i ∈ range L, f (j * L + i) := sum_range_mul_eq_sum_sum f N L
      _ ≤ ∑ j ∈ range N, ∑ _i ∈ range L,
          2 * (((j + 2).choose 2 : ℕ) : ℝ) * (L : ℝ) ^ 2 * s ^ j :=
        sum_le_sum (fun j _ => sum_le_sum (fun i hi => hblock j i (mem_range.mp hi)))
      _ = 2 * (L : ℝ) ^ 3 * ∑ j ∈ range N, (((j + 2).choose 2 : ℕ) : ℝ) * s ^ j := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        simp only [sum_const, card_range, nsmul_eq_mul]
        ring
      _ ≤ 2 * (L : ℝ) ^ 3 * (1 / (1 - s) ^ (2 + 1)) := by
        gcongr
        exact sum_le_hasSum _ (fun j _ => by positivity)
          (hasSum_choose_mul_geometric_of_norm_lt_one 2 hs)
      _ = _ := by ring
  exact ⟨summable_of_sum_range_le hf hpartial, Real.tsum_le_of_sum_range_le hf hpartial⟩

end

end PGM
