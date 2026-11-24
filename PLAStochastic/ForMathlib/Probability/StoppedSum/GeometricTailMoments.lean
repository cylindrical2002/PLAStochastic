import PLAStochastic.ForMathlib.Probability.StoppedSum.WaldENat
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Real.Sqrt

namespace PGM

/-!
# Moments of a segment length with a geometric block tail

A segment length is a measurable `T : Ω → ℕ∞`.  Fix a block length `L ≥ 1` and a ratio
`0 ≤ r < 1`, and assume the geometric block tail

`P(j L < T) ≤ r ^ j`   for all `j : ℕ`   (`htail`).

Write `T.toNat` for the real-valued surrogate (`⊤ ↦ 0`); it agrees with `T` almost surely.

* `tail_pow_le_tsum`: pointwise `n^(k+1) ≤ L^(k+1) ∑_j 1{jL < n} (k+1)! C(j+k, k)`;
  integrating against `htail` and summing `∑_j C(j+k,k) r^j = (1-r)^{-(k+1)}` gives
  `lintegral_pow_succ_le_of_tail`: `E[T^(k+1)] ≤ (k+1)! / (1-r)^(k+1) * L^(k+1)`.
* `lintegral_le_of_tail`, `ae_lt_top_of_tail`, `measure_eq_top_of_tail`,
  `ae_toNat_eq_of_tail`: `E[T] ≤ L / (1-r)` and `T < ⊤` almost surely.
* `integrable_toNat_pow_of_tail`, `integral_toNat_pow_le_of_tail`,
  `integral_toNat_div_pow_le_of_tail`, `integral_toNat_le_of_tail`: the real moments
  `E[T^q] ≤ q! / (1-r)^q * L^q` and `E[(T/L)^q] ≤ q! / (1-r)^q`.
* `tsum_sqrt_mul_sqrt_tail_le`: `∑_t √t √P(t < T) ≤ (1-√r)^{-2} L √L`, with summability.
* `lintegral_ge_of_lower_tail`, `integral_toNat_ge_of_lower_tail`: `n p ≤ E[T]` when
  `P(n < T) ≥ p`.
* `integral_sq_sub_ge_of_upper_event`: `δ (a/2)^2 ≤ E[(T - C)^2]` when `C ≤ a/2` and
  `P(a ≤ T) ≥ δ`.
-/

open MeasureTheory Finset
open scoped ENNReal Nat

/-- `m ^ (k + 1) ≤ (k + 1)! * ∑_{j < m} C(j + k, k)`. -/
theorem tail_pow_le_sum_choose (m k : ℕ) :
    m ^ (k + 1) ≤ (k + 1)! * ∑ j ∈ range m, (j + k).choose k := by
  rcases m with _ | m
  · simp
  rw [Nat.sum_range_add_choose, ← Nat.descFactorial_eq_factorial_mul_choose]
  have := Nat.pow_sub_le_descFactorial (m + k + 1) (k + 1)
  simpa [show m + k + 1 + 1 - (k + 1) = m + 1 by omega] using this

/-- Pointwise block bound: `n ^ (k+1) ≤ L^(k+1) ∑_j 1{jL < n} (k+1)! C(j+k,k)`. -/
theorem tail_pow_le_tsum (n : ℕ∞) {L : ℕ} (hL : 1 ≤ L) (k : ℕ) :
    (n : ℝ≥0∞) ^ (k + 1) ≤ (L : ℝ≥0∞) ^ (k + 1) *
      ∑' j : ℕ, if ((j * L : ℕ) : ℕ∞) < n then
        (((k + 1)! * (j + k).choose k : ℕ) : ℝ≥0∞) else 0 := by
  induction n using ENat.recTopCoe with
  | top =>
    have hc : ∀ j : ℕ, (1 : ℝ≥0∞) ≤ (((k + 1)! * (j + k).choose k : ℕ) : ℝ≥0∞) := by
      intro j
      exact_mod_cast Nat.one_le_iff_ne_zero.2
        (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.choose_pos (by omega)).ne')
    have hsum : (∑' j : ℕ, if ((j * L : ℕ) : ℕ∞) < ⊤ then
        (((k + 1)! * (j + k).choose k : ℕ) : ℝ≥0∞) else 0) = ⊤ := by
      refine eq_top_iff.2 ?_
      rw [← ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero]
      refine ENNReal.tsum_le_tsum fun j => ?_
      rw [if_pos (ENat.natCast_lt_top _)]
      exact hc j
    rw [hsum, ENNReal.mul_top (pow_ne_zero _ (by exact_mod_cast (by omega : L ≠ 0)))]
    exact le_top
  | coe n =>
    set m := (n + L - 1) / L with hm
    have hnm : n ≤ m * L := by
      have := Nat.lt_div_mul_add (a := n + L - 1) (b := L) (by omega)
      rw [← hm] at this
      omega
    have hj : ∀ j < m, j * L < n := by
      intro j hj
      have h1 : (j + 1) * L ≤ n + L - 1 := (Nat.le_div_iff_mul_le (by omega)).1 hj
      rw [add_mul, one_mul] at h1
      omega
    have key : n ^ (k + 1) ≤ L ^ (k + 1) * ((k + 1)! * ∑ j ∈ range m, (j + k).choose k) :=
      calc n ^ (k + 1) ≤ (m * L) ^ (k + 1) := Nat.pow_le_pow_left hnm _
        _ = L ^ (k + 1) * m ^ (k + 1) := by rw [mul_pow, mul_comm]
        _ ≤ _ := Nat.mul_le_mul_left _ (tail_pow_le_sum_choose m k)
    calc ((n : ℕ∞) : ℝ≥0∞) ^ (k + 1) = ((n ^ (k + 1) : ℕ) : ℝ≥0∞) := by simp
      _ ≤ ((L ^ (k + 1) * ((k + 1)! * ∑ j ∈ range m, (j + k).choose k) : ℕ) : ℝ≥0∞) :=
          Nat.cast_le.2 key
      _ = (L : ℝ≥0∞) ^ (k + 1) * ∑ j ∈ range m,
            (((k + 1)! * (j + k).choose k : ℕ) : ℝ≥0∞) := by
          push_cast [Finset.mul_sum]; rfl
      _ ≤ _ := by
          gcongr
          refine le_trans (le_of_eq (Finset.sum_congr rfl fun j hjm => ?_))
            (ENNReal.sum_le_tsum (range m))
          rw [if_pos (by exact_mod_cast hj j (Finset.mem_range.1 hjm))]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℕ∞} {L : ℕ} {r : ℝ}

theorem tail_measurableSet_lt (hT : Measurable T) (x : ℕ∞) :
    MeasurableSet {ω | x < T ω} :=
  hT (MeasurableSet.of_discrete : MeasurableSet (Set.Ioi x))

/-- **Moment engine.** Under the geometric block tail,
`E[T^(k+1)] ≤ (k+1)! / (1-r)^(k+1) * L^(k+1)` in `ℝ≥0∞`. -/
theorem lintegral_pow_succ_le_of_tail [IsFiniteMeasure P] (hT : Measurable T) (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) (k : ℕ) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ^ (k + 1) ∂P
      ≤ ENNReal.ofReal ((k + 1)! / (1 - r) ^ (k + 1) * L ^ (k + 1)) := by
  set c : ℕ → ℝ≥0∞ := fun j => (((k + 1)! * (j + k).choose k : ℕ) : ℝ≥0∞)
  have hs : ∀ j : ℕ, MeasurableSet {ω | ((j * L : ℕ) : ℕ∞) < T ω} := fun j =>
    tail_measurableSet_lt hT _
  have hr' : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hg := (hasSum_choose_mul_geometric_of_norm_lt_one k hr').mul_left ((k + 1)! : ℝ)
  have hsum : ∑' j : ℕ, c j * ENNReal.ofReal (r ^ j)
      = ENNReal.ofReal ((k + 1)! * (1 / (1 - r) ^ (k + 1))) := by
    rw [← hg.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hg.summable]
    refine tsum_congr fun j => ?_
    rw [← mul_assoc, ENNReal.ofReal_mul (by positivity), ← Nat.cast_mul, ENNReal.ofReal_natCast]
  calc ∫⁻ ω, (T ω : ℝ≥0∞) ^ (k + 1) ∂P
      ≤ ∫⁻ ω, (L : ℝ≥0∞) ^ (k + 1) *
          ∑' j : ℕ, Set.indicator {ω | ((j * L : ℕ) : ℕ∞) < T ω} (fun _ => c j) ω ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using tail_pow_le_tsum (T ω) hL k
    _ = (L : ℝ≥0∞) ^ (k + 1) * ∑' j : ℕ, c j * P {ω | ((j * L : ℕ) : ℕ∞) < T ω} := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_tsum fun j =>
          (measurable_const.indicator (hs j)).aemeasurable]
        simp_rw [lintegral_indicator_const (hs _)]
    _ ≤ (L : ℝ≥0∞) ^ (k + 1) * ∑' j : ℕ, c j * ENNReal.ofReal (r ^ j) := by
        gcongr with j
        rw [← ofReal_measureReal]
        exact ENNReal.ofReal_le_ofReal (htail j)
    _ = _ := by
        rw [hsum, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- **First moment.** `E[T] ≤ L / (1 - r)` in `ℝ≥0∞`. -/
theorem lintegral_le_of_tail [IsFiniteMeasure P] (hT : Measurable T) (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    ∫⁻ ω, (T ω : ℝ≥0∞) ∂P ≤ ENNReal.ofReal (L / (1 - r)) := by
  have h := lintegral_pow_succ_le_of_tail hT hL hr0 hr1 htail 0
  simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one] at h
  rwa [one_div_mul_eq_div] at h

/-- The segment is almost surely finite. -/
theorem ae_lt_top_of_tail [IsFiniteMeasure P] (hT : Measurable T) (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    ∀ᵐ ω ∂P, T ω < ⊤ :=
  wald_ae_lt_top hT (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (lintegral_le_of_tail hT hL hr0 hr1 htail))

/-- `P(T = ⊤) = 0`. -/
theorem measure_eq_top_of_tail [IsFiniteMeasure P] (hT : Measurable T) (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    P {ω | T ω = ⊤} = 0 := by
  have h := ae_iff.1 (ae_lt_top_of_tail hT hL hr0 hr1 htail)
  simpa only [lt_top_iff_ne_top, not_not] using h

/-- `T.toNat` agrees with `T` almost surely. -/
theorem ae_toNat_eq_of_tail [IsFiniteMeasure P] (hT : Measurable T) (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    ∀ᵐ ω ∂P, ((T ω).toNat : ℕ∞) = T ω := by
  filter_upwards [ae_lt_top_of_tail hT hL hr0 hr1 htail] with ω h
  exact ENat.natCast_toNat h.ne

theorem lintegral_ofReal_toNat_pow_le (T : Ω → ℕ∞) (q : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((T ω).toNat : ℝ) ^ q) ∂P ≤ ∫⁻ ω, (T ω : ℝ≥0∞) ^ q ∂P := by
  refine lintegral_mono fun ω => ?_
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  gcongr
  simpa using ENat.toENNReal_le.2 (ENat.natCast_toNat_le_self (T ω))

theorem measurable_toNat_pow (hT : Measurable T) (q : ℕ) :
    Measurable fun ω => ((T ω).toNat : ℝ) ^ q :=
  (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ) ^ q)).comp hT

/-- `T.toNat ^ q` is integrable for every `q`. -/
theorem integrable_toNat_pow_of_tail [IsFiniteMeasure P] (hT : Measurable T) (hL : 1 ≤ L)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) (q : ℕ) :
    Integrable (fun ω => ((T ω).toNat : ℝ) ^ q) P := by
  rcases q with _ | k
  · simp
  refine ⟨(measurable_toNat_pow hT _).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ω => by positivity)).2 ?_⟩
  exact ((lintegral_ofReal_toNat_pow_le T _).trans
    (lintegral_pow_succ_le_of_tail hT hL hr0 hr1 htail k)).trans_lt ENNReal.ofReal_lt_top

/-- **Moments.** `E[T.toNat ^ q] ≤ q! / (1 - r)^q * L^q`. -/
theorem integral_toNat_pow_le_of_tail [IsProbabilityMeasure P] (hT : Measurable T)
    (hL : 1 ≤ L) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) (q : ℕ) :
    ∫ ω, ((T ω).toNat : ℝ) ^ q ∂P ≤ q ! / (1 - r) ^ q * L ^ q := by
  rcases q with _ | k
  · simp
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => by positivity)
    (measurable_toNat_pow hT _).aestronglyMeasurable]
  have h1 : 0 < 1 - r := by linarith
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) ((lintegral_ofReal_toNat_pow_le T _).trans
    (lintegral_pow_succ_le_of_tail hT hL hr0 hr1 htail k))

/-- Normalised moments: `E[(T.toNat / L) ^ q] ≤ q! / (1 - r)^q`. -/
theorem integral_toNat_div_pow_le_of_tail [IsProbabilityMeasure P] (hT : Measurable T)
    (hL : 1 ≤ L) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) (q : ℕ) :
    Integrable (fun ω => (((T ω).toNat : ℝ) / L) ^ q) P ∧
      ∫ ω, (((T ω).toNat : ℝ) / L) ^ q ∂P ≤ q ! / (1 - r) ^ q := by
  have hLpos : (0 : ℝ) < (L : ℝ) ^ q := pow_pos (by exact_mod_cast hL) q
  simp_rw [div_pow]
  refine ⟨(integrable_toNat_pow_of_tail hT hL hr0 hr1 htail q).div_const _, ?_⟩
  rw [integral_div, div_le_iff₀ hLpos]
  exact integral_toNat_pow_le_of_tail hT hL hr0 hr1 htail q

/-- **First moment, real form.** -/
theorem integral_toNat_le_of_tail [IsProbabilityMeasure P] (hT : Measurable T)
    (hL : 1 ≤ L) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    Integrable (fun ω => ((T ω).toNat : ℝ)) P ∧ ∫ ω, ((T ω).toNat : ℝ) ∂P ≤ L / (1 - r) := by
  have h1 := integrable_toNat_pow_of_tail hT hL hr0 hr1 htail 1
  have h2 := integral_toNat_pow_le_of_tail hT hL hr0 hr1 htail 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at h1 h2
  exact ⟨h1, by rwa [one_div_mul_eq_div] at h2⟩

omit [MeasurableSpace Ω] in
theorem sum_range_mul_eq_sum_sum (f : ℕ → ℝ) (N L : ℕ) :
    ∑ t ∈ range (N * L), f t = ∑ j ∈ range N, ∑ i ∈ range L, f (j * L + i) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- **Weighted tail sum.** `∑_t √t √P(t < T) ≤ (1 - √r)⁻² L √L`, with summability. -/
theorem tsum_sqrt_mul_sqrt_tail_le [IsFiniteMeasure P] (hL : 1 ≤ L) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (htail : ∀ j : ℕ, P.real {ω | ((j * L : ℕ) : ℕ∞) < T ω} ≤ r ^ j) :
    Summable (fun t : ℕ => √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < T ω})) ∧
      ∑' t : ℕ, √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < T ω})
        ≤ 1 / (1 - √r) ^ 2 * (L * √L) := by
  set f : ℕ → ℝ := fun t => √(t : ℝ) * √(P.real {ω | (t : ℕ∞) < T ω}) 
  set s := √r with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg r
  have hs1 : s < 1 := (Real.sqrt_lt' one_pos).2 (by simpa using hr1)
  have hs' : ‖s‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
  have hf0 : ∀ t, 0 ≤ f t := fun t => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hblock : ∀ j i : ℕ, i < L → f (j * L + i) ≤ (j + 1) * √(L : ℝ) * s ^ j := by
    intro j i hi
    have h1 : √((j * L + i : ℕ) : ℝ) ≤ (j + 1) * √(L : ℝ) := by
      have hiL : (i : ℝ) + 1 ≤ L := by exact_mod_cast hi
      calc √((j * L + i : ℕ) : ℝ) ≤ √(((j : ℝ) + 1) * L) := by
            refine Real.sqrt_le_sqrt ?_
            push_cast
            nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        _ = √((j : ℝ) + 1) * √(L : ℝ) := Real.sqrt_mul (by positivity) _
        _ ≤ (j + 1) * √(L : ℝ) := by
            gcongr
            refine (Real.sqrt_le_left (by positivity)).2 ?_
            nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have h2 : √(P.real {ω | ((j * L + i : ℕ) : ℕ∞) < T ω}) ≤ s ^ j := by
      have hsub : {ω | ((j * L + i : ℕ) : ℕ∞) < T ω} ⊆ {ω | ((j * L : ℕ) : ℕ∞) < T ω} :=
        fun ω (hω : ((j * L + i : ℕ) : ℕ∞) < T ω) => lt_of_le_of_lt
          (show ((j * L : ℕ) : ℕ∞) ≤ ((j * L + i : ℕ) : ℕ∞) from
            Nat.cast_le.2 (Nat.le_add_right _ _)) hω
      calc √(P.real {ω | ((j * L + i : ℕ) : ℕ∞) < T ω}) ≤ √(r ^ j) :=
            Real.sqrt_le_sqrt ((measureReal_mono hsub).trans (htail j))
        _ = s ^ j := by
            rw [show r ^ j = (s ^ j) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, hs,
              Real.sq_sqrt hr0]]
            exact Real.sqrt_sq (by positivity)
    exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
  have hpartial : ∀ N : ℕ, ∑ t ∈ range N, f t ≤ 1 / (1 - s) ^ 2 * (L * √(L : ℝ)) := by
    intro N
    calc ∑ t ∈ range N, f t ≤ ∑ t ∈ range (N * L), f t :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.2 (Nat.le_mul_of_pos_right N hL)) fun t _ _ => hf0 t
      _ = ∑ j ∈ range N, ∑ i ∈ range L, f (j * L + i) := sum_range_mul_eq_sum_sum f N L
      _ ≤ ∑ j ∈ range N, ∑ i ∈ range L, (j + 1) * √(L : ℝ) * s ^ j :=
          sum_le_sum fun j _ => sum_le_sum fun i hi => hblock j i (mem_range.1 hi)
      _ = (L * √(L : ℝ)) * ∑ j ∈ range N, (((j + 1).choose 1 : ℕ) : ℝ) * s ^ j := by
          rw [Finset.mul_sum]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_const, card_range, nsmul_eq_mul, Nat.choose_one_right]
          push_cast
          ring
      _ ≤ (L * √(L : ℝ)) * (1 / (1 - s) ^ (1 + 1)) := by
          gcongr
          exact sum_le_hasSum _ (fun j _ => by positivity)
            (hasSum_choose_mul_geometric_of_norm_lt_one 1 hs')
      _ = 1 / (1 - s) ^ 2 * (L * √(L : ℝ)) := by ring
  exact ⟨summable_of_sum_range_le hf0 hpartial, Real.tsum_le_of_sum_range_le hf0 hpartial⟩

/-- **Mean from a lower tail**, `ℝ≥0∞` form: `n p ≤ E[T]` when `P(n < T) ≥ p`. -/
theorem lintegral_ge_of_lower_tail (hT : Measurable T) (n : ℕ) {p : ℝ}
    (hp : p ≤ P.real {ω | (n : ℕ∞) < T ω}) :
    ENNReal.ofReal (n * p) ≤ ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
  set s := {ω | (n : ℕ∞) < T ω}
  have hs : MeasurableSet s := tail_measurableSet_lt hT _
  calc ENNReal.ofReal (n * p) ≤ ENNReal.ofReal (n * P.real s) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg n))
    _ = n * ENNReal.ofReal (P s).toReal := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, measureReal_def]
    _ ≤ n * P s := by gcongr; exact ENNReal.ofReal_toReal_le
    _ = ∫⁻ ω, s.indicator (fun _ => (n : ℝ≥0∞)) ω ∂P := (lintegral_indicator_const hs _).symm
    _ ≤ ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases h : (n : ℕ∞) < T ω
        · rw [Set.indicator_of_mem (show ω ∈ s from h)]
          simpa using ENat.toENNReal_le.2 h.le
        · rw [Set.indicator_of_notMem (show ω ∉ s from h)]
          exact zero_le

/-- **Mean from a lower tail**, real form (for an almost surely finite `T`). -/
theorem integral_toNat_ge_of_lower_tail (hT : Measurable T) (hfin : ∀ᵐ ω ∂P, T ω < ⊤)
    (hint : Integrable (fun ω => ((T ω).toNat : ℝ)) P) (n : ℕ) {p : ℝ}
    (hp : p ≤ P.real {ω | (n : ℕ∞) < T ω}) :
    n * p ≤ ∫ ω, ((T ω).toNat : ℝ) ∂P := by
  have heq : ∫⁻ ω, ENNReal.ofReal ((T ω).toNat : ℝ) ∂P = ∫⁻ ω, (T ω : ℝ≥0∞) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hfin] with ω h
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h.ne
    rw [← hm]
    simp
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => Nat.cast_nonneg _)
    hint.aestronglyMeasurable, heq]
  exact (ENNReal.ofReal_le_iff_le_toReal (heq ▸ hint.lintegral_lt_top.ne)).1
    (lintegral_ge_of_lower_tail hT n hp)

/-- **Variance from an upper event.** If `C ≤ a / 2` and `P(a ≤ T.toNat) ≥ δ`, then
`δ (a/2)^2 ≤ E[(T.toNat - C)^2]`; in particular for `C = E[T.toNat]`. -/
theorem integral_sq_sub_ge_of_upper_event [IsFiniteMeasure P] (hT : Measurable T)
    (h2 : Integrable (fun ω => ((T ω).toNat : ℝ) ^ 2) P) {C a δ : ℝ} (hCa : C ≤ a / 2)
    (hδ : δ ≤ P.real {ω | a ≤ ((T ω).toNat : ℝ)}) :
    δ * (a / 2) ^ 2 ≤ ∫ ω, (((T ω).toNat : ℝ) - C) ^ 2 ∂P := by
  set X : Ω → ℝ := fun ω => ((T ω).toNat : ℝ) with hX
  have hXm : Measurable X := (Measurable.of_discrete (f := fun n : ℕ∞ => (n.toNat : ℝ))).comp hT
  have h1 : Integrable X P := h2.mono' hXm.aestronglyMeasurable (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have := Nat.le_self_pow two_ne_zero (T ω).toNat
    simp only [hX]
    exact_mod_cast this)
  have hint : Integrable (fun ω => (X ω - C) ^ 2) P := by
    refine ((h2.sub (h1.const_mul (2 * C))).add (integrable_const (C ^ 2))).congr
      (ae_of_all _ fun ω => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hX]
    ring
  have hE : MeasurableSet {ω | a ≤ X ω} := measurableSet_le measurable_const hXm
  have hpt : ∀ ω, {ω | a ≤ X ω}.indicator (fun _ => (a / 2) ^ 2) ω ≤ (X ω - C) ^ 2 := by
    intro ω
    by_cases h : a ≤ X ω
    · rw [Set.indicator_of_mem (show ω ∈ {ω | a ≤ X ω} from h)]
      have hX0 : 0 ≤ X ω := Nat.cast_nonneg _
      have habs : |a / 2| ≤ X ω - C := abs_le.2 ⟨by linarith, by linarith⟩
      calc (a / 2) ^ 2 = |a / 2| ^ 2 := (sq_abs _).symm
        _ ≤ (X ω - C) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | a ≤ X ω} from h)]
      positivity
  calc δ * (a / 2) ^ 2 ≤ P.real {ω | a ≤ X ω} * (a / 2) ^ 2 :=
        mul_le_mul_of_nonneg_right hδ (sq_nonneg _)
    _ = ∫ ω, {ω | a ≤ X ω}.indicator (fun _ => (a / 2) ^ 2) ω ∂P := by
        rw [integral_indicator_const _ hE, smul_eq_mul]
    _ ≤ ∫ ω, (X ω - C) ^ 2 ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω => Set.indicator_nonneg
          (fun _ _ => sq_nonneg _) ω) hint (ae_of_all _ hpt)

end PGM
