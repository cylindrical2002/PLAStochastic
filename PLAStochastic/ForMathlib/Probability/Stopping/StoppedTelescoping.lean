import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# A stopping-value telescoping series with absolute integral summability

For a bounded measurable process and an integrable natural-valued stop, the
series of surviving increments is absolutely integrable. Splitting at any
deterministic cutoff gives the free cutoff value, a surviving long series, and
the finite already-stopped correction.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Finset

theorem stopped_value_telescoping (Y : ℕ → ℝ) (T M : ℕ) :
    Y T = Y M + (∑' k : ℕ, if k + M < T then Y (k + M + 1) - Y (k + M) else 0) -
      ∑ k ∈ range M, if T ≤ k then Y (k + 1) - Y k else 0 := by
  let G := fun k : ℕ => if k < T then Y (k + 1) - Y k else 0
  let W := fun k : ℕ => if T ≤ k then Y (k + 1) - Y k else 0
  have hz (k : ℕ) (hk : k ∉ range T) : G k = 0 := by
    have hkt : ¬ k < T := by simpa only [mem_range] using hk
    simp only [G, hkt, if_false]
  have hs : Summable G := summable_of_ne_finset_zero hz
  have htotal : (∑' k : ℕ, G k) = Y T - Y 0 := by
    rw [tsum_eq_sum hz]
    calc
      _ = ∑ k ∈ range T, (Y (k + 1) - Y k) := by
        apply sum_congr rfl
        intro k hk
        simp only [G, mem_range.mp hk, if_true]
      _ = _ := sum_range_sub Y T
  have hpart : (∑ k ∈ range M, G k) + (∑ k ∈ range M, W k) = Y M - Y 0 := by
    rw [← sum_add_distrib]
    calc
      _ = ∑ k ∈ range M, (Y (k + 1) - Y k) := by
        apply sum_congr rfl
        intro k _
        by_cases hk : k < T
        · simp only [G, W, hk, if_true, not_le.mpr hk, if_false, add_zero]
        · simp only [G, W, hk, if_false, not_lt.mp hk, if_true, zero_add]
      _ = _ := sum_range_sub Y M
  have hsplit := hs.sum_add_tsum_nat_add M
  rw [htotal] at hsplit
  change Y T = Y M + (∑' k : ℕ, G (k + M)) - ∑ k ∈ range M, W k
  linarith only [hpart, hsplit]

def stoppedIncrement {Ω : Type*} (T : Ω → ℕ) (Y : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  if k < T ω then Y (k + 1) ω - Y k ω else 0

theorem stoppedIncrement_integral_norm_summable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℕ} {Y : ℕ → Ω → ℝ}
    (hT : Measurable T) (hiT : Integrable (fun ω => (T ω : ℝ)) P)
    (hY : ∀ k, Measurable (Y k)) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ k ω, |Y k ω| ≤ B) :
    (∀ k, Integrable (stoppedIncrement T Y k) P) ∧
      Summable (fun k => ∫ ω, ‖stoppedIncrement T Y k ω‖ ∂P) := by
  have hm (k : ℕ) : Measurable (stoppedIncrement T Y k) := by
    apply ((hY (k + 1)).sub (hY k)).piecewise
      (measurableSet_lt measurable_const hT)
      measurable_const
  have hbound (k : ℕ) (ω : Ω) : ‖stoppedIncrement T Y k ω‖ ≤ 2 * B := by
    unfold stoppedIncrement
    split_ifs
    · rw [Real.norm_eq_abs]
      exact (by
        have h := norm_sub_le (Y (k + 1) ω) (Y k ω)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
        linarith only [h, hb (k + 1) ω, hb k ω])
    · simpa only [norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB
  have hi (k : ℕ) : Integrable (stoppedIncrement T Y k) P :=
    (integrable_const (2 * B)).mono' (hm k).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbound k))
  refine ⟨hi, summable_of_sum_range_le (c := 2 * B * ∫ ω, (T ω : ℝ) ∂P)
    (fun k => integral_nonneg fun ω => norm_nonneg _) ?_⟩
  intro N
  have hp (ω : Ω) : ∑ k ∈ range N, ‖stoppedIncrement T Y k ω‖ ≤ 2 * B * T ω := by
    let S := (range N).filter (fun k => k < T ω)
    have heq : (∑ k ∈ range N, ‖stoppedIncrement T Y k ω‖) =
        ∑ k ∈ S, ‖Y (k + 1) ω - Y k ω‖ := by
      rw [sum_filter]
      apply sum_congr rfl
      intro k _
      by_cases hk : k < T ω <;> simp only [stoppedIncrement, hk, if_true, if_false, norm_zero]
    have hsub : S ⊆ range (T ω) := fun k hk =>
      mem_range.mpr ((mem_filter.mp hk).2)
    rw [heq]
    calc
      _ ≤ ∑ k ∈ S, (2 * B) := by
        apply sum_le_sum
        intro k _
        rw [Real.norm_eq_abs]
        exact (by
        have h := norm_sub_le (Y (k + 1) ω) (Y k ω)
        rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at h
        linarith only [h, hb (k + 1) ω, hb k ω])
      _ ≤ ∑ k ∈ range (T ω), (2 * B) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  calc
    _ = ∫ ω, ∑ k ∈ range N, ‖stoppedIncrement T Y k ω‖ ∂P :=
      (integral_finsetSum _ (fun k _ => (hi k).norm)).symm
    _ ≤ ∫ ω, 2 * B * (T ω : ℝ) ∂P :=
      integral_mono (integrable_finsetSum _ (fun k _ => (hi k).norm)) (hiT.const_mul _) hp
    _ = 2 * B * ∫ ω, (T ω : ℝ) ∂P := integral_const_mul _ _

theorem integral_stopped_value_telescoping {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {T : Ω → ℕ} {Y : ℕ → Ω → ℝ}
    (hT : Measurable T) (hiT : Integrable (fun ω => (T ω : ℝ)) P)
    (hY : ∀ k, Measurable (Y k)) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ k ω, |Y k ω| ≤ B)
    (M : ℕ) :
    Summable (fun k : ℕ => ∫ ω, stoppedIncrement T Y (k + M) ω ∂P) ∧
      (∫ ω, Y (T ω) ω ∂P) = (∫ ω, Y M ω ∂P) +
        (∑' k : ℕ, ∫ ω, stoppedIncrement T Y (k + M) ω ∂P) -
        ∑ k ∈ range M, ∫ ω, (if T ω ≤ k then Y (k + 1) ω - Y k ω else 0) ∂P := by
  obtain ⟨hiG, hnG⟩ := stoppedIncrement_integral_norm_summable hT hiT hY hB hb
  have hnTail := (summable_nat_add_iff M).mpr hnG
  have hsTail : Summable (fun k : ℕ => ∫ ω, stoppedIncrement T Y (k + M) ω ∂P) :=
    hnTail.of_norm_bounded (fun k => norm_integral_le_integral_norm _)
  have hiY (k : ℕ) : Integrable (Y k) P :=
    (integrable_const B).mono' (hY k).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb k ω)
  have hmEval : Measurable (fun z : Ω × ℕ => Y z.2 z.1) :=
    measurable_from_prod_countable_left (fun k => hY k)
  have hmStop : Measurable (fun ω => Y (T ω) ω) :=
    hmEval.comp (measurable_id.prodMk hT)
  have hiStop : Integrable (fun ω => Y (T ω) ω) P :=
    (integrable_const B).mono' hmStop.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb (T ω) ω)
  let W := fun k ω => if T ω ≤ k then Y (k + 1) ω - Y k ω else 0
  have hiW (k : ℕ) : Integrable (W k) P := by
    apply (((hiY (k + 1)).sub (hiY k)).sub (hiG k)).congr
    exact Filter.Eventually.of_forall fun ω => by
      by_cases hk : k < T ω
      · simp only [Pi.sub_apply, W, stoppedIncrement, hk, if_true, not_le.mpr hk,
          if_false, sub_self]
      · simp only [Pi.sub_apply, W, stoppedIncrement, hk, if_false, not_lt.mp hk,
          if_true, sub_zero]
  have hiWS : Integrable (fun ω => ∑ k ∈ range M, W k ω) P :=
    integrable_finsetSum _ (fun k _ => hiW k)
  have hp (ω : Ω) : Y (T ω) ω = Y M ω +
      (∑' k : ℕ, stoppedIncrement T Y (k + M) ω) - ∑ k ∈ range M, W k ω :=
    stopped_value_telescoping (fun k => Y k ω) (T ω) M
  have hiTail : Integrable (fun ω => ∑' k : ℕ, stoppedIncrement T Y (k + M) ω) P := by
    apply ((hiStop.sub (hiY M)).add hiWS).congr
    exact Filter.Eventually.of_forall fun ω => by
      have h := hp ω
      dsimp only [Pi.sub_apply, Pi.add_apply]
      linarith only [h]
  refine ⟨hsTail, ?_⟩
  calc
    _ = ∫ ω, Y M ω + (∑' k : ℕ, stoppedIncrement T Y (k + M) ω) -
        ∑ k ∈ range M, W k ω ∂P := integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = (∫ ω, Y M ω ∂P) + (∫ ω, ∑' k : ℕ, stoppedIncrement T Y (k + M) ω ∂P) -
        ∫ ω, ∑ k ∈ range M, W k ω ∂P := by
      rw [integral_sub (f := fun ω => Y M ω + ∑' k : ℕ, stoppedIncrement T Y (k + M) ω)
        ((hiY M).add hiTail) hiWS, integral_add (hiY M) hiTail]
    _ = _ := by
      rw [← integral_tsum_of_summable_integral_norm (fun k => hiG (k + M)) hnTail,
        integral_finsetSum _ (fun k _ => hiW k)]

end

end ProbabilityTheory
