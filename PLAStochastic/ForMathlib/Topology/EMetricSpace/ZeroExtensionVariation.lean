import PLAStochastic.ForMathlib.MeasureTheory.Integral.HalfLineTrace
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Derivative and boundary contributions to variation

The zero extension retains both endpoint jumps. The estimates apply to complex
functions and do not require any derivative of the original step density.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal Interval

variable {v dv : ℝ → ℂ} {a b : ℝ}

theorem kernelVariation_le_integral (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt v (dv x) x)
    (hi : IntervalIntegrable dv volume a b) :
    eVariationOn v (Icc a b) ≤ ENNReal.ofReal (∫ x in a..b, ‖dv x‖) := by
  have hi' {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      IntervalIntegrable dv volume x y :=
    hi.mono_set (by rw [uIcc_of_le hxy, uIcc_of_le hab]; exact Icc_subset_Icc hx.1 hy.2)
  have hdist {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
      edist (v y) (v x) ≤ ENNReal.ofReal (∫ t in x..y, ‖dv t‖) := by
    rw [edist_dist, dist_eq_norm]
    apply ENNReal.ofReal_le_ofReal
    have he : ∫ t in x..y, dv t = v y - v x :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hd t (by rw [uIcc_of_le hxy] at ht; exact ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩))
        (hi' hx hy hxy)
    rw [← he]
    exact intervalIntegral.norm_integral_le_integral_norm hxy
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  calc
    (∑ i ∈ Finset.range n, edist (v (u (i + 1))) (v (u i))) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (∫ t in u i..u (i + 1), ‖dv t‖) := by
      exact Finset.sum_le_sum fun i _ => hdist (hs i) (hs (i + 1)) (hu (Nat.le_succ i))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, ∫ t in u i..u (i + 1), ‖dv t‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact intervalIntegral.integral_nonneg (hu (Nat.le_succ i)) (fun _ _ => norm_nonneg _)
    _ = ENNReal.ofReal (∫ t in u 0..u n, ‖dv t‖) := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun i _ => (hi' (hs i) (hs (i + 1)) (hu (Nat.le_succ i))).norm)]
    _ ≤ ENNReal.ofReal (∫ t in a..b, ‖dv t‖) := by
      apply ENNReal.ofReal_le_ofReal
      exact intervalIntegral.integral_mono_interval (hs 0).1 (hu (Nat.zero_le n)) (hs n).2
        (Eventually.of_forall fun _ => norm_nonneg _) hi.norm

/-- Exact variation of zero extension, including both jumps at the boundary. -/
theorem kernelVariation_indicator_eq (hab : a ≤ b) (v : ℝ → ℂ) :
    eVariationOn ((Icc a b).indicator v) univ =
      ENNReal.ofReal ‖v a‖ + eVariationOn v (Icc a b) + ENNReal.ofReal ‖v b‖ := by
  let f := (Icc a b).indicator v
  have hL0 : EqOn f (fun _ => 0) (Iio a) := by
    intro x hx
    exact indicator_of_notMem (fun h => not_lt_of_ge h.1 hx) _
  have hR0 : EqOn f (fun _ => 0) (Ioi b) := by
    intro x hx
    exact indicator_of_notMem (fun h => not_lt_of_ge h.2 hx) _
  have hLlim : Tendsto f (𝓝[Iio a] a) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx using (hL0 hx).symm
  have hRlim : Tendsto f (𝓝[Ioi b] b) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx using (hR0 hx).symm
  have hL : eVariationOn f (Iic a) = ENNReal.ofReal ‖v a‖ := by
    have he := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
      (s := univ) (a := a) (f := f) (l := 0)
      (by simpa only [univ_inter] using (inferInstance : (𝓝[Iio a] a).NeBot))
      (mem_univ a) (by simpa only [univ_inter] using hLlim)
    simp only [univ_inter] at he
    rw [he, eVariationOn.eq_of_eqOn hL0]
    have hz : eVariationOn (fun _ : ℝ => (0 : ℂ)) (Iio a) = 0 :=
      eVariationOn.constant_on (by simp)
    simp [hz, f, indicator_of_mem (show a ∈ Icc a b from ⟨le_rfl, hab⟩), edist_dist]
  have hR : eVariationOn f (Ici b) = ENNReal.ofReal ‖v b‖ := by
    have he := eVariationOn.eVariationOn_on_inter_Ici_eq_Ioi_add_edist
      (s := univ) (a := b) (f := f) (l := 0)
      (by simpa only [univ_inter] using (inferInstance : (𝓝[Ioi b] b).NeBot))
      (mem_univ b) (by simpa only [univ_inter] using hRlim)
    simp only [univ_inter] at he
    rw [he, eVariationOn.eq_of_eqOn hR0]
    have hz : eVariationOn (fun _ : ℝ => (0 : ℂ)) (Ioi b) = 0 :=
      eVariationOn.constant_on (by simp)
    simp [hz, f, indicator_of_mem (show b ∈ Icc a b from ⟨hab, le_rfl⟩), edist_dist]
  have hmid : eVariationOn f (Icc a b) = eVariationOn v (Icc a b) :=
    eVariationOn.eq_of_eqOn fun x hx => indicator_of_mem hx v
  have hsplit := eVariationOn.union f (isGreatest_Iic : IsGreatest (Iic a) a)
    (isLeast_Ici : IsLeast (Ici a) a)
  have hsplitR := eVariationOn.union f
    (show IsGreatest (Icc a b) b from ⟨⟨hab, le_rfl⟩, fun _ h => h.2⟩)
    (isLeast_Ici : IsLeast (Ici b) b)
  have hsets : Icc a b ∪ Ici b = Ici a := by ext x; simp only [mem_union, mem_Icc, mem_Ici]; grind
  rw [hsets] at hsplitR
  rw [Iic_union_Ici] at hsplit
  change eVariationOn f univ = _
  rw [hsplit, hsplitR, hL, hR, hmid, add_assoc]

theorem kernelVariation_indicator_le (hab : a ≤ b)
    (hd : ∀ x ∈ Icc a b, HasDerivAt v (dv x) x)
    (hi : IntervalIntegrable dv volume a b) :
    eVariationOn ((Icc a b).indicator v) univ ≤
      ENNReal.ofReal ((∫ x in a..b, ‖dv x‖) + ‖v a‖ + ‖v b‖) := by
  rw [kernelVariation_indicator_eq hab]
  have hint : 0 ≤ ∫ x in a..b, ‖dv x‖ :=
    intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)
  rw [ENNReal.ofReal_add (add_nonneg hint (norm_nonneg _)) (norm_nonneg _),
    ENNReal.ofReal_add hint (norm_nonneg _)]
  simpa only [add_comm, add_left_comm, add_assoc] using
    add_le_add_right (add_le_add_left (kernelVariation_le_integral hab hd hi)
      (ENNReal.ofReal ‖v a‖)) (ENNReal.ofReal ‖v b‖)

end
end PGM
