import PLAStochastic.Index.GEP.StrongApprox.Quantile.GaussianTail
import PLAStochastic.Index.GEP.Universality.StrongApproxInterface
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments
import PLAStochastic.Index.GEP.OrbitClosure.CyclicReduction

/-! # Gaussian and source-walk probability bounds for the strong approximation -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Finset
open scoped NNReal ENNReal

/-- A one-sided Gaussian Chernoff bound with its actual variance. -/
theorem sa_gaussian_right_tail {v : ℝ≥0} (hv : 0 < v) {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 v).real (Ioi x) ≤ Real.exp (-(x ^ 2 / (2 * v))) := by
  have hv' : (0 : ℝ) < v := hv
  have hb := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 v) (X := id) x
    (div_nonneg hx hv'.le) (integrable_exp_mul_gaussianReal (x / v))
  rw [mgf_id_gaussianReal] at hb
  simp only [zero_mul, zero_add] at hb
  rw [← Real.exp_add] at hb
  have he : -(x / (v : ℝ)) * x + v * (x / v) ^ 2 / 2 = -(x ^ 2 / (2 * v)) := by
    field_simp
    ring
  rw [he] at hb
  exact (measureReal_mono Set.Ioi_subset_Ici_self).trans hb

/-- The two-sided Gaussian tail bound used at innovations and at walk endpoints. -/
theorem sa_gaussian_abs_tail {v : ℝ≥0} (hv : 0 < v) {x : ℝ} (hx : 0 ≤ x) :
    (gaussianReal 0 v).real {y | x < |y|} ≤ 2 * Real.exp (-(x ^ 2 / (2 * v))) := by
  have he : {y : ℝ | x < |y|} = Ioi x ∪ Iio (-x) := by
    ext y
    simp only [mem_ofPred_eq, mem_union, Set.mem_Ioi, Set.mem_Iio]
    rw [lt_abs]
    constructor <;> rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (by linarith)
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hn : (gaussianReal 0 v).map (fun y : ℝ => -y) = gaussianReal 0 v := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := v))
  have hleft : (gaussianReal 0 v).real (Iio (-x)) = (gaussianReal 0 v).real (Ioi x) := by
    have h := congrArg (fun μ : Measure ℝ => μ.real (Ioi x)) hn
    rw [map_measureReal_apply measurable_neg measurableSet_Ioi] at h
    have he : (fun y : ℝ => -y) ⁻¹' Ioi x = Iio (-x) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_Iio]
      constructor <;> intro hy <;> linarith
    rw [he] at h
    exact h
  rw [he]
  have h := measureReal_union_le (μ := gaussianReal 0 v) (Ioi x) (Iio (-x))
  rw [hleft] at h
  exact h.trans (by linarith [sa_gaussian_right_tail hv hx])

/-- Convolution powers of the standard Gaussian have variance equal to the block length. -/
theorem sa_convPow_standardGaussian (n : ℕ) :
    convPow (gaussianReal 0 1) n = gaussianReal 0 n := by
  induction n with
  | zero => simp [convPow_zero]
  | succ n ih =>
    rw [convPow_succ, ih, gaussianReal_conv_gaussianReal]
    simp

/-- The exact Gaussian walk endpoint law. -/
theorem sa_gaussian_walk_law (n : ℕ) :
    (iidLaw gaussPM).map (fun z => gapKeys z n) = gaussianReal 0 n := by
  rw [map_gapKeys_eq_convPow]
  exact sa_convPow_standardGaussian n

/-- A finite Gaussian walk maximum, bounded by the sum of endpoint tails. -/
theorem sa_gaussian_walk_max_tail (n : ℕ) {x : ℝ} (hx : 0 < x) :
    (iidLaw gaussPM).real {z | ∃ k ≤ n, x < |gapKeys z k|} ≤
      2 * (n + 1) * Real.exp (-(x ^ 2 / (2 * n))) := by
  have he : {z : ℕ → ℝ | ∃ k ≤ n, x < |gapKeys z k|} =
      ⋃ k ∈ range (n + 1), {z | x < |gapKeys z k|} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion, Finset.mem_range, Nat.lt_succ_iff, exists_prop]
  rw [he]
  refine (measureReal_biUnion_finset_le _ _).trans ?_
  calc
    ∑ k ∈ range (n + 1), (iidLaw gaussPM).real {z | x < |gapKeys z k|} ≤
        ∑ _k ∈ range (n + 1), 2 * Real.exp (-(x ^ 2 / (2 * n))) := by
      apply sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      by_cases hk0 : k = 0
      · simp only [hk0, gapKeys_zero, abs_zero, not_lt.mpr hx.le, ofPred_false, measureReal_empty]
        positivity
      have hkpos : (0 : ℝ≥0) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hm : MeasurableSet {y : ℝ | x < |y|} := measurableSet_lt measurable_const measurable_id.abs
      have ht := sa_gaussian_abs_tail hkpos hx.le
      rw [← sa_gaussian_walk_law k, map_measureReal_apply (measurable_gapKeys_apply k) hm] at ht
      refine ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num))
      simp only [NNReal.coe_natCast]
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg x)
        (by positivity : (0 : ℝ) < 2 * k) (by exact_mod_cast Nat.mul_le_mul_left 2 hkn))
    _ = _ := by simp; ring

/-- Bernstein's maximum bound applies on any fixed block of the original iid gap sequence. -/
theorem sa_source_block_max_tail {θ B : ℝ} (hθ : 0 < θ) {ν : ProbabilityMeasure ℝ}
    (hpos : (ν : Measure ℝ) (Iic 0) = 0) (hmean : lawMean ν = 1) (hexp : ExpMom θ B ν)
    (u m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx : 0 < x) :
    (iidLaw ν).real {z | ∃ k ≤ m, x < |gapKeys z (u + k) - gapKeys z u - k|} ≤
      2 * Real.exp (-(bernsteinRate θ B * min (x ^ 2 / m) x)) := by
  have h := iid_maximal_bernstein hθ hpos hmean hexp m hm hx
  have hset : MeasurableSet {z : ℕ → ℝ | ∃ k ≤ m, x < |gapKeys z k - k|} := by
    have he : {z : ℕ → ℝ | ∃ k ≤ m, x < |gapKeys z k - k|} =
        ⋃ k, ⋃ (_ : k ≤ m), {z | x < |gapKeys z k - k|} := by ext z; simp
    rw [he]
    exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
      measurableSet_lt measurable_const ((measurable_gapKeys_apply k).sub_const _).abs
  rw [← map_shift_iidLaw ν u, map_measureReal_apply (by fun_prop) hset] at h
  simpa only [Set.preimage_ofPred_eq, gapKeys_shift] using h

end

end PGM
