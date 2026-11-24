import PLAStochastic.Index.KEP.StoppedPrefixes
import PLAStochastic.ForMathlib.Probability.Hellinger.Coupling
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Passing a paid uniform finite-prefix comparison to the full stopped path

The original extended stopping rule defines the common stopped-path map.
Its finite observed prefix agrees with the full path whenever stopping has
already occurred. Actual geometric tails pay the approximation on each side.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def kepStoppedGapPath (eps : ℝ) (g : ℕ → ℝ) : ℕ → ℝ :=
  fun k => if (k : ℕ∞) < gapSegLen eps g then g k else 0

theorem measurable_kepStoppedGapPath (eps : ℝ) : Measurable (kepStoppedGapPath eps) := by
  refine measurable_pi_lambda _ fun k => ?_
  exact Measurable.ite ((isStoppingRule_gapSegLen eps).measurableSet_lt k)
    (measurable_pi_apply k) measurable_const

theorem kepStoppedGapPath_prefix_of_stopped {eps : ℝ} {g : ℕ → ℝ} {N : ℕ}
    (ht : gapSegLen eps g ≤ (N : ℕ∞)) :
    kepStoppedGapPath eps g = kepStoppedPrefix eps N g := by
  funext k
  by_cases hk : (k : ℕ∞) < gapSegLen eps g
  · have hkn : k < N := ENat.natCast_lt_natCast.mp (hk.trans_le ht)
    simp only [kepStoppedGapPath, kepStoppedPrefix, hk, hkn, and_self, if_true]
  · simp only [kepStoppedGapPath, kepStoppedPrefix, hk, and_false, if_false]

instance isProbabilityMeasure_map_kepStoppedGapPath
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (eps : ℝ) :
    IsProbabilityMeasure (P.map (kepStoppedGapPath eps)) :=
  Measure.isProbabilityMeasure_map (measurable_kepStoppedGapPath eps).aemeasurable

instance isProbabilityMeasure_map_kepStoppedPrefix
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (eps : ℝ) (N : ℕ) :
    IsProbabilityMeasure (P.map (kepStoppedPrefix eps N)) :=
  Measure.isProbabilityMeasure_map (measurable_kepStoppedPrefix eps N).aemeasurable

theorem measureHellinger_stopped_path_prefix (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P]
    (eps : ℝ) (N : ℕ) :
    measureHellinger (P.map (kepStoppedGapPath eps)) (P.map (kepStoppedPrefix eps N)) ≤
      Real.sqrt (2 * P.real {g | (N : ℕ∞) < gapSegLen eps g}) := by
  have hs : MeasurableSet {g : ℕ → ℝ | gapSegLen eps g ≤ (N : ℕ∞)} :=
    by simpa only [compl_ofPred, not_lt] using
      ((isStoppingRule_gapSegLen eps).measurableSet_lt N).compl
  have h := measureHellinger_coupled_outputs P (measurable_kepStoppedGapPath eps)
    (measurable_kepStoppedPrefix eps N) hs (fun g hg => kepStoppedGapPath_prefix_of_stopped hg)
  simpa only [compl_ofPred, not_le] using h

theorem measureHellinger_stopped_paths_of_prefix_bound
    (P Q : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (eps : ℝ) (M : ℕ) {A r : ℝ} (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprefix : ∀ N, measureHellinger (P.map (kepStoppedPrefix eps N))
      (Q.map (kepStoppedPrefix eps N)) ^ 2 ≤ A)
    (hPtail : ∀ k, P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ r ^ k)
    (hQtail : ∀ k, Q.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ r ^ k) :
    measureHellinger (P.map (kepStoppedGapPath eps)) (Q.map (kepStoppedGapPath eps)) ^ 2 ≤ A := by
  have hfin (N : ℕ) : measureHellinger (P.map (kepStoppedPrefix eps N))
      (Q.map (kepStoppedPrefix eps N)) ≤ Real.sqrt A := by
    nlinarith [hprefix N, Real.sq_sqrt hA, Real.sqrt_nonneg A,
      measureHellinger_nonneg (P.map (kepStoppedPrefix eps N)) (Q.map (kepStoppedPrefix eps N))]
  have hbound (k : ℕ) : measureHellinger (P.map (kepStoppedGapPath eps))
      (Q.map (kepStoppedGapPath eps)) ≤ 2 * Real.sqrt (2 * r ^ k) + Real.sqrt A := by
    have hP := (measureHellinger_stopped_path_prefix P eps (k * M)).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hPtail k) (by norm_num)))
    have hQ := (measureHellinger_stopped_path_prefix Q eps (k * M)).trans
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hQtail k) (by norm_num)))
    have ht := measureHellinger_triangle (P.map (kepStoppedGapPath eps))
      (P.map (kepStoppedPrefix eps (k * M))) (Q.map (kepStoppedGapPath eps))
    have ht' := measureHellinger_triangle (P.map (kepStoppedPrefix eps (k * M)))
      (Q.map (kepStoppedPrefix eps (k * M))) (Q.map (kepStoppedGapPath eps))
    rw [measureHellinger_comm (Q.map (kepStoppedPrefix eps (k * M)))] at ht'
    linarith only [ht, ht', hP, hQ, hfin (k * M)]
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hlim : Tendsto (fun k : ℕ => 2 * Real.sqrt (2 * r ^ k) + Real.sqrt A)
      atTop (𝓝 (Real.sqrt A)) := by
    simpa only [mul_zero, Real.sqrt_zero, zero_add] using
      (tendsto_const_nhds.mul ((tendsto_const_nhds.mul hpow).sqrt)).add_const (Real.sqrt A)
  have hle := ge_of_tendsto' hlim hbound
  nlinarith [Real.sq_sqrt hA, Real.sqrt_nonneg A,
    measureHellinger_nonneg (P.map (kepStoppedGapPath eps)) (Q.map (kepStoppedGapPath eps))]

end

end PGM
