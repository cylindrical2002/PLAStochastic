import PLAStochastic.Brownian.Hitting.OneSidedTail
import PLAStochastic.Affine.Moments.Anchored.ExpandingStrip
import Mathlib.Probability.Distributions.Exponential

/-!
# The exponential laws of the two marginal drifted suprema

Each supremum has rate two. Both are defined from the same Brownian path;
these marginal laws make no independence assertion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem hasLaw_driftedSup_toReal_expMeasure (hB : IsBrownianReal B μ) :
    HasLaw (fun ω => (driftedSup (B · ω) 1).toReal) (expMeasure 2) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsProbabilityMeasure (expMeasure 2) := isProbabilityMeasure_expMeasure (by norm_num)
  let X := fun ω => (driftedSup (B · ω) 1).toReal
  have hX : AEMeasurable X μ := (aemeasurable_driftedPair hB 1).fst.ennreal_toReal
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  refine ⟨hX, Measure.eq_of_cdf _ _ ?_⟩
  ext a
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hX measurableSet_Iic,
    cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 2)]
  by_cases ha : 0 ≤ a
  · rw [if_pos ha]
    have htail : μ.real {ω | a < X ω} = Real.exp (-2 * a) := by
      calc
        μ.real {ω | a < X ω} = μ.real {ω | ENNReal.ofReal a < driftedSup (B · ω) 1} := by
          apply measureReal_congr
          filter_upwards [driftedPair_ne_top_ae hB] with ω hω
          exact propext (ENNReal.ofReal_lt_iff_lt_toReal ha hω.1).symm
        _ = Real.exp (-2 * a) := by
          rw [measureReal_def, measure_driftedSup_gt hB ha, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    have heq : X ⁻¹' Iic a = {ω | a < X ω}ᶜ := by ext ω; simp
    have hnull : NullMeasurableSet {ω | a < X ω} μ :=
      hX.nullMeasurableSet_preimage measurableSet_Ioi
    rw [heq, measureReal_compl₀ hnull]
    simp only [probReal_univ, htail, neg_mul]
  · rw [if_neg ha]
    have heq : X ⁻¹' Iic a = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact (not_le_of_gt (lt_of_lt_of_le (lt_of_not_ge ha) ENNReal.toReal_nonneg)) hω
    rw [heq, measureReal_empty]

theorem hasLaw_realDriftedSup_expMeasure (hB : IsBrownianReal B μ) :
    HasLaw (fun ω => realDriftedSup (B · ω) 1) (expMeasure 2) μ := by
  apply (hasLaw_driftedSup_toReal_expMeasure hB).congr
  filter_upwards [hB.eval_zero_ae_eq_zero, driftedPair_ne_top_ae hB] with ω h0 hfin
  exact (driftedSup_toReal_eq_realDriftedSup h0 hfin.1).symm

theorem hasLaw_realDriftedSup_neg_expMeasure (hB : IsBrownianReal B μ) :
    HasLaw (fun ω => realDriftedSup (fun t => -B t ω) 1) (expMeasure 2) μ :=
  hasLaw_realDriftedSup_expMeasure hB.neg

end BrownianAffine
