import PLAStochastic.Affine.Process.Hitting.DoobWedge
import PLAStochastic.ForMathlib.Probability.CDF.JointTriangle

/-!
# The actual Brownian supremum sum and the integrated wedge probability
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def brownianSupremumPair (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ × ℝ :=
  (realDriftedSup (B · ω) 1, realDriftedSup (fun t => -B t ω) 1)

def brownianSupremaLaw (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) : Measure (ℝ × ℝ) :=
  μ.map (brownianSupremumPair B)

theorem aemeasurable_brownianSupremumPair (hB : IsBrownianReal B μ) :
    AEMeasurable (brownianSupremumPair B) μ :=
  (hasLaw_realDriftedSup_expMeasure hB).aemeasurable.prodMk
    (hasLaw_realDriftedSup_neg_expMeasure hB).aemeasurable

theorem brownianSupremumPair_nonneg_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, 0 ≤ (brownianSupremumPair B ω).1 ∧ 0 ≤ (brownianSupremumPair B ω).2 := by
  filter_upwards [hB.eval_zero_ae_eq_zero, driftedPair_ne_top_ae hB] with ω h0 hf
  change 0 ≤ realDriftedSup (B · ω) 1 ∧ 0 ≤ realDriftedSup (fun t => -B t ω) 1
  rw [← driftedSup_toReal_eq_realDriftedSup h0 hf.1,
    ← driftedSup_toReal_eq_realDriftedSup (by simp only [h0, neg_zero]) hf.2]
  exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_nonneg⟩

theorem brownianSupremaLaw_nonneg_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ p ∂brownianSupremaLaw B μ, 0 ≤ p.1 ∧ 0 ≤ p.2 :=
  (ae_map_iff (aemeasurable_brownianSupremumPair hB)
    ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd))).mpr
    (brownianSupremumPair_nonneg_ae hB)

theorem brownianSupremaLaw_map_sum (hB : IsBrownianReal B μ) :
    (brownianSupremaLaw B μ).map (fun p => p.1 + p.2) =
      μ.map (fun ω => realDriftedSum (B · ω) 1) := by
  exact AEMeasurable.map_map_of_aemeasurable (by fun_prop) (aemeasurable_brownianSupremumPair hB)

theorem jointCDFENN_brownianSupremaLaw (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    jointCDFENN (brownianSupremaLaw B μ) a b = ENNReal.ofReal (wedgeSeries a b) := by
  rw [jointCDFENN, brownianSupremaLaw,
    Measure.map_apply_of_aemeasurable (aemeasurable_brownianSupremumPair hB)
      (measurableSet_jointCDF a b)]
  exact measure_realDriftedSup_joint_le hB ha hb

/-- The integrated Doob series is the true positive-part expectation of the dependent sum. -/
theorem integral_wedgeSeries_eq_positivePartMean (hB : IsBrownianReal B μ)
    {s : ℝ} (hs : 0 < s) :
    (∫ a in 0..s, wedgeSeries a (s - a)) =
      positivePartMean (μ.map (fun ω => realDriftedSum (B · ω) 1)) s := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (brownianSupremaLaw B μ) :=
    Measure.isFiniteMeasure_map μ (brownianSupremumPair B)
  rw [← brownianSupremaLaw_map_sum hB,
    ← integral_jointCDF_triangle (brownianSupremaLaw B μ) (brownianSupremaLaw_nonneg_ae hB) hs.le]
  simp only [intervalIntegral.integral_of_le hs.le, ← integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro a ha
  dsimp only
  rw [jointCDFENN_brownianSupremaLaw hB ha.1 (sub_pos.mpr ha.2)]
  have hn : 0 ≤ wedgeSeries a (s - a) := by
    rw [← measureReal_wedgeSurvival_eq_wedgeSeries hB ha.1 (sub_pos.mpr ha.2)]
    exact measureReal_nonneg
  exact (ENNReal.toReal_ofReal hn).symm

end BrownianAffine
