import PLAStochastic.Brownian.Hitting.WedgeStopping
import PLAStochastic.Brownian.Hitting.DriftedSuprema

/-!
# The measurable wedge survival event and its cutoff alternatives
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def wedgeSurvival (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) : Set Ω :=
  {ω | ∀ t : ℝ≥0, wedgeDeviation B a b t ω ≤ 0}

omit [MeasurableSpace Ω] in
theorem wedgeSurvival_iff_driftedSup_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ω : Ω) :
    ω ∈ wedgeSurvival B a b ↔
      driftedSup (B · ω) 1 ≤ ENNReal.ofReal a ∧
      driftedSup (fun t => -B t ω) 1 ≤ ENNReal.ofReal b := by
  simp only [wedgeSurvival, mem_ofPred_eq, wedgeDeviation, max_le_iff, sub_nonpos,
    driftedSup, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff ha, ENNReal.ofReal_le_ofReal_iff hb,
    one_mul, forall_and]

theorem nullMeasurableSet_wedgeSurvival (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : NullMeasurableSet (wedgeSurvival B a b) μ := by
  have heq : wedgeSurvival B a b =
      (fun ω => driftedPair (B · ω) 1) ⁻¹' Iic (ENNReal.ofReal a, ENNReal.ofReal b) := by
    ext ω
    exact wedgeSurvival_iff_driftedSup_bounds ha hb ω
  rw [heq]
  exact (aemeasurable_driftedPair hB 1).nullMeasurableSet_preimage measurableSet_Iic

omit [MeasurableSpace Ω] in
theorem boundedWedgeExit_eq_cutoff_of_survival {a b : ℝ} {ω : Ω}
    (hω : ω ∈ wedgeSurvival B a b) (T : ℝ≥0) : boundedWedgeExit B a b T ω = T := by
  have heq : {t : ℝ≥0 | t ≤ T ∧ wedgeDeviation B a b t ω ∈ Ioi 0} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact (not_lt_of_ge (hω t)) ht.2
  simp only [boundedWedgeExit, boundedOpenExitTime, heq, insert_empty_eq, csInf_singleton]

omit [MeasurableSpace Ω] in
theorem boundedWedgeExit_eventually_zero_coordinate {a b : ℝ} {ω : Ω}
    (hc : Continuous (B · ω)) (hzero : B 0 ω = 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hω : ω ∉ wedgeSurvival B a b) :
    ∀ᶠ H : ℕ in atTop,
      a + (boundedWedgeExit B a b H ω : ℝ) - B (boundedWedgeExit B a b H ω) ω = 0 ∨
        b + (boundedWedgeExit B a b H ω : ℝ) + B (boundedWedgeExit B a b H ω) ω = 0 := by
  have hne : {t : ℝ≥0 | wedgeDeviation B a b t ω ∈ Ioi 0}.Nonempty := by
    have hx : ∃ t : ℝ≥0, ¬ wedgeDeviation B a b t ω ≤ 0 := not_forall.mp hω
    obtain ⟨t, ht⟩ := hx
    exact ⟨t, lt_of_not_ge ht⟩
  have hn : Tendsto (fun H : ℕ => (H : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [boundedOpenExitTime_eventually_eq hne,
    hn.eventually (eventually_gt_atTop (openExitTime (wedgeDeviation B a b) (Ioi 0) ω))]
      with H heq hH
  apply boundedWedgeExit_zero_coordinate hc hzero ha hb
  exact heq.trans_lt hH

theorem brownian_wedge_coordinates_tendsto_atTop_ae (hB : IsBrownianReal B μ) (a b : ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun H : ℕ => a + (H : ℝ) - B H ω) atTop atTop ∧
      Tendsto (fun H : ℕ => b + (H : ℝ) + B H ω) atTop atTop := by
  have hn : Tendsto (fun H : ℕ => (H : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [brownian_drift_tendsto_atBot_ae hB (by norm_num : (0 : ℝ) < 1),
    brownian_drift_tendsto_atBot_ae hB.neg (by norm_num : (0 : ℝ) < 1)] with ω hp hm
  constructor
  · have ht := (tendsto_neg_atBot_atTop.comp hp).comp hn
    have hs := tendsto_atTop_add_const_left atTop a ht
    convert! hs using 1
    funext H
    simp only [Function.comp_def, one_mul, NNReal.coe_natCast]
    ring
  · have ht := (tendsto_neg_atBot_atTop.comp hm).comp hn
    have hs := tendsto_atTop_add_const_left atTop b ht
    convert! hs using 1
    funext H
    simp only [Function.comp_def, one_mul, NNReal.coe_natCast, Pi.neg_apply]
    ring

end BrownianAffine
