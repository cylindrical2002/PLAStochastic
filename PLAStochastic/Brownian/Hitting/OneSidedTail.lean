import PLAStochastic.Brownian.Hitting.TwoBarrierExit
import PLAStochastic.Brownian.Hitting.DriftedSuprema

/-!
# One-sided drifted Brownian tails

The lower barrier is sent to minus infinity in the actual two-barrier exit
identity. No law of a Brownian maximum is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

omit [MeasurableSpace Ω] in
theorem openExitTime_lower_of_no_upper_crossing {X : ℝ≥0 → Ω → ℝ} {a b : ℝ} {ω : Ω}
    (hX : Continuous (X · ω)) (h0 : X 0 ω ∈ Icc (-b) a)
    (hne : {t : ℝ≥0 | X t ω ∈ driftBarrierSet a b}.Nonempty)
    (hno : ¬ ∃ t, a < X t ω) :
    X (openExitTime X (driftBarrierSet a b) ω) ω = -b := by
  have hcl : openExitTime X (driftBarrierSet a b) ω ∈
      closure {t : ℝ≥0 | X t ω ∈ driftBarrierSet a b} :=
    (isGLB_csInf hne ⟨0, fun _ _ => bot_le⟩).mem_closure hne
  have hlo : X (openExitTime X (driftBarrierSet a b) ω) ω ≤ -b := by
    apply closure_minimal (t := (fun t => X t ω) ⁻¹' Iic (-b)) ?_
      (isClosed_Iic.preimage hX) hcl
    intro t ht
    rcases ht with hl | hu
    · exact (show X t ω < -b from hl).le
    · exact (hno ⟨t, hu⟩).elim
  have hbnd := openExitTime_boundary hX h0 hne
  rcases hbnd with h | h
  · exact le_antisymm hlo ((h0.1.trans h0.2).trans_eq h.symm)
  · exact h

omit [MeasurableSpace Ω] in
theorem openExitTime_upper_eventually {X : ℝ≥0 → Ω → ℝ} {a : ℝ} {ω : Ω}
    (hX : Continuous (X · ω)) (hzero : X 0 ω = 0) (ha : 0 ≤ a)
    (hyes : ∃ t, a < X t ω) :
    ∀ᶠ n : ℕ in atTop,
      X (openExitTime X (driftBarrierSet a (n + 1)) ω) ω = a := by
  obtain ⟨t, ht⟩ := hyes
  obtain ⟨L, hL⟩ := isCompact_Icc.bddBelow_image (K := Icc (0 : ℝ≥0) t) hX.continuousOn
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (eventually_gt_atTop (-L))] with n hn
  have hne : {s : ℝ≥0 | X s ω ∈ driftBarrierSet a (n + 1)}.Nonempty :=
    ⟨t, Or.inr ht⟩
  have h0 : X 0 ω ∈ Icc (-(n + 1 : ℝ)) a := by
    rw [hzero]
    exact ⟨neg_nonpos.mpr (by positivity), ha⟩
  rcases openExitTime_boundary hX h0 hne with h | h
  · exact h
  · have hρ : openExitTime X (driftBarrierSet a (n + 1)) ω ≤ t :=
      csInf_le ⟨0, fun _ _ => bot_le⟩ (Or.inr ht)
    have hmin := hL (mem_image_of_mem (fun s => X s ω) ⟨bot_le, hρ⟩)
    rw [h] at hmin
    linarith

/-- The affine rescaling of the two possible exponential exit values. -/
def normalizedBrownianExit (B : ℝ≥0 → Ω → ℝ) (a b : ℝ) (ω : Ω) : ℝ :=
  (actualBrownianExponential B
    (openExitTime (actualBrownianDrift B) (driftBarrierSet a b) ω) ω - Real.exp (-2 * b)) /
    (Real.exp (2 * a) - Real.exp (-2 * b))

variable {B : ℝ≥0 → Ω → ℝ}

theorem integrable_normalizedBrownianExit (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : Integrable (normalizedBrownianExit B a b) μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  exact ((integral_actualBrownianExponential_exit hB ha hb).1.sub (integrable_const _)).div_const _

theorem integral_normalizedBrownianExit (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ ω, normalizedBrownianExit B a b ω ∂μ) =
      (1 - Real.exp (-2 * b)) / (Real.exp (2 * a) - Real.exp (-2 * b)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hi := integral_actualBrownianExponential_exit hB ha hb
  simp only [normalizedBrownianExit, integral_div]
  rw [integral_sub hi.1 (integrable_const _), hi.2]
  simp

omit [MeasurableSpace Ω] in
theorem normalizedBrownianExit_of_boundary {a b : ℝ} {ω : Ω}
    (hab : -b < a)
    (h : actualBrownianDrift B
      (openExitTime (actualBrownianDrift B) (driftBarrierSet a b) ω) ω = a ∨
      actualBrownianDrift B
      (openExitTime (actualBrownianDrift B) (driftBarrierSet a b) ω) ω = -b) :
    normalizedBrownianExit B a b ω = 1 ∨ normalizedBrownianExit B a b ω = 0 := by
  have hne : Real.exp (2 * a) - Real.exp (-2 * b) ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by linarith)))
  have hid (t : ℝ≥0) : actualBrownianExponential B t ω =
      Real.exp (2 * actualBrownianDrift B t ω) := by
    dsimp only [actualBrownianExponential, actualBrownianDrift]
    congr 1
    ring
  rcases h with h | h
  · left
    simp only [normalizedBrownianExit, hid, h, div_self hne]
  · right
    simp only [normalizedBrownianExit, hid, h, mul_neg, neg_mul, sub_self, zero_div]

theorem normalizedBrownianExit_zero_one_ae (hB : IsBrownianReal B μ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    ∀ᵐ ω ∂μ, normalizedBrownianExit B a b ω = 1 ∨ normalizedBrownianExit B a b ω = 0 := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, brownianDrift_exit_nonempty_ae hB a b]
    with ω hω hzero hne
  have hc : Continuous (actualBrownianDrift B · ω) := hω.sub continuous_subtype_val
  have h0 : actualBrownianDrift B 0 ω ∈ Icc (-b) a := by
    simpa only [actualBrownianDrift, hzero, NNReal.coe_zero, sub_zero, mem_Icc]
      using And.intro (neg_nonpos.mpr hb.le) ha
  exact normalizedBrownianExit_of_boundary (by linarith) (openExitTime_boundary hc h0 hne)

theorem normalizedBrownianExit_tendsto_crossing_indicator (hB : IsBrownianReal B μ)
    {a : ℝ} (ha : 0 ≤ a) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => normalizedBrownianExit B a (n + 1) ω) atTop
      (𝓝 ({ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω}.indicator (fun _ => (1 : ℝ)) ω)) := by
  classical
  have hneall : ∀ᵐ ω ∂μ, ∀ n : ℕ,
      {t : ℝ≥0 | actualBrownianDrift B t ω ∈ driftBarrierSet a (n + 1)}.Nonempty :=
    ae_all_iff.mpr (fun n => brownianDrift_exit_nonempty_ae hB a (n + 1))
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero, hneall] with ω hω hzero hne
  have hc : Continuous (actualBrownianDrift B · ω) := hω.sub continuous_subtype_val
  have h0 : actualBrownianDrift B 0 ω = 0 := by
    simp only [actualBrownianDrift, hzero, NNReal.coe_zero, sub_zero]
  have hid (t : ℝ≥0) : actualBrownianExponential B t ω =
      Real.exp (2 * actualBrownianDrift B t ω) := by
    dsimp only [actualBrownianExponential, actualBrownianDrift]
    congr 1
    ring
  by_cases hyes : ∃ t : ℝ≥0, a < actualBrownianDrift B t ω
  · rw [indicator_of_mem (show ω ∈ {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω} from hyes)]
    apply tendsto_const_nhds.congr'
    filter_upwards [openExitTime_upper_eventually hc h0 ha hyes] with n hn
    have hd : Real.exp (2 * a) - Real.exp (-2 * (n + 1)) ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt (Real.exp_lt_exp.mpr (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith)))
    simp only [normalizedBrownianExit, hid, hn, div_self hd]
  · rw [indicator_of_notMem (show ω ∉ {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω} from hyes)]
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall (fun n => by
      have hz : actualBrownianDrift B 0 ω ∈ Icc (-(n + 1 : ℝ)) a := by
        rw [h0]
        exact ⟨neg_nonpos.mpr (by positivity), ha⟩
      have hl := openExitTime_lower_of_no_upper_crossing hc hz (hne n) hyes
      simp only [normalizedBrownianExit, hid, hl, mul_neg, neg_mul, sub_self, zero_div])

omit [MeasurableSpace Ω] in
theorem driftedSup_gt_iff_crossing {a : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ENNReal.ofReal a < driftedSup (B · ω) 1 ↔ ∃ t : ℝ≥0, a < actualBrownianDrift B t ω := by
  simp only [driftedSup, lt_iSup_iff, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha,
    actualBrownianDrift, one_mul]

theorem nullMeasurableSet_brownian_drift_crossing (hB : IsBrownianReal B μ)
    {a : ℝ} (ha : 0 ≤ a) :
    NullMeasurableSet {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω} μ := by
  have heq : {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω} =
      (fun ω => driftedSup (B · ω) 1) ⁻¹' Ioi (ENNReal.ofReal a) := by
    ext ω
    exact (driftedSup_gt_iff_crossing ha ω).symm
  rw [heq]
  exact (aemeasurable_driftedPair hB 1).fst.nullMeasurableSet_preimage measurableSet_Ioi

/-- The actual one-sided drifted Brownian supremum has exponential tail. -/
theorem measureReal_brownian_drift_crossing (hB : IsBrownianReal B μ)
    {a : ℝ} (ha : 0 ≤ a) :
    μ.real {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω} = Real.exp (-2 * a) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let F : ℕ → Ω → ℝ := fun n => normalizedBrownianExit B a (n + 1)
  let s := {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω}
  have hF (n : ℕ) : Integrable (F n) μ := integrable_normalizedBrownianExit hB ha (by positivity)
  have hbound (n : ℕ) : ∀ᵐ ω ∂μ, ‖F n ω‖ ≤ (1 : ℝ) := by
    filter_upwards [normalizedBrownianExit_zero_one_ae hB ha (by positivity : 0 < (n : ℝ) + 1)]
      with ω hω
    rcases hω with h | h <;> simp only [F, h, norm_one, norm_zero, le_refl, zero_le_one]
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun n => (hF n).aestronglyMeasurable) (integrable_const _) hbound
    (normalizedBrownianExit_tendsto_crossing_indicator hB ha)
  have hind : (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real s := by
    rw [integral_indicator₀ (nullMeasurableSet_brownian_drift_crossing hB ha)]
    simp [s]
  change Tendsto (fun n => ∫ ω, F n ω ∂μ) atTop (𝓝 (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ)) at hconv
  rw [hind] at hconv
  have hexp : Tendsto (fun n : ℕ => Real.exp (-2 * ((n : ℝ) + 1))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    exact Tendsto.const_mul_atTop_of_neg (by norm_num : (-2 : ℝ) < 0) hn
  have hratio := ((tendsto_const_nhds (x := (1 : ℝ))).sub hexp).div (tendsto_const_nhds.sub hexp)
    (show Real.exp (2 * a) - 0 ≠ 0 by simp)
  have hformula : (fun n => ∫ ω, F n ω ∂μ) =
      fun n : ℕ => (1 - Real.exp (-2 * ((n : ℝ) + 1))) /
        (Real.exp (2 * a) - Real.exp (-2 * ((n : ℝ) + 1))) := by
    funext n
    exact integral_normalizedBrownianExit hB ha (by positivity)
  rw [hformula] at hconv
  have hh := tendsto_nhds_unique hconv hratio
  simpa only [sub_zero, one_div, ← Real.exp_neg, neg_mul] using hh

theorem measure_brownian_drift_crossing (hB : IsBrownianReal B μ)
    {a : ℝ} (ha : 0 ≤ a) :
    μ {ω | ∃ t : ℝ≥0, a < actualBrownianDrift B t ω} = ENNReal.ofReal (Real.exp (-2 * a)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  rw [← measureReal_brownian_drift_crossing hB ha, measureReal_def, ENNReal.ofReal_toReal]
  exact measure_ne_top _ _

theorem measure_driftedSup_gt (hB : IsBrownianReal B μ)
    {a : ℝ} (ha : 0 ≤ a) :
    μ {ω | ENNReal.ofReal a < driftedSup (B · ω) 1} = ENNReal.ofReal (Real.exp (-2 * a)) := by
  simpa only [driftedSup_gt_iff_crossing ha] using measure_brownian_drift_crossing hB ha

end BrownianAffine
