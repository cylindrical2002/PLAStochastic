import PLAStochastic.Swing.FrozenCarry.Path.SlopeLipschitz
import PLAStochastic.Swing.Gaussian.ZeroLadder.StrictLadderLaw

/-! # The limiting slope in the paper's sign convention

This is the actual supremum of the original walk, with the incoming margin
subtracted.  Reflection identifies it pathwise with the frozen-slope object;
all probabilistic properties are then derived from the original Gaussian
increment law.  No independent replacement slope is introduced.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*}

def swingLimitingSlope (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) : ℝ :=
  ⨆ n : ℕ, (cumulativeSamples X n ω-r)/((n : ℝ)+1)

theorem swingLimitingSlope_eq_frozen_reflection
    (X : ℕ → Ω → ℝ) (r : ℝ) (ω : Ω) :
    swingLimitingSlope X r ω =
      frozenSlopeMagnitude (fun n ω => -X n ω) r ω := by
  change sSup (range (fun n : ℕ => (cumulativeSamples X n ω-r)/((n : ℝ)+1))) = _
  unfold frozenSlopeMagnitude
  congr 1
  apply congrArg Set.range
  funext n
  simp only [frozenUpperSlope, cumulativeSamples, Finset.sum_neg_distrib]
  ring

variable [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem swingLimitingSlope_joint_measurable (hX : ∀ n, Measurable (X n)) :
    Measurable (fun p : ℝ × Ω => swingLimitingSlope X p.1 p.2) := by
  have hs : ∀ n, Measurable (cumulativeSamples X n) := by
    intro n
    exact Finset.measurable_sum _ (fun k _ => hX k)
  unfold swingLimitingSlope
  exact Measurable.iSup (fun n =>
    (((hs n).comp measurable_snd).sub measurable_fst).div_const _)

theorem swingLimitingSlope_measurable (hX : ∀ n, Measurable (X n)) (r : ℝ) :
    Measurable (swingLimitingSlope X r) :=
  (swingLimitingSlope_joint_measurable hX).comp measurable_prodMk_left

theorem swingLimitingSlope_regular_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, LipschitzWith 1 (fun r => swingLimitingSlope X r ω) ∧
      Antitone (fun r => swingLimitingSlope X r ω) := by
  have hnegX : ∀ n, Measurable (fun ω => -X n ω) := fun n => (hX n).neg
  have hnegi : iIndepFun (fun n ω => -X n ω) μ :=
    hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hnegG := gaussianIncrement_reflected_law hX hG
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hnegX hnegi hnegG 0] with ω hω
  simpa only [swingLimitingSlope_eq_frozen_reflection] using
    And.intro (frozenSlopeMagnitude_lipschitz_of_sublinear hω)
      (frozenSlopeMagnitude_antitone_of_sublinear hω)

theorem swingLimitingSlope_pos_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    ∀ᵐ ω ∂μ, 0 < swingLimitingSlope X r ω := by
  have hnegX : ∀ n, Measurable (fun ω => -X n ω) := fun n => (hX n).neg
  have hnegi : iIndepFun (fun n ω => -X n ω) μ :=
    hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hnegG := gaussianIncrement_reflected_law hX hG
  filter_upwards [frozenSlopeMagnitude_positive_ae hnegX hnegi hnegG r] with ω hω
  simpa only [swingLimitingSlope_eq_frozen_reflection] using hω.2

/-- One full-measure event gives positivity and regularity for every real
incoming margin.  Positivity is first intersected over natural margins and
then extended to all real margins by antitonicity. -/
theorem swingLimitingSlope_all_margins_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, (∀ r : ℝ, 0 < swingLimitingSlope X r ω) ∧
      LipschitzWith 1 (fun r => swingLimitingSlope X r ω) ∧
      Antitone (fun r => swingLimitingSlope X r ω) := by
  have hn : ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < swingLimitingSlope X n ω :=
    ae_all_iff.mpr (fun n => swingLimitingSlope_pos_ae hX hi hG n)
  filter_upwards [hn, swingLimitingSlope_regular_ae hX hi hG] with ω hpos hreg
  refine ⟨?_, hreg⟩
  intro r
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact (hpos n).trans_le (hreg.2 hn.le)

/-- The actual slope distribution for a fixed incoming margin. -/
def swingLimitingSlopeLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (r : ℝ) : Measure ℝ :=
  μ.map (swingLimitingSlope X r)

theorem swingLimitingSlopeLaw_isProbabilityMeasure [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (r : ℝ) :
    IsProbabilityMeasure (swingLimitingSlopeLaw X μ r) :=
  Measure.isProbabilityMeasure_map (swingLimitingSlope_measurable hX r).aemeasurable

/-- The actual slope map sends a coupled pair of margins to a pair of slopes
whose expected Lipschitz test discrepancy is at most the original distance.
This is the concrete slope part of the later two-stage kernel coupling. -/
theorem swingLimitingSlope_integral_test_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzWith L f) (r c : ℝ)
    (hr : Integrable (fun ω => f (swingLimitingSlope X r ω)) μ)
    (hc : Integrable (fun ω => f (swingLimitingSlope X c ω)) μ) :
    |(∫ ω, f (swingLimitingSlope X r ω) ∂μ) -
      (∫ ω, f (swingLimitingSlope X c ω) ∂μ)| ≤ (L : ℝ) * |r-c| := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  rw [← integral_sub hr hc]
  have hbound : ∀ᵐ ω ∂μ,
      |f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω)| ≤
        (L : ℝ) * |r-c| := by
    filter_upwards [swingLimitingSlope_regular_ae hX hi hG] with ω hω
    have hfirst := hf.dist_le_mul (swingLimitingSlope X r ω) (swingLimitingSlope X c ω)
    have hsecond := hω.1.dist_le_mul r c
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hfirst hsecond
    exact hfirst.trans (mul_le_mul_of_nonneg_left hsecond L.coe_nonneg)
  calc
    |∫ ω, f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω) ∂μ| ≤
        ∫ ω, |f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω)| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => f (swingLimitingSlope X r ω) - f (swingLimitingSlope X c ω))
    _ ≤ ∫ _ω, (L : ℝ) * |r-c| ∂μ :=
      integral_mono_ae (hr.sub hc).norm (integrable_const _) hbound
    _ = (L : ℝ) * |r-c| := by simp

end SwingRepair
