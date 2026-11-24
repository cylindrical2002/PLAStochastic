import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.CutoffAssembly

/-!
# The continuous central cutoff for the leading coefficient

The limiting reward is zero on the negative half-line and has a jump at the
origin.  This file records the concrete continuous approximation used to
bridge that jump.  It is intentionally independent of the filter-wise
assembly: the latter only needs the continuity, boundedness, and the central
set-integral estimates proved here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The positive-side ramp and its continuous cutoff -/

/-- A linear ramp from zero at the origin to one at `δ`. -/
def positiveMarginRamp (δ r : ℝ) : ℝ := KernelLimit.clamp01 (r / δ)

theorem positiveMarginRamp_continuous (δ : ℝ) :
    Continuous (positiveMarginRamp δ) := by
  unfold positiveMarginRamp
  exact KernelLimit.continuous_clamp01.comp (continuous_id.div_const δ)

theorem positiveMarginRamp_nonneg (δ r : ℝ) :
    0 ≤ positiveMarginRamp δ r :=
  KernelLimit.clamp01_nonneg _

theorem positiveMarginRamp_le_one (δ r : ℝ) :
    positiveMarginRamp δ r ≤ 1 :=
  KernelLimit.clamp01_le_one _

theorem positiveMarginRamp_eq_zero_of_nonpos
    {δ r : ℝ} (hδ : 0 < δ) (hr : r ≤ 0) :
    positiveMarginRamp δ r = 0 := by
  unfold positiveMarginRamp
  apply KernelLimit.clamp01_eq_zero
  exact div_nonpos_of_nonpos_of_nonneg hr hδ.le

theorem positiveMarginRamp_eq_one_of_ge
    {δ r : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) :
    positiveMarginRamp δ r = 1 := by
  unfold positiveMarginRamp
  apply KernelLimit.clamp01_eq_one
  apply (le_div_iff₀ hδ).2
  simpa using hr

/-- The bounded continuous test function obtained by ramping the positive
renewal reward and applying the far-tail cutoff. -/
def marginLeadingReward_continuousCutoff
    (X : ℕ → Ω → ℝ) (μ : Measure Ω) (δ C r : ℝ) : ℝ :=
  4 * gaussianRenewalPotential X μ (max r 0) *
    positiveMarginRamp δ r * compactCutoff C r

theorem marginLeadingReward_continuousCutoff_continuous
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (δ C : ℝ) :
    Continuous (marginLeadingReward_continuousCutoff X μ δ C) := by
  have hmax : Continuous (fun r : ℝ => max r 0) :=
    continuous_id.max continuous_const
  have hV : Continuous (fun r : ℝ =>
      gaussianRenewalPotential X μ (max r 0)) := by
    have hcomp := (gaussianRenewalPotential_continuousOn hX hi hG).comp_continuous
      hmax (fun r => le_max_right r 0)
    simpa [Function.comp_def] using hcomp
  have hr : Continuous (positiveMarginRamp δ) :=
    positiveMarginRamp_continuous δ
  have hc : Continuous (compactCutoff C) := compactCutoff_continuous C
  exact ((continuous_const.mul hV).mul hr).mul hc

theorem marginLeadingReward_continuousCutoff_nonneg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ C r : ℝ} :
    0 ≤ marginLeadingReward_continuousCutoff X μ δ C r := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hV : 0 ≤ gaussianRenewalPotential X μ (max r 0) :=
    gaussianRenewalPotential_nonneg_of_nonneg hX hi hG (le_max_right r 0)
  have h4V : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
    mul_nonneg (by norm_num) hV
  have hr : 0 ≤ positiveMarginRamp δ r := positiveMarginRamp_nonneg _ _
  have hc : 0 ≤ compactCutoff C r := compactCutoff_nonneg _ _
  exact mul_nonneg (mul_nonneg h4V hr) hc

/-!
The cutoff has a bound independent of the ramp width.  This is useful both
for finite stationary laws and for the limiting law, since a finite measure
integrates every bounded continuous function.
-/
theorem marginLeadingReward_continuousCutoff_bounded
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ C : ℝ} (hC : 0 ≤ C) :
    ∃ B : ℝ, ∀ r : ℝ,
      |marginLeadingReward_continuousCutoff X μ δ C r| ≤ B := by
  let M : ℝ := gaussianExcessExpMomentBound 2
  refine ⟨4 * (C + 1 + M), ?_⟩
  intro r
  by_cases hr : |r| ≤ C + 1
  · have hrmax : max r 0 ≤ C + 1 := by
      apply max_le
      · exact (le_abs_self r).trans hr
      · linarith
    have hV := gaussianRenewalPotential_le_linear_of_nonneg hX hi hG
      (w := max r 0) (le_max_right r 0)
    have hM : 0 ≤ M := by
      dsimp [M]
      exact (gaussianExcessExpMomentBound_pos 2).le
    have hV' : gaussianRenewalPotential X μ (max r 0) ≤ C + 1 + M := by
      dsimp [M] at hV ⊢
      linarith
    have hVnon : 0 ≤ gaussianRenewalPotential X μ (max r 0) :=
      gaussianRenewalPotential_nonneg_of_nonneg hX hi hG (le_max_right r 0)
    have hRnon : 0 ≤ positiveMarginRamp δ r := positiveMarginRamp_nonneg _ _
    have hRle : positiveMarginRamp δ r ≤ 1 := positiveMarginRamp_le_one _ _
    have hCnon : 0 ≤ compactCutoff C r := compactCutoff_nonneg _ _
    have hCle : compactCutoff C r ≤ 1 := compactCutoff_le_one _ _
    have hprod : 0 ≤ marginLeadingReward_continuousCutoff X μ δ C r :=
      marginLeadingReward_continuousCutoff_nonneg hX hi hG
    rw [abs_of_nonneg hprod]
    calc
      marginLeadingReward_continuousCutoff X μ δ C r ≤
          4 * gaussianRenewalPotential X μ (max r 0) *
            positiveMarginRamp δ r := by
        unfold marginLeadingReward_continuousCutoff
        have hleft : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) *
            positiveMarginRamp δ r :=
          mul_nonneg (mul_nonneg (by norm_num) hVnon) hRnon
        calc
          4 * gaussianRenewalPotential X μ (max r 0) *
              positiveMarginRamp δ r * compactCutoff C r ≤
              4 * gaussianRenewalPotential X μ (max r 0) *
                positiveMarginRamp δ r * 1 :=
            mul_le_mul_of_nonneg_left hCle hleft
          _ = 4 * gaussianRenewalPotential X μ (max r 0) *
              positiveMarginRamp δ r := by ring
      _ ≤ 4 * gaussianRenewalPotential X μ (max r 0) := by
        have hleft : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
          mul_nonneg (by norm_num) hVnon
        calc
          4 * gaussianRenewalPotential X μ (max r 0) *
              positiveMarginRamp δ r ≤
              4 * gaussianRenewalPotential X μ (max r 0) * 1 :=
            mul_le_mul_of_nonneg_left hRle hleft
          _ = 4 * gaussianRenewalPotential X μ (max r 0) := by ring
      _ ≤ 4 * (C + 1 + M) := by
        have := mul_le_mul_of_nonneg_left hV' (by norm_num : (0 : ℝ) ≤ 4)
        linarith
  · have hzero : compactCutoff C r = 0 :=
      compactCutoff_eq_zero (le_of_not_ge hr)
    have hM : 0 ≤ M := by
      dsimp [M]
      exact (gaussianExcessExpMomentBound_pos 2).le
    have hB : 0 ≤ 4 * (C + 1 + M) := by positivity
    rw [show marginLeadingReward_continuousCutoff X μ δ C r = 0 by
      simp [marginLeadingReward_continuousCutoff, hzero]]
    simpa using hB

theorem marginLeadingReward_continuousCutoff_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν] {δ C : ℝ} (hC : 0 ≤ C) :
    Integrable (marginLeadingReward_continuousCutoff X μ δ C) ν := by
  obtain ⟨B, hB⟩ := marginLeadingReward_continuousCutoff_bounded
    hX hi hG hC
  exact Integrable.of_bound
    (marginLeadingReward_continuousCutoff_continuous hX hi hG δ C).aestronglyMeasurable
    B (ae_of_all _ (fun r => by
      rw [Real.norm_eq_abs]
      exact hB r))

/-! ### Pointwise comparison with the discontinuous limiting reward -/

theorem marginLeadingReward_continuousCutoff_eq_zero_of_nonpos
    (_hX : ∀ n, Measurable (X n)) (_hi : iIndepFun X μ)
    (_hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ C r : ℝ} (hδ : 0 < δ) (hr : r ≤ 0) :
    marginLeadingReward_continuousCutoff X μ δ C r = 0 := by
  have hRzero : positiveMarginRamp δ r = 0 :=
    positiveMarginRamp_eq_zero_of_nonpos hδ hr
  simp [marginLeadingReward_continuousCutoff, hRzero]

theorem marginLeadingReward_continuousCutoff_eq_marginLeadingReward
    (_hX : ∀ n, Measurable (X n)) (_hi : iIndepFun X μ)
    (_hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ C r : ℝ} (hδ : 0 < δ) (hrδ : δ ≤ r) (hrC : |r| ≤ C) :
    marginLeadingReward_continuousCutoff X μ δ C r =
      marginLeadingReward X μ r := by
  have hrpos : 0 < r := lt_of_lt_of_le hδ hrδ
  have hRone : positiveMarginRamp δ r = 1 :=
    positiveMarginRamp_eq_one_of_ge hδ hrδ
  simp only [marginLeadingReward_continuousCutoff, hRone,
    compactCutoff_eq_one hrC]
  unfold marginLeadingReward
  rw [if_pos hrpos, max_eq_left hrpos.le]
  ring

theorem marginLeadingReward_continuousCutoff_le_marginLeadingReward
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ C r : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) (hr : 0 ≤ r) :
    marginLeadingReward_continuousCutoff X μ δ C r ≤
      marginLeadingReward X μ r := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hV : 0 ≤ gaussianRenewalPotential X μ (max r 0) :=
    gaussianRenewalPotential_nonneg_of_nonneg hX hi hG (le_max_right r 0)
  have h4V : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
    mul_nonneg (by norm_num) hV
  have hR : 0 ≤ positiveMarginRamp δ r := positiveMarginRamp_nonneg _ _
  have hRle : positiveMarginRamp δ r ≤ 1 := positiveMarginRamp_le_one _ _
  have hcut : 0 ≤ compactCutoff C r := compactCutoff_nonneg _ _
  have hcutle : compactCutoff C r ≤ 1 := compactCutoff_le_one _ _
  by_cases hrpos : 0 < r
  · have hmargin : marginLeadingReward X μ r =
        4 * gaussianRenewalPotential X μ (max r 0) := by
      unfold marginLeadingReward
      rw [if_pos hrpos, max_eq_left hrpos.le]
    rw [hmargin]
    unfold marginLeadingReward_continuousCutoff
    calc
      4 * gaussianRenewalPotential X μ (max r 0) * positiveMarginRamp δ r *
          compactCutoff C r ≤
        4 * gaussianRenewalPotential X μ (max r 0) * positiveMarginRamp δ r := by
          simpa [mul_one] using
            (mul_le_mul_of_nonneg_left hcutle (mul_nonneg h4V hR))
      _ ≤ 4 * gaussianRenewalPotential X μ (max r 0) := by
          simpa [mul_one] using (mul_le_mul_of_nonneg_left hRle h4V)
  · have hr0 : r = 0 := le_antisymm (le_of_not_gt hrpos) hr
    subst r
    have hRzero : positiveMarginRamp δ 0 = 0 :=
      positiveMarginRamp_eq_zero_of_nonpos hδ le_rfl
    simp [marginLeadingReward_continuousCutoff, marginLeadingReward, hRzero]

/-! ### A generic central set-integral comparison -/

theorem abs_setIntegral_sub_le_of_nonneg_bounds
    {ν : Measure ℝ} [IsFiniteMeasure ν] {S : Set ℝ} {u v : ℝ → ℝ}
    (hS : MeasurableSet S) (hu : IntegrableOn u S ν)
    (hv : IntegrableOn v S ν)
    (hu0 : ∀ x ∈ S, 0 ≤ u x) (hv0 : ∀ x ∈ S, 0 ≤ v x)
    {A B : ℝ} (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (huA : ∀ x ∈ S, u x ≤ A) (hvB : ∀ x ∈ S, v x ≤ B) :
    |(∫ x in S, u x ∂ν) - ∫ x in S, v x ∂ν| ≤
      (A + B) * ν.real S := by
  have hconstA0 : Integrable (fun _ : ℝ => A) ν := integrable_const A
  have hconstB0 : Integrable (fun _ : ℝ => B) ν := integrable_const B
  have hconstA : IntegrableOn (fun _ : ℝ => A) S ν := hconstA0.integrableOn
  have hconstB : IntegrableOn (fun _ : ℝ => B) S ν := hconstB0.integrableOn
  have hu_le : (∫ x in S, u x ∂ν) ≤ A * ν.real S := by
    calc
      (∫ x in S, u x ∂ν) ≤ ∫ _x in S, A ∂ν :=
        setIntegral_mono_on hu hconstA hS huA
      _ = A * ν.real S := by rw [setIntegral_const, smul_eq_mul]; ring
  have hv_le : (∫ x in S, v x ∂ν) ≤ B * ν.real S := by
    calc
      (∫ x in S, v x ∂ν) ≤ ∫ _x in S, B ∂ν :=
        setIntegral_mono_on hv hconstB hS hvB
      _ = B * ν.real S := by rw [setIntegral_const, smul_eq_mul]; ring
  have hu_nonneg : 0 ≤ ∫ x in S, u x ∂ν := setIntegral_nonneg hS hu0
  have hv_nonneg : 0 ≤ ∫ x in S, v x ∂ν := setIntegral_nonneg hS hv0
  have hmass : 0 ≤ ν.real S := ENNReal.toReal_nonneg
  calc
    |(∫ x in S, u x ∂ν) - ∫ x in S, v x ∂ν| ≤
        (∫ x in S, u x ∂ν) + ∫ x in S, v x ∂ν := by
      simpa [abs_of_nonneg hu_nonneg, abs_of_nonneg hv_nonneg] using
        (abs_sub (∫ x in S, u x ∂ν) (∫ x in S, v x ∂ν))
    _ ≤ A * ν.real S + B * ν.real S :=
      add_le_add hu_le hv_le
    _ = (A + B) * ν.real S := by ring

/-! ### Central errors for the finite and limiting laws -/

theorem marginLeadingReward_continuousCutoff_central_error_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    |(∫ r in Icc (-δ) δ, marginLeadingReward X μ r ∂ν) -
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r ∂ν| ≤
      4 * (gaussianExcessExpMomentBound 2 + δ) * ν.real (Icc (-δ) δ) := by
  have hf := marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  have hg := marginLeadingReward_continuousCutoff_integrable
    (ν := ν) (δ := δ) (C := C) hX hi hG hC
  have hfi : IntegrableOn (marginLeadingReward X μ) (Icc (-δ) δ) ν := hf.integrableOn
  have hgi : IntegrableOn
      (marginLeadingReward_continuousCutoff X μ δ C) (Icc (-δ) δ) ν :=
    hg.integrableOn
  have hzero := marginLeadingReward_setIntegral_zero_le hX hi hG hνabs hδ.le
  have hle : ∀ r ∈ Icc (-δ) δ,
      marginLeadingReward_continuousCutoff X μ δ C r ≤
        marginLeadingReward X μ r := by
    intro r hr
    by_cases hr0 : 0 ≤ r
    · exact marginLeadingReward_continuousCutoff_le_marginLeadingReward
        hX hi hG hδ hC hr0
    · have hr' : r ≤ 0 := le_of_not_ge hr0
      rw [marginLeadingReward_continuousCutoff_eq_zero_of_nonpos hX hi hG
        hδ hr']
      exact marginLeadingReward_nonneg hX hi hG
  have hnon : 0 ≤
      (∫ r in Icc (-δ) δ, marginLeadingReward X μ r ∂ν) -
        ∫ r in Icc (-δ) δ,
          marginLeadingReward_continuousCutoff X μ δ C r ∂ν := by
    exact sub_nonneg.mpr (setIntegral_mono_on hgi hfi measurableSet_Icc hle)
  rw [abs_of_nonneg hnon]
  have hcut0 : 0 ≤
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r ∂ν :=
    setIntegral_nonneg measurableSet_Icc (fun r hr =>
      marginLeadingReward_continuousCutoff_nonneg hX hi hG)
  linarith

theorem normalizedFrozenMean_continuousCutoff_central_error_le
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ C : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 < δ) (hC : 0 ≤ C)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    |(∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r
          ∂(stationaryMarginLaw E π)) -
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r
          ∂(stationaryMarginLaw E π)| ≤
      (2 * frozenUniformMeanConstant * (1 + δ) +
        4 * (gaussianExcessExpMomentBound 2 + δ)) *
      (stationaryMarginLaw E π).real (Icc (-δ) δ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let : IsProbabilityMeasure ν := isProbabilityMeasure_stationaryMarginLaw E π
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hf := normalizedFrozenMean_integrable_stationaryMarginLaw
    (X := X) (μ := μ) hX hi hG hE hπ
  have hg := marginLeadingReward_continuousCutoff_integrable
    (X := X) (μ := μ) (ν := ν) (δ := δ) (C := C) hX hi hG hC
  have hfi : IntegrableOn (normalizedFrozenMean X μ E) (Icc (-δ) δ) ν :=
    hf.integrableOn
  have hgi : IntegrableOn
      (marginLeadingReward_continuousCutoff X μ δ C) (Icc (-δ) δ) ν :=
    hg.integrableOn
  have hA : 0 ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
    have : 0 ≤ (1 + δ : ℝ) := by linarith
    positivity [frozenUniformMeanConstant_pos]
  have hB : 0 ≤ 4 * (gaussianExcessExpMomentBound 2 + δ) := by
    have hM : 0 ≤ gaussianExcessExpMomentBound 2 :=
      (gaussianExcessExpMomentBound_pos 2).le
    positivity
  have hu0 : ∀ r ∈ Icc (-δ) δ,
      0 ≤ normalizedFrozenMean X μ E r := by
    intro r hr
    have hE1 : 1 ≤ E := by
      have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
      exact hexp.trans ((le_max_right _ _).trans ((le_max_left _ _).trans hE))
    exact normalizedFrozenMean_nonneg hX hi hG hE1
  have hv0 : ∀ r ∈ Icc (-δ) δ,
      0 ≤ marginLeadingReward_continuousCutoff X μ δ C r := by
    intro r hr
    exact marginLeadingReward_continuousCutoff_nonneg hX hi hG
  have huA : ∀ r ∈ Icc (-δ) δ,
      normalizedFrozenMean X μ E r ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
    intro r hr
    have hm := normalizedFrozenMean_le_linear (X := X) (μ := μ)
      (r := r) hX hi hG hEone
    have hmax : max r 0 ≤ δ := max_le hr.2 hδ.le
    calc
      normalizedFrozenMean X μ E r ≤
          2 * frozenUniformMeanConstant * (1 + max r 0) := hm
      _ ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
        have hc : 0 ≤ 2 * frozenUniformMeanConstant := by
          positivity [frozenUniformMeanConstant_pos]
        exact mul_le_mul_of_nonneg_left (by linarith) hc
  have huB : ∀ r ∈ Icc (-δ) δ,
      marginLeadingReward_continuousCutoff X μ δ C r ≤
        4 * (gaussianExcessExpMomentBound 2 + δ) := by
    intro r hr
    have hM : 0 ≤ gaussianExcessExpMomentBound 2 :=
      (gaussianExcessExpMomentBound_pos 2).le
    have hmax : max r 0 ≤ δ := max_le hr.2 hδ.le
    have hV := gaussianRenewalPotential_le_linear_of_nonneg
      (X := X) (μ := μ) hX hi hG (w := max r 0) (le_max_right r 0)
    have hV' : gaussianRenewalPotential X μ (max r 0) ≤
        gaussianExcessExpMomentBound 2 + δ := by linarith
    have hR : positiveMarginRamp δ r ≤ 1 := positiveMarginRamp_le_one _ _
    have hcut : compactCutoff C r ≤ 1 := compactCutoff_le_one _ _
    have hR0 : 0 ≤ positiveMarginRamp δ r := positiveMarginRamp_nonneg _ _
    have hV0 : 0 ≤ gaussianRenewalPotential X μ (max r 0) :=
      gaussianRenewalPotential_nonneg_of_nonneg hX hi hG (le_max_right r 0)
    have h4V : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
      mul_nonneg (by norm_num) hV0
    calc
      marginLeadingReward_continuousCutoff X μ δ C r ≤
          4 * gaussianRenewalPotential X μ (max r 0) := by
        unfold marginLeadingReward_continuousCutoff
        calc
          4 * gaussianRenewalPotential X μ (max r 0) *
              positiveMarginRamp δ r * compactCutoff C r ≤
              4 * gaussianRenewalPotential X μ (max r 0) *
                positiveMarginRamp δ r :=
            (by simpa [mul_one] using
              (mul_le_mul_of_nonneg_left hcut (mul_nonneg h4V hR0)))
          _ ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
            (by simpa [mul_one] using (mul_le_mul_of_nonneg_left hR h4V))
      _ ≤ 4 * (gaussianExcessExpMomentBound 2 + δ) :=
        mul_le_mul_of_nonneg_left hV' (by norm_num)
  exact abs_setIntegral_sub_le_of_nonneg_bounds measurableSet_Icc hfi hgi
    hu0 hv0 hA hB huA huB

/-! The preceding finite-law estimate has a completely uniform `O(δ)` form
when `δ ≤ 1`; this is the form most convenient for a filter argument. -/

theorem normalizedFrozenMean_continuousCutoff_central_error_le_linear
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ C : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    |(∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r
          ∂(stationaryMarginLaw E π)) -
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r
          ∂(stationaryMarginLaw E π)| ≤
      (2 * frozenUniformMeanConstant * (1 + δ) +
        4 * (gaussianExcessExpMomentBound 2 + δ)) *
        (2 * nativeFirstMarginConcentrationConstant 1 * δ) := by
  have hmain := normalizedFrozenMean_continuousCutoff_central_error_le
    (X := X) (μ := μ) hX hi hG hE hδ hC hπ
  have hmass := stationaryMarginLaw_zero_interval_le_linear
    (X := X) (μ := μ) hX hi hG hE hδ.le _hδ1 hπ
  have hcoef : 0 ≤
      2 * frozenUniformMeanConstant * (1 + δ) +
        4 * (gaussianExcessExpMomentBound 2 + δ) := by
    have hF : 0 ≤ frozenUniformMeanConstant :=
      frozenUniformMeanConstant_pos.le
    have hM : 0 ≤ gaussianExcessExpMomentBound 2 :=
      (gaussianExcessExpMomentBound_pos 2).le
    positivity
  exact hmain.trans (mul_le_mul_of_nonneg_left hmass hcoef)

/-! The same estimate after multiplying the finite reward by the compact
cutoff.  This is the convenient form for the four-region lemma: the positive
far transition has then been removed exactly, while the central error only
gains the (small) finite central mass. -/

theorem normalizedFrozenMean_compactCutoff_continuousCutoff_central_error_le
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ C : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 < δ) (_hδ1 : δ ≤ 1)
    (hC : 0 ≤ C) {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    |(∫ r in Icc (-δ) δ,
        normalizedFrozenMean X μ E r * compactCutoff C r
          ∂(stationaryMarginLaw E π)) -
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r
          ∂(stationaryMarginLaw E π)| ≤
      (2 * frozenUniformMeanConstant * (1 + δ) +
        4 * (gaussianExcessExpMomentBound 2 + δ)) *
        (stationaryMarginLaw E π).real (Icc (-δ) δ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let : IsProbabilityMeasure ν := isProbabilityMeasure_stationaryMarginLaw E π
  have hf := normalizedFrozenMean_integrable_stationaryMarginLaw
    (X := X) (μ := μ) hX hi hG hE hπ
  have hfc : Integrable
      (fun r => normalizedFrozenMean X μ E r * compactCutoff C r) ν := by
    exact hf.mul_bdd (μ := ν) (compactCutoff_continuous C).measurable.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg C r)]
        exact compactCutoff_le_one C r))
  have hg := marginLeadingReward_continuousCutoff_integrable
    (X := X) (μ := μ) (ν := ν) (δ := δ) (C := C) hX hi hG hC
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hA : 0 ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
    have : 0 ≤ (1 + δ : ℝ) := by linarith
    positivity [frozenUniformMeanConstant_pos]
  have hB : 0 ≤ 4 * (gaussianExcessExpMomentBound 2 + δ) := by
    have hM : 0 ≤ gaussianExcessExpMomentBound 2 :=
      (gaussianExcessExpMomentBound_pos 2).le
    positivity
  have hu0 : ∀ r ∈ Icc (-δ) δ,
      0 ≤ normalizedFrozenMean X μ E r * compactCutoff C r := by
    intro r hr
    exact mul_nonneg
      (normalizedFrozenMean_nonneg (r := r) hX hi hG
        (by have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
            exact hexp.trans ((le_max_right _ _).trans
              ((le_max_left _ _).trans hE))))
      (compactCutoff_nonneg C r)
  have hv0 : ∀ r ∈ Icc (-δ) δ,
      0 ≤ marginLeadingReward_continuousCutoff X μ δ C r := by
    intro r hr
    exact marginLeadingReward_continuousCutoff_nonneg hX hi hG
  have huA : ∀ r ∈ Icc (-δ) δ,
      normalizedFrozenMean X μ E r * compactCutoff C r ≤
        2 * frozenUniformMeanConstant * (1 + δ) := by
    intro r hr
    have hm := normalizedFrozenMean_le_linear (X := X) (μ := μ)
      (r := r) hX hi hG hEone
    have hmax : max r 0 ≤ δ := max_le hr.2 hδ.le
    have hcut : compactCutoff C r ≤ 1 := compactCutoff_le_one C r
    have hnon : 0 ≤ normalizedFrozenMean X μ E r :=
      normalizedFrozenMean_nonneg (r := r) hX hi hG
        (by have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
            exact hexp.trans ((le_max_right _ _).trans
              ((le_max_left _ _).trans hE)))
    have hbase : normalizedFrozenMean X μ E r ≤
        2 * frozenUniformMeanConstant * (1 + δ) := by
      calc
        normalizedFrozenMean X μ E r ≤
            2 * frozenUniformMeanConstant * (1 + max r 0) := hm
        _ ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
          have hc : 0 ≤ 2 * frozenUniformMeanConstant := by
            positivity [frozenUniformMeanConstant_pos]
          exact mul_le_mul_of_nonneg_left (by linarith) hc
    exact (mul_le_of_le_one_right hnon hcut).trans hbase
  have hvB : ∀ r ∈ Icc (-δ) δ,
      marginLeadingReward_continuousCutoff X μ δ C r ≤
        4 * (gaussianExcessExpMomentBound 2 + δ) := by
    intro r hr
    have hM : 0 ≤ gaussianExcessExpMomentBound 2 :=
      (gaussianExcessExpMomentBound_pos 2).le
    have hmax : max r 0 ≤ δ := max_le hr.2 hδ.le
    have hV := gaussianRenewalPotential_le_linear_of_nonneg
      (X := X) (μ := μ) hX hi hG (w := max r 0) (le_max_right r 0)
    have hV' : gaussianRenewalPotential X μ (max r 0) ≤
        gaussianExcessExpMomentBound 2 + δ := by linarith
    have hR : positiveMarginRamp δ r ≤ 1 := positiveMarginRamp_le_one _ _
    have hcut : compactCutoff C r ≤ 1 := compactCutoff_le_one _ _
    have hR0 : 0 ≤ positiveMarginRamp δ r := positiveMarginRamp_nonneg _ _
    have hV0 : 0 ≤ gaussianRenewalPotential X μ (max r 0) :=
      gaussianRenewalPotential_nonneg_of_nonneg hX hi hG (le_max_right r 0)
    have h4V : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
      mul_nonneg (by norm_num) hV0
    calc
      marginLeadingReward_continuousCutoff X μ δ C r ≤
          4 * gaussianRenewalPotential X μ (max r 0) := by
        unfold marginLeadingReward_continuousCutoff
        calc
          4 * gaussianRenewalPotential X μ (max r 0) *
              positiveMarginRamp δ r * compactCutoff C r ≤
              4 * gaussianRenewalPotential X μ (max r 0) *
                positiveMarginRamp δ r := by
            simpa [mul_one] using
              (mul_le_mul_of_nonneg_left hcut (mul_nonneg h4V hR0))
          _ ≤ 4 * gaussianRenewalPotential X μ (max r 0) := by
            simpa [mul_one] using (mul_le_mul_of_nonneg_left hR h4V)
      _ ≤ 4 * (gaussianExcessExpMomentBound 2 + δ) :=
        mul_le_mul_of_nonneg_left hV' (by norm_num)
  exact abs_setIntegral_sub_le_of_nonneg_bounds measurableSet_Icc
    hfc.integrableOn hg.integrableOn hu0 hv0 hA hB huA hvB

/-! On the limiting side the continuous ramp is pointwise below the compactly
cutoff reward.  Consequently no second copy of the central bound is needed. -/

theorem marginLeadingReward_compactCutoff_continuousCutoff_central_error_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {δ C : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C) :
    |(∫ r in Icc (-δ) δ,
        marginLeadingReward X μ r * compactCutoff C r ∂ν) -
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r ∂ν| ≤
      4 * (gaussianExcessExpMomentBound 2 + δ) *
        ν.real (Icc (-δ) δ) := by
  have hf := marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  have hfc : Integrable
      (fun r => marginLeadingReward X μ r * compactCutoff C r) ν := by
    exact hf.mul_bdd (μ := ν) (compactCutoff_continuous C).measurable.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (compactCutoff_nonneg C r)]
        exact compactCutoff_le_one C r))
  have hg := marginLeadingReward_continuousCutoff_integrable
    (X := X) (μ := μ) (ν := ν) (δ := δ) (C := C) hX hi hG hC
  have hfc0 : ∀ r ∈ Icc (-δ) δ,
      0 ≤ marginLeadingReward X μ r * compactCutoff C r := by
    intro r hr
    exact mul_nonneg (marginLeadingReward_nonneg hX hi hG)
      (compactCutoff_nonneg C r)
  have hg0 : ∀ r ∈ Icc (-δ) δ,
      0 ≤ marginLeadingReward_continuousCutoff X μ δ C r := by
    intro r hr
    exact marginLeadingReward_continuousCutoff_nonneg hX hi hG
  have hle : ∀ r ∈ Icc (-δ) δ,
      marginLeadingReward_continuousCutoff X μ δ C r ≤
        marginLeadingReward X μ r * compactCutoff C r := by
    intro r hr
    by_cases hrpos : 0 < r
    · let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      have hV : 0 ≤ gaussianRenewalPotential X μ (max r 0) :=
        gaussianRenewalPotential_nonneg_of_nonneg hX hi hG (le_max_right r 0)
      have h4V : 0 ≤ 4 * gaussianRenewalPotential X μ (max r 0) :=
        mul_nonneg (by norm_num) hV
      have hR : positiveMarginRamp δ r ≤ 1 := positiveMarginRamp_le_one _ _
      have hcut : 0 ≤ compactCutoff C r := compactCutoff_nonneg _ _
      have hmargin : marginLeadingReward X μ r =
          4 * gaussianRenewalPotential X μ (max r 0) := by
        unfold marginLeadingReward
        rw [if_pos hrpos, max_eq_left hrpos.le]
      rw [hmargin]
      unfold marginLeadingReward_continuousCutoff
      simpa [mul_one] using
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hR h4V) hcut)
    · have hr0 : r ≤ 0 := le_of_not_gt hrpos
      rw [marginLeadingReward_continuousCutoff_eq_zero_of_nonpos
        hX hi hG hδ hr0]
      exact mul_nonneg (marginLeadingReward_nonneg hX hi hG)
        (compactCutoff_nonneg C r)
  have hfiS : IntegrableOn
      (fun r => marginLeadingReward X μ r * compactCutoff C r)
      (Icc (-δ) δ) ν := hfc.integrableOn
  have hgiS : IntegrableOn
      (marginLeadingReward_continuousCutoff X μ δ C)
      (Icc (-δ) δ) ν := hg.integrableOn
  have hnon : 0 ≤
      (∫ r in Icc (-δ) δ,
        marginLeadingReward X μ r * compactCutoff C r ∂ν) -
      ∫ r in Icc (-δ) δ,
        marginLeadingReward_continuousCutoff X μ δ C r ∂ν := by
    exact sub_nonneg.mpr (setIntegral_mono_on hgiS hfiS
      measurableSet_Icc hle)
  rw [abs_of_nonneg hnon]
  have hfc_le : ∀ r ∈ Icc (-δ) δ,
      marginLeadingReward X μ r * compactCutoff C r ≤
        marginLeadingReward X μ r := by
    intro r hr
    exact mul_le_of_le_one_right (marginLeadingReward_nonneg hX hi hG)
      (compactCutoff_le_one C r)
  have hfin := marginLeadingReward_setIntegral_zero_le hX hi hG hνabs hδ.le
  have hmono := setIntegral_mono_on hfiS hf.integrableOn measurableSet_Icc hfc_le
  have hfc_nonneg : 0 ≤ ∫ r in Icc (-δ) δ,
      marginLeadingReward X μ r * compactCutoff C r ∂ν :=
    setIntegral_nonneg measurableSet_Icc hfc0
  have hg_nonneg : 0 ≤ ∫ r in Icc (-δ) δ,
      marginLeadingReward_continuousCutoff X μ δ C r ∂ν :=
    setIntegral_nonneg measurableSet_Icc hg0
  linarith

/-! The negative compact-side contribution vanishes along any budget filter
tending to infinity.  This packages the logarithmic carry estimate in a form
that can be inserted directly into the final integral-transfer triangle. -/

theorem tendsto_normalizedFrozenMean_setIntegral_Iio_neg
    [SFinite μ] {ι : Type*} {l : Filter ι} [l.NeBot]
    {budget : ι → ℝ} {πs : ι → Measure ℝ}
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1)
    (hbudget : ∀ i, stationaryScaleThreshold ≤ budget i)
    (hbudget_top : Tendsto budget l atTop)
    (hπP : ∀ i, IsProbabilityMeasure (πs i))
    (hπinv : ∀ i,
      (nativeRestartKernel X μ (budget i)).Invariant (πs i))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto
      (fun i => ∫ r in Iio (-δ), normalizedFrozenMean X μ (budget i) r
        ∂(stationaryMarginLaw (budget i) (πs i))) l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let A : ℝ := frozenNegativeCarryLogConstant *
    (1 + max (Real.log (1 / δ)) 0)
  have hA : 0 ≤ A := by
    dsimp [A]
    have hmax : 0 ≤ max (Real.log (1 / δ)) 0 := le_max_right _ _
    positivity [frozenNegativeCarryLogConstant_pos]
  have hlog : Tendsto (fun i => Real.log (budget i)) l atTop :=
    Real.tendsto_log_atTop.comp hbudget_top
  have hevlog : ∀ᶠ i in l, A / ε < Real.log (budget i) :=
    hlog.eventually (eventually_gt_atTop (A / ε))
  filter_upwards [hevlog] with i hi_log
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let νi : Measure ℝ := stationaryMarginLaw (budget i) (πs i)
  let : IsProbabilityMeasure (πs i) := hπP i
  let : IsProbabilityMeasure νi :=
    isProbabilityMeasure_stationaryMarginLaw (budget i) (πs i)
  have hbound := normalizedFrozenMean_setIntegral_Iio_neg_log_le
    (X := X) (μ := μ) hX hi hG (E := budget i) (δ := δ)
    (hbudget i) hδ (hπinv i)
  have hnon : 0 ≤ ∫ r in Iio (-δ),
      normalizedFrozenMean X μ (budget i) r ∂νi :=
    setIntegral_nonneg measurableSet_Iio (fun r hr =>
      normalizedFrozenMean_nonneg hX hi hG (by
        have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
        exact hexp.trans ((le_max_right _ _).trans
          ((le_max_left _ _).trans (hbudget i)))))
  have hlogpos : 0 < Real.log (budget i) := by
    apply Real.log_pos
    exact lt_of_lt_of_le (by norm_num) ((le_max_right _ _).trans
      ((le_max_left _ _).trans (hbudget i)))
  have hA_lt : A < ε * Real.log (budget i) := by
    have := (div_lt_iff₀ hε).mp hi_log
    simpa [mul_comm] using this
  have hratio : A / Real.log (budget i) < ε :=
    (div_lt_iff₀ hlogpos).2 (by simpa [mul_comm] using hA_lt)
  have hbound' :
      ∫ r in Iio (-δ), normalizedFrozenMean X μ (budget i) r ∂νi < ε := by
    have hAeq : A / Real.log (budget i) =
        frozenNegativeCarryLogConstant / Real.log (budget i) *
          (1 + max (Real.log (1 / δ)) 0) := by
      dsimp [A]
      ring
    have hboundA :
        ∫ r in Iio (-δ), normalizedFrozenMean X μ (budget i) r ∂νi ≤
          A / Real.log (budget i) := by
      rw [hAeq]
      simpa [νi] using hbound
    exact hboundA.trans_lt hratio
  simpa [νi, Real.dist_eq, abs_of_nonneg hnon] using hbound'

/-! A purely measure-theoretic four-piece decomposition.  It is the small
algebraic bridge used by the final transfer: the central piece is supplied as
a set-integral comparison, the negative and positive-far pieces are tails,
and a uniform pointwise error controls the positive compact annulus. -/

theorem abs_integral_sub_le_of_central_negative_positive_far
    {ν : Measure ℝ} [IsFiniteMeasure ν] {f g : ℝ → ℝ}
    {δ R : ℝ} (hδ : 0 ≤ δ) (hδR : δ ≤ R)
    (hf : Integrable f ν) (hg : Integrable g ν)
    (hf0 : ∀ x, 0 ≤ f x)
    {ec en ep ef : ℝ} (_hec : 0 ≤ ec) (_hen : 0 ≤ en)
    (_hep : 0 ≤ ep) (_hef : 0 ≤ ef)
    (hcentral :
      |(∫ x in Icc (-δ) δ, f x ∂ν) -
        ∫ x in Icc (-δ) δ, g x ∂ν| ≤ ec)
    (hneg_zero : ∀ x ∈ Iio (-δ), g x = 0)
    (hneg : ∫ x in Iio (-δ), f x ∂ν ≤ en)
    (hpos : ∀ x ∈ Ioc δ R, |f x - g x| ≤ ep)
    (hfar_zero : ∀ x ∈ Ioi R, g x = 0)
    (hfar : ∫ x in Ioi R, f x ∂ν ≤ ef) :
    |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| ≤
      ec + en + ep * ν.real (Ioc δ R) + ef := by
  let d : ℝ → ℝ := fun x => f x - g x
  have hd : Integrable d ν := hf.sub hg
  have hneg_set : MeasurableSet (Iio (-δ)) := measurableSet_Iio
  have hcent_set : MeasurableSet (Icc (-δ) δ) := measurableSet_Icc
  have hpos_set : MeasurableSet (Ioc δ R) := measurableSet_Ioc
  have hfar_set : MeasurableSet (Ioi R) := measurableSet_Ioi
  have hneg_cent : Disjoint (Iio (-δ)) (Icc (-δ) δ) := by
    refine Set.disjoint_left.2 ?_
    intro x hxneg hxcent
    exact (not_le_of_gt hxneg) (mem_Icc.mp hxcent).1
  have hcent_pos : Disjoint (Icc (-δ) δ) (Ioc δ R) := by
    refine Set.disjoint_left.2 ?_
    intro x hxcent hxpos
    exact (not_lt_of_ge (mem_Icc.mp hxcent).2) (mem_Ioc.mp hxpos).1
  have hneg_pos : Disjoint (Iio (-δ)) (Ioc δ R) := by
    refine Set.disjoint_left.2 ?_
    intro x hxneg hxpos
    change x < -δ at hxneg
    have hxp := (mem_Ioc.mp hxpos).1
    linarith [hδ, hxp]
  have hnegcent_pos :
      Disjoint ((Iio (-δ)) ∪ (Icc (-δ) δ)) (Ioc δ R) :=
    Set.disjoint_union_left.2 ⟨hneg_pos, hcent_pos⟩
  have hleft_far :
      Disjoint (((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R)) (Ioi R) := by
    have hleft :
        ((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R) = Iic R := by
      rw [Iio_union_Icc_eq_Iic (by linarith [hδ]),
        Iic_union_Ioc_eq_Iic hδR]
    rw [hleft]
    exact Set.disjoint_left.2 (fun x hxleft hxfar => by
      change x ≤ R at hxleft
      change R < x at hxfar
      exact (not_lt_of_ge hxleft) hxfar)
  have hcover :
      (((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R)) ∪ (Ioi R) =
        (Set.univ : Set ℝ) := by
    rw [show ((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R) = Iic R by
      rw [Iio_union_Icc_eq_Iic (by linarith [hδ]),
        Iic_union_Ioc_eq_Iic hδR], Iic_union_Ioi]
  have hsum_neg_cent :
      ∫ x in (Iio (-δ)) ∪ (Icc (-δ) δ), d x ∂ν =
        ∫ x in Iio (-δ), d x ∂ν +
          ∫ x in Icc (-δ) δ, d x ∂ν :=
    setIntegral_union hneg_cent hcent_set hd.integrableOn hd.integrableOn
  have hsum_neg_cent_pos :
      ∫ x in ((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R), d x ∂ν =
        (∫ x in Iio (-δ), d x ∂ν +
          ∫ x in Icc (-δ) δ, d x ∂ν) +
          ∫ x in Ioc δ R, d x ∂ν := by
    rw [setIntegral_union hnegcent_pos hpos_set hd.integrableOn hd.integrableOn,
      hsum_neg_cent]
  have hsum_all :
      ∫ x, d x ∂ν =
        (∫ x in Iio (-δ), d x ∂ν +
          ∫ x in Icc (-δ) δ, d x ∂ν) +
          ∫ x in Ioc δ R, d x ∂ν +
          ∫ x in Ioi R, d x ∂ν := by
    calc
      ∫ x, d x ∂ν = ∫ x in (Set.univ : Set ℝ), d x ∂ν := by simp
      _ = ∫ x in
          (((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R)) ∪ (Ioi R),
          d x ∂ν := by rw [hcover]
      _ = ∫ x in ((Iio (-δ)) ∪ (Icc (-δ) δ)) ∪ (Ioc δ R), d x ∂ν +
          ∫ x in Ioi R, d x ∂ν :=
        setIntegral_union hleft_far hfar_set hd.integrableOn hd.integrableOn
      _ = _ := by rw [hsum_neg_cent_pos]
  have hcentral_d :
      |∫ x in Icc (-δ) δ, d x ∂ν| ≤ ec := by
    have hsub := integral_sub (μ := ν.restrict (Icc (-δ) δ))
      hf.integrableOn hg.integrableOn
    have heq :
        ∫ x in Icc (-δ) δ, d x ∂ν =
          (∫ x in Icc (-δ) δ, f x ∂ν) -
            ∫ x in Icc (-δ) δ, g x ∂ν := by
      simpa [d] using hsub
    rw [heq]
    exact hcentral
  have hneg_d :
      |∫ x in Iio (-δ), d x ∂ν| ≤ en := by
    have heq : ∫ x in Iio (-δ), d x ∂ν =
        ∫ x in Iio (-δ), f x ∂ν := by
      apply setIntegral_congr_fun hneg_set
      intro x hx
      simp [d, hneg_zero x hx]
    rw [heq, abs_of_nonneg (setIntegral_nonneg hneg_set
      (fun x hx => hf0 x))]
    exact hneg
  have hfar_d :
      |∫ x in Ioi R, d x ∂ν| ≤ ef := by
    have heq : ∫ x in Ioi R, d x ∂ν =
        ∫ x in Ioi R, f x ∂ν := by
      apply setIntegral_congr_fun hfar_set
      intro x hx
      simp [d, hfar_zero x hx]
    rw [heq, abs_of_nonneg (setIntegral_nonneg hfar_set
      (fun x hx => hf0 x))]
    exact hfar
  have hpos_d :
      |∫ x in Ioc δ R, d x ∂ν| ≤ ep * ν.real (Ioc δ R) := by
    have hdp : Integrable d (ν.restrict (Ioc δ R)) := hd.integrableOn
    have hconst : Integrable (fun _ : ℝ => ep)
        (ν.restrict (Ioc δ R)) := integrable_const ep
    have hpoint : ∀ᵐ x ∂(ν.restrict (Ioc δ R)), |d x| ≤ ep := by
      rw [ae_restrict_iff' hpos_set]
      exact Eventually.of_forall (fun x hx => hpos x hx)
    have hmono : ∫ x, |d x| ∂(ν.restrict (Ioc δ R)) ≤
        ∫ _x, ep ∂(ν.restrict (Ioc δ R)) :=
      integral_mono_ae hdp.norm hconst hpoint
    have habs : |∫ x, d x ∂(ν.restrict (Ioc δ R))| ≤
        ∫ x, |d x| ∂(ν.restrict (Ioc δ R)) :=
      abs_integral_le_integral_abs
    have hconst' : ∫ _x in Ioc δ R, ep ∂ν =
        ep * ν.real (Ioc δ R) := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    calc
      |∫ x in Ioc δ R, d x ∂ν| ≤
          ∫ x, |d x| ∂(ν.restrict (Ioc δ R)) := by simpa using habs
      _ ≤ ∫ _x, ep ∂(ν.restrict (Ioc δ R)) := hmono
      _ = ep * ν.real (Ioc δ R) := hconst'
  have hglobal :
      |(∫ x, f x ∂ν) - ∫ x, g x ∂ν| =
        |(∫ x in Iio (-δ), d x ∂ν +
          ∫ x in Icc (-δ) δ, d x ∂ν) +
          ∫ x in Ioc δ R, d x ∂ν +
          ∫ x in Ioi R, d x ∂ν| := by
    rw [← integral_sub hf hg, hsum_all]
  rw [hglobal]
  calc
    _ ≤ |(∫ x in Iio (-δ), d x ∂ν +
          ∫ x in Icc (-δ) δ, d x ∂ν) +
          ∫ x in Ioc δ R, d x ∂ν| +
          |∫ x in Ioi R, d x ∂ν| := abs_add_le _ _
    _ ≤ (|∫ x in Iio (-δ), d x ∂ν| +
          |∫ x in Icc (-δ) δ, d x ∂ν|) +
          |∫ x in Ioc δ R, d x ∂ν| +
          |∫ x in Ioi R, d x ∂ν| := by
      have htri := abs_add_le
        (∫ x in Iio (-δ), d x ∂ν)
        (∫ x in Icc (-δ) δ, d x ∂ν)
      have htri' :
          |(∫ x in Iio (-δ), d x ∂ν +
            ∫ x in Icc (-δ) δ, d x ∂ν) +
              ∫ x in Ioc δ R, d x ∂ν| ≤
            (|∫ x in Iio (-δ), d x ∂ν| +
              |∫ x in Icc (-δ) δ, d x ∂ν|) +
              |∫ x in Ioc δ R, d x ∂ν| := by
        calc
          _ ≤ |∫ x in Iio (-δ), d x ∂ν +
              ∫ x in Icc (-δ) δ, d x ∂ν| +
              |∫ x in Ioc δ R, d x ∂ν| := abs_add_le _ _
          _ ≤ _ := add_le_add_left htri _
      exact add_le_add_left htri' _
    _ ≤ en + ec + ep * ν.real (Ioc δ R) + ef := by
      linarith [hneg_d, hcentral_d, hpos_d, hfar_d]
    _ = ec + en + ep * ν.real (Ioc δ R) + ef := by ring


end LeadingCoefficient
end SwingRepair
