import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.IntegralPassage
import PLAStochastic.Swing.Restart.Chain.MarginAntiConcentration
import PLAStochastic.Swing.FrozenCarry.NegativeCarry.LogBound

/-!
# Concrete bounds for the final leading-coefficient passage

This file isolates the parts of the last integral transfer which are already
available from the actual Gaussian/frozen-prefix construction.  In particular,
the renewal potential has a linear bound, the frozen mean is measurable as a
function of the margin, and the compact-uniform limit can be composed with an
arbitrary budget filter tending to infinity.  Concrete zero-neighbourhood,
negative-margin, far-tail, and compact-cutoff bounds are recorded below; the
remaining central-cutoff and filter-wise assembly is kept explicit in the
final transfer theorem.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### Bounds for the true renewal potential -/

theorem gaussianRenewalPotential_nonneg_of_nonneg
    (_hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (_hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ gaussianRenewalPotential X μ w := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  unfold gaussianRenewalPotential
  have hnon : 0 ≤ ∫ ω, gaussianHalfLineOvershoot X w 0 ω ∂μ :=
    integral_nonneg (μ := μ) (f := fun ω => gaussianHalfLineOvershoot X w 0 ω)
      (fun ω => gaussianHalfLineOvershoot_nonneg X w 0 ω)
  exact add_nonneg hw hnon

theorem gaussianRenewalPotential_le_linear_of_nonneg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {w : ℝ} (hw : 0 ≤ w) :
    gaussianRenewalPotential X μ w ≤
      w + gaussianExcessExpMomentBound 2 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  unfold gaussianRenewalPotential
  have ho := gaussianHalfLineOvershoot_uniform_moments hX hi hG
    (x := w) (a := 0) hw (by norm_num)
  simpa [add_comm] using (add_le_add_left ho.1.2 w)

theorem marginLeadingReward_nonneg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} :
    0 ≤ marginLeadingReward X μ r := by
  unfold marginLeadingReward
  split_ifs with hr
  · have hv := gaussianRenewalPotential_nonneg_of_nonneg hX hi hG hr.le
    positivity
  · exact le_rfl

theorem marginLeadingReward_le_linear
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} :
    marginLeadingReward X μ r ≤
      4 * (max r 0 + gaussianExcessExpMomentBound 2) := by
  unfold marginLeadingReward
  split_ifs with hr
  · have hv := gaussianRenewalPotential_le_linear_of_nonneg hX hi hG hr.le
    simpa [max_eq_left hr.le] using
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 4))
  · have hzero : (0 : ℝ) ≤ max r 0 + gaussianExcessExpMomentBound 2 := by
      have hc := (gaussianExcessExpMomentBound_pos 2).le
      positivity
    positivity

/-! The nonnegativity statement is useful when applying a linear tail bound. -/

theorem normalizedFrozenMean_nonneg
    [IsFiniteMeasure μ] (_hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (_hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {E r : ℝ} (hE : 1 ≤ E) :
    0 ≤ normalizedFrozenMean X μ E r := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  unfold normalizedFrozenMean
  have hnum : 0 ≤ ∫ ω, frozenPrefixLengthReal X r E ω ∂μ := by
    apply integral_nonneg
    intro ω
    exact Nat.cast_nonneg _
  have hden : 0 ≤ E * Real.log E := by
    exact mul_nonneg (by linarith) (Real.log_nonneg hE)
  exact div_nonneg hnum hden

theorem normalizedFrozenMean_le_linear
    [IsProbabilityMeasure μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {E r : ℝ} (hE : Real.exp 1 ≤ E) :
    normalizedFrozenMean X μ E r ≤
      2 * frozenUniformMeanConstant * (1 + max r 0) := by
  have hE1 : 1 ≤ E := by
    have : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    exact this.trans hE
  unfold normalizedFrozenMean
  have hmean := frozenPrefixLength_uniform_mean_bound hX hi hG r hE1
  have h1exp : (1 : ℝ) < Real.exp 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hlog : 0 < Real.log E := Real.log_pos (lt_of_lt_of_le h1exp hE)
  have hratio : Real.log (Real.exp 1 * E) / Real.log E ≤ 2 := by
    rw [Real.log_mul (Real.exp_pos _).ne' (by linarith : E ≠ 0), Real.log_exp]
    have hlogE : 1 ≤ Real.log E :=
      (Real.le_log_iff_exp_le (by positivity)).mpr hE
    apply (div_le_iff₀ hlog).mpr
    nlinarith
  have hnum_nonneg : 0 ≤ ∫ ω, frozenPrefixLengthReal X r E ω ∂μ := by
    apply integral_nonneg
    intro ω
    exact Nat.cast_nonneg _
  have hden : 0 < E * Real.log E := mul_pos (by positivity) hlog
  have hleft : normalizedFrozenMean X μ E r ≤
      frozenUniformMeanConstant * (1 + max r 0) *
        (Real.log (Real.exp 1 * E) / Real.log E) := by
    apply (div_le_iff₀ hden).mpr
    calc
      (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤
          frozenUniformMeanConstant * E * (1 + max r 0) *
            Real.log (Real.exp 1 * E) := hmean
      _ = (frozenUniformMeanConstant * (1 + max r 0) *
          (Real.log (Real.exp 1 * E) / Real.log E)) * (E * Real.log E) := by
        field_simp
  calc
    normalizedFrozenMean X μ E r ≤
        frozenUniformMeanConstant * (1 + max r 0) *
          (Real.log (Real.exp 1 * E) / Real.log E) := hleft
    _ ≤ 2 * frozenUniformMeanConstant * (1 + max r 0) := by
      have hc : 0 ≤ frozenUniformMeanConstant * (1 + max r 0) := by
        positivity [frozenUniformMeanConstant_pos]
      nlinarith

/-! The negative compact side of the conditional-mean limit.  H.1 gives a
uniform `E (1 + log_+(1/c))` bound for a negative carry `-c`; on a compact
interval separated from zero the logarithmic factor is bounded, and division
by `E log E` therefore tends to zero uniformly. -/
theorem normalizedFrozenMean_negative_tendstoUniformlyOn
    [IsFiniteMeasure μ] (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ C : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) :
    TendstoUniformlyOn
      (fun (E r : ℝ) => normalizedFrozenMean X μ E r)
      (fun _r => 0) atTop (Icc (-C) (-δ)) := by
  let L : ℝ := max (Real.log (1/δ)) 0
  let A : ℝ := frozenNegativeCarryLogConstant * (1 + L)
  have hL : 0 ≤ L := le_max_right _ _
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg frozenNegativeCarryLogConstant_pos.le (by linarith)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hlog : ∀ᶠ E : ℝ in atTop, A / ε < Real.log E := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop (A / ε)] with E hE
    exact hE
  have hE16 : ∀ᶠ E : ℝ in atTop, 16 ≤ E := eventually_ge_atTop 16
  filter_upwards [hlog, hE16] with E hElog hE16
  intro r hr
  have hrc : δ ≤ -r := by
    have := (mem_Icc.mp hr).2
    linarith
  have hrcpos : 0 < -r := hδ.trans_le hrc
  have hcupper : 1 / (-r) ≤ 1 / δ := by
    exact one_div_le_one_div_of_le hδ hrc
  have hlogmono : Real.log (1 / (-r)) ≤ Real.log (1 / δ) :=
    Real.strictMonoOn_log.monotoneOn
      (show 1 / (-r) ∈ Set.Ioi (0 : ℝ) by
        change 0 < 1 / (-r); positivity)
      (show 1 / δ ∈ Set.Ioi (0 : ℝ) by
        change 0 < 1 / δ; positivity) hcupper
  have hmax : max (Real.log (1 / (-r))) 0 ≤ L := by
    exact max_le_max hlogmono (le_refl (0 : ℝ))
  have hmean := frozenPrefixLength_negative_mean_log_bound hX hi hG
    (c := -r) (E := E) hrcpos hE16
  have hrr : -(-r) = r := by ring
  rw [hrr] at hmean
  have hnum : (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤ E * A := by
    have hmean' : (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤
        frozenNegativeCarryLogConstant * E *
          (1 + max (Real.log (1 / (-r))) 0) := by
      exact hmean
    dsimp [A] at hA ⊢
    calc
      (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤
          frozenNegativeCarryLogConstant * E *
            (1 + max (Real.log (1 / (-r))) 0) := hmean'
      _ ≤ frozenNegativeCarryLogConstant * E * (1 + L) := by
        have hcoef : 0 ≤ frozenNegativeCarryLogConstant * E := by
          exact mul_nonneg frozenNegativeCarryLogConstant_pos.le (by linarith)
        exact mul_le_mul_of_nonneg_left (by linarith) hcoef
      _ = E * (frozenNegativeCarryLogConstant * (1 + L)) := by ring
  have hEpos : 0 < E := by linarith
  have hlogpos : 0 < Real.log E := by
    have : (1 : ℝ) < E := by linarith
    exact Real.log_pos this
  have hden : 0 < E * Real.log E := mul_pos hEpos hlogpos
  have hnon : 0 ≤ normalizedFrozenMean X μ E r :=
    normalizedFrozenMean_nonneg hX hi hG (by linarith)
  rw [dist_zero_left, Real.norm_eq_abs, abs_of_nonneg hnon]
  unfold normalizedFrozenMean
  apply (div_lt_iff₀ hden).2
  have htarget : A ≤ ε * Real.log E := by
    have hh : A < Real.log E * ε := (div_lt_iff₀ hε).mp hElog
    exact le_of_lt (by simpa [mul_comm] using hh)
  have hprod : E * A < E * (ε * Real.log E) :=
    have hh : A < Real.log E * ε := (div_lt_iff₀ hε).mp hElog
    mul_lt_mul_of_pos_left (by simpa [mul_comm] using hh) hEpos
  calc
    (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤ E * A := hnum
    _ < ε * (E * Real.log E) := by
      nlinarith [hprod]

/-! ### A reusable bounded-continuous cutoff transfer -/

/-- A continuous linear-growth function becomes bounded after multiplying by the
compact cutoff `1 - farCut C`.  This is the exact test function used in the
tail/compact decomposition of the final integral. -/
def compactCutoff (C : ℝ) (x : ℝ) : ℝ := 1 - KernelLimit.farCut C x

theorem compactCutoff_continuous (C : ℝ) : Continuous (compactCutoff C) := by
  unfold compactCutoff
  exact continuous_const.sub (KernelLimit.continuous_farCut C)

theorem compactCutoff_nonneg (C x : ℝ) : 0 ≤ compactCutoff C x := by
  unfold compactCutoff
  linarith [KernelLimit.farCut_le_one C x]

theorem compactCutoff_le_one (C x : ℝ) : compactCutoff C x ≤ 1 := by
  unfold compactCutoff
  linarith [KernelLimit.farCut_nonneg C x]

theorem compactCutoff_eq_one {C x : ℝ} (hx : |x| ≤ C) :
    compactCutoff C x = 1 := by
  unfold compactCutoff
  rw [KernelLimit.farCut_eq_zero hx]
  norm_num

theorem compactCutoff_eq_zero {C x : ℝ} (hx : C + 1 ≤ |x|) :
    compactCutoff C x = 0 := by
  unfold compactCutoff
  rw [KernelLimit.farCut_eq_one hx]
  norm_num

theorem continuous_linear_cutoff_bounded
    {f : ℝ → ℝ} (_hf : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hlin : ∀ x, |f x| ≤ A * (1 + |x|)) (C : ℝ) :
    ∃ B : ℝ, ∀ x, |f x * compactCutoff C x| ≤ B := by
  refine ⟨A * (1 + |C| + 1), ?_⟩
  intro x
  by_cases hx : |x| ≤ C + 1
  · have hcut : |compactCutoff C x| ≤ 1 := by
      rw [abs_of_nonneg (compactCutoff_nonneg C x)]
      exact compactCutoff_le_one C x
    have hcx : |x| ≤ |C| + 1 := by
      have hc : C + 1 ≤ |C| + 1 := by linarith [le_abs_self C]
      linarith
    calc
      |f x * compactCutoff C x| = |f x| * |compactCutoff C x| := abs_mul _ _
      _ ≤ |f x| := by
        calc
          |f x| * |compactCutoff C x| ≤ |f x| * 1 :=
            mul_le_mul_of_nonneg_left hcut (abs_nonneg _)
          _ = |f x| := by ring
      _ ≤ A * (1 + |x|) := hlin x
      _ ≤ A * (1 + |C| + 1) := by
        apply mul_le_mul_of_nonneg_left _ hA
        linarith
  · have hcut : compactCutoff C x = 0 := by
      apply compactCutoff_eq_zero
      exact le_of_not_ge hx
    calc
      |f x * compactCutoff C x| = 0 := by simp [hcut]
      _ ≤ A * (1 + |C| + 1) := by
        exact mul_nonneg hA (by positivity)

/-!
If the uncut integrands have a uniform linear tail estimate, the compact cutoff
is an explicit member of `IntegralTransferHypothesis`.  The two scalar tail
inequalities are deliberately parameters: they are exactly where the stationary
first-moment bound, the negative-margin estimate, and the zero-neighbourhood
estimate are inserted in the model proof.
-/
theorem integralTransfer_compact_cutoff
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    {fs : ι → ℝ → ℝ} {f : ℝ → ℝ}
    (hf : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hflin : ∀ x, |f x| ≤ A * (1 + |x|))
    (hcut_tail : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ,
      (∀ᶠ i in l, abs ((∫ x, fs i x ∂(νs i : Measure ℝ)) -
          ∫ x, f x * (1 - KernelLimit.farCut C x) ∂(νs i : Measure ℝ)) < ε) ∧
      abs ((∫ x, f x * (1 - KernelLimit.farCut C x) ∂(ν : Measure ℝ)) -
        ∫ x, f x ∂(ν : Measure ℝ)) < ε) :
    IntegralTransferHypothesis (l := l) (νs := νs) (ν := ν) fs f := by
  intro ε hε
  obtain ⟨C, hCs, hCl⟩ := hcut_tail (ε / 2) (by linarith)
  have hbound := continuous_linear_cutoff_bounded hf hA hflin C
  obtain ⟨B, hB⟩ := hbound
  refine ⟨fun x => f x * compactCutoff C x, B, ?_, hB, ?_, ?_⟩
  · exact hf.mul (compactCutoff_continuous C)
  · filter_upwards [hCs] with i hi
    have hi' : abs ((∫ x, fs i x ∂(νs i : Measure ℝ)) -
        ∫ x, f x * (1 - KernelLimit.farCut C x) ∂(νs i : Measure ℝ)) < ε / 2 := hi
    simpa [compactCutoff] using (lt_trans hi' (by linarith : ε / 2 < ε))
  · have hcl' : abs ((∫ x, f x * (1 - KernelLimit.farCut C x) ∂(ν : Measure ℝ)) -
        ∫ x, f x ∂(ν : Measure ℝ)) < ε / 2 := hCl
    have hcl'' : abs ((∫ x, f x ∂(ν : Measure ℝ)) -
        ∫ x, f x * (1 - KernelLimit.farCut C x) ∂(ν : Measure ℝ)) < ε / 2 := by
      simpa [abs_sub_comm] using hcl'
    simpa [compactCutoff] using (lt_trans hcl'' (by linarith : ε / 2 < ε))

/-!
The one-step anti-concentration estimate survives stationarization.  This is
the concrete zero-neighbourhood input needed by the final cutoff argument:
the current margin law is the output law by invariance, and the latter has the
uniform interval bound from `NativeGeneralAntiConcentration`.
-/
theorem stationaryMarginLaw_interval_antiConcentration [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : 1 ≤ 2*E) {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π)
    {B p q : ℝ} (hB : 0 ≤ B) (hpq : p ≤ q) (hpB : -B ≤ p) :
    (stationaryMarginLaw E π).real (Icc p q) ≤
      nativeFirstMarginConcentrationConstant B * (q-p) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hset : MeasurableSet (Icc p q) := measurableSet_Icc
  let A : Set ℝ := {x : ℝ | E - |x| ∈ Icc p q}
  have hA : MeasurableSet A := by
    exact hset.preimage (measurable_const.sub measurable_abs)
  have hprod := nativeRestart_invariant_measure_eq_prod hX hπ hA
  have hmap0 : stationaryMarginLaw E π (Icc p q) = π A := by
    unfold stationaryMarginLaw A
    rw [Measure.map_apply (f := fun y : ℝ => E - |y|)
      (measurable_const.sub continuous_abs.measurable) hset]
    rfl
  have hmap : π A =
      (π.prod μ) ((fun z : ℝ × Ω => E - |nativeRestartNext X E z.1 z.2|) ⁻¹' Icc p q) := by
    rw [hprod]
    rfl
  have hms : MeasurableSet ((fun z : ℝ × Ω =>
      E - |nativeRestartNext X E z.1 z.2|) ⁻¹' Icc p q) := by
    exact hset.preimage (measurable_const.sub
      ((nativeRestartNext_measurable X hX E).abs))
  rw [Measure.real, hmap0, hmap, Measure.prod_apply hms]
  have hslice : ∀ x : ℝ,
      (Prod.mk x) ⁻¹' ((fun z : ℝ × Ω =>
        E - |nativeRestartNext X E z.1 z.2|) ⁻¹' Icc p q) =
      {ω | E - |nativeRestartNext X E x ω| ∈ Icc p q} := by
    intro x
    rfl
  have hbound : ∀ x : ℝ,
      μ ((Prod.mk x) ⁻¹' ((fun z : ℝ × Ω =>
        E - |nativeRestartNext X E z.1 z.2|) ⁻¹' Icc p q)) ≤
      ENNReal.ofReal (nativeFirstMarginConcentrationConstant B*(q-p)) := by
    intro x
    rw [hslice x]
    have hr := measureReal_nativeRestartMargin_mem_Icc_le hX hi hG hE hB hpq hpB x
    calc
      μ {ω | E - |nativeRestartNext X E x ω| ∈ Icc p q} =
          ENNReal.ofReal (μ.real {ω | E - |nativeRestartNext X E x ω| ∈ Icc p q}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (nativeFirstMarginConcentrationConstant B*(q-p)) :=
        ENNReal.ofReal_le_ofReal hr
  have hlin : (∫⁻ x, μ ((Prod.mk x) ⁻¹' ((fun z : ℝ × Ω =>
      E - |nativeRestartNext X E z.1 z.2|) ⁻¹' Icc p q)) ∂π) ≤
      ENNReal.ofReal (nativeFirstMarginConcentrationConstant B*(q-p)) := by
    calc
      _ ≤ ∫⁻ _x : ℝ, ENNReal.ofReal (nativeFirstMarginConcentrationConstant B*(q-p)) ∂π :=
        lintegral_mono hbound
      _ = ENNReal.ofReal (nativeFirstMarginConcentrationConstant B*(q-p)) := by
        rw [lintegral_const, measure_univ, mul_one]
  have hnon : 0 ≤ nativeFirstMarginConcentrationConstant B*(q-p) := by
    exact mul_nonneg (nativeFirstMarginConcentrationConstant_nonneg hB)
      (sub_nonneg.mpr hpq)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  simpa only [ENNReal.toReal_ofReal hnon] using hreal

/-! The stationary first absolute margin moment makes the normalized frozen
mean integrable under every actual stationary margin law. -/
theorem normalizedFrozenMean_integrable_stationaryMarginLaw [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    Integrable (normalizedFrozenMean X μ E)
      (stationaryMarginLaw E π) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let : IsProbabilityMeasure ν := by
    exact isProbabilityMeasure_stationaryMarginLaw E π
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hπabs0 := stationary_margin_abs_pow_integrable hX hi hG hE hπ
      (k := 1) (by norm_num)
  have hπabs : Integrable (fun y : ℝ => |E - abs y|) π := by
    simpa using hπabs0
  have hνabs : Integrable (fun r : ℝ => |r|) ν := by
    rw [show ν = stationaryMarginLaw E π by rfl, stationaryMarginLaw]
    apply (integrable_map_measure continuous_abs.aestronglyMeasurable
      (measurable_reflectedMargin E).aemeasurable).mpr
    simpa [Function.comp_def] using hπabs
  have hsum : Integrable (fun r : ℝ => 1 + |r|) ν :=
    (integrable_const (1 : ℝ)).add hνabs
  have hdom : Integrable (fun r : ℝ =>
      2 * frozenUniformMeanConstant * (1 + |r|)) ν := by
    simpa [mul_add] using hsum.const_mul (2 * frozenUniformMeanConstant)
  have hmeas : AEMeasurable (normalizedFrozenMean X μ E) ν :=
    normalizedFrozenMean_aemeasurable_stationaryMarginLaw hX hi hG E π
  refine hdom.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with r
  have hE1 : 1 ≤ E := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    exact h1.trans hEone
  rw [Real.norm_of_nonneg (normalizedFrozenMean_nonneg hX hi hG hE1)]
  have hm := normalizedFrozenMean_le_linear (r := r) hX hi hG hEone
  have hc : 0 ≤ 2 * frozenUniformMeanConstant := by
    nlinarith [frozenUniformMeanConstant_pos]
  exact hm.trans (mul_le_mul_of_nonneg_left (by
    have hmr : max r 0 ≤ |r| := max_le (le_abs_self r) (abs_nonneg r)
    linarith) hc)

/-!
The interval anti-concentration estimate combines with the all-state linear
bound for the normalized frozen mean.  This is the concrete zero-neighbourhood
estimate used by a cutoff transfer.  Integrability is kept explicit here: it
is supplied by the stationary first-moment estimate together with the linear
growth bound in the eventual full Theorem 4.3 assembly.
-/
theorem normalizedFrozenMean_setIntegral_Icc_zero_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ : ℝ}
    (hE : Real.exp 1 ≤ E) (hδ : 0 ≤ δ)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π)
    (hint : Integrable (normalizedFrozenMean X μ E)
      (stationaryMarginLaw E π)) :
    ∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
      4 * frozenUniformMeanConstant * (1 + δ) *
        nativeFirstMarginConcentrationConstant δ * δ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  have hE1 : 1 ≤ E := by
    have h1 : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    exact h1.trans hE
  have hmass := stationaryMarginLaw_interval_antiConcentration
    (X := X) (μ := μ) hX hi hG (E := E) (by linarith)
      hπ hδ (by linarith : -δ ≤ δ) (by linarith : -δ ≤ -δ)
  let : IsProbabilityMeasure ν := by
    exact isProbabilityMeasure_stationaryMarginLaw E π
  have hconst : 0 ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
    have h1 : 0 ≤ (1 + δ : ℝ) := by linarith
    nlinarith [frozenUniformMeanConstant_pos]
  have hpoint : ∀ x ∈ Icc (-δ) δ,
      normalizedFrozenMean X μ E x ≤
        2 * frozenUniformMeanConstant * (1 + δ) := by
    intro x hx
    have hm := normalizedFrozenMean_le_linear (r := x) hX hi hG hE
    have hx0 : max x 0 ≤ δ := max_le hx.2 hδ
    calc
      normalizedFrozenMean X μ E x ≤
          2 * frozenUniformMeanConstant * (1 + max x 0) := hm
      _ ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
        have hc : 0 ≤ 2 * frozenUniformMeanConstant := by
          nlinarith [frozenUniformMeanConstant_pos]
        exact mul_le_mul_of_nonneg_left (by linarith) hc
  have hsetint : IntegrableOn (normalizedFrozenMean X μ E) (Icc (-δ) δ) ν :=
    hint.integrableOn
  have hconstint : IntegrableOn (fun _ : ℝ =>
      2 * frozenUniformMeanConstant * (1 + δ)) (Icc (-δ) δ) ν :=
    (integrable_const _).integrableOn
  have hmono := setIntegral_mono_on hsetint hconstint measurableSet_Icc hpoint
  calc
    ∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r ∂ν ≤
        ∫ _r in Icc (-δ) δ, 2 * frozenUniformMeanConstant * (1 + δ) ∂ν := hmono
    _ = (2 * frozenUniformMeanConstant * (1 + δ)) * ν.real (Icc (-δ) δ) := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ (2 * frozenUniformMeanConstant * (1 + δ)) *
        (2 * nativeFirstMarginConcentrationConstant δ * δ) := by
      apply mul_le_mul_of_nonneg_left _ hconst
      have heq : nativeFirstMarginConcentrationConstant δ * (δ + δ) =
          2 * nativeFirstMarginConcentrationConstant δ * δ := by ring
      rw [show δ - -δ = δ + δ by ring, heq] at hmass
      simpa [ν] using hmass
    _ = 4 * frozenUniformMeanConstant * (1 + δ) *
        nativeFirstMarginConcentrationConstant δ * δ := by ring

/-! The preceding estimate with its explicit integrability input can be used
directly at the actual stationary scale; the moment theorem discharges that
input uniformly in the invariant law. -/
theorem normalizedFrozenMean_setIntegral_Icc_zero_le_of_stationary
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 ≤ δ)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    ∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
      4 * frozenUniformMeanConstant * (1 + δ) *
        nativeFirstMarginConcentrationConstant δ * δ := by
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  exact normalizedFrozenMean_setIntegral_Icc_zero_le hX hi hG hEone hδ hπ
    (normalizedFrozenMean_integrable_stationaryMarginLaw hX hi hG hE hπ)

/-! A fixed observation window removes the apparent dependence of the
anti-concentration constant on the shrinking cutoff.  For `δ ≤ 1` we may
always use the unit window in the one-step Gaussian bound; this is the form
that is uniform enough to send the zero cutoff to zero. -/
theorem stationaryMarginLaw_zero_interval_le_linear
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    (stationaryMarginLaw E π).real (Icc (-δ) δ) ≤
      2 * nativeFirstMarginConcentrationConstant 1 * δ := by
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hE2 : 1 ≤ 2 * E := by
    have hexp : (1 : ℝ) ≤ Real.exp 1 := by norm_num
    nlinarith
  have hmass := stationaryMarginLaw_interval_antiConcentration
    (X := X) (μ := μ) hX hi hG (E := E) hE2 hπ
      (B := 1) (p := -δ) (q := δ) (by norm_num)
      (by linarith) (by linarith)
  have hconst : 0 ≤ nativeFirstMarginConcentrationConstant 1 :=
    nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  rw [show δ - -δ = 2 * δ by ring] at hmass
  calc
    (stationaryMarginLaw E π).real (Icc (-δ) δ) ≤
        nativeFirstMarginConcentrationConstant 1 * (2 * δ) := hmass
    _ = 2 * nativeFirstMarginConcentrationConstant 1 * δ := by ring

theorem normalizedFrozenMean_setIntegral_Icc_zero_le_linear
    [SFinite μ] (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    ∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
      8 * frozenUniformMeanConstant *
        nativeFirstMarginConcentrationConstant 1 * δ := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmass := stationaryMarginLaw_zero_interval_le_linear
    (X := X) (μ := μ) hX hi hG hE hδ hδ1 hπ
  let : IsProbabilityMeasure (stationaryMarginLaw E π) :=
    isProbabilityMeasure_stationaryMarginLaw E π
  have hint := normalizedFrozenMean_integrable_stationaryMarginLaw
    (X := X) (μ := μ) hX hi hG hE hπ
  have hconst : 0 ≤ 2 * frozenUniformMeanConstant * (1 + δ) := by
    have : 0 ≤ (1 + δ : ℝ) := by linarith
    nlinarith [frozenUniformMeanConstant_pos]
  have hpoint : ∀ x ∈ Icc (-δ) δ,
      normalizedFrozenMean X μ E x ≤
        2 * frozenUniformMeanConstant * (1 + δ) := by
    intro x hx
    have hEone : Real.exp 1 ≤ E := by
      exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
    have hm := normalizedFrozenMean_le_linear (r := x) hX hi hG hEone
    have hx0 : max x 0 ≤ δ := max_le hx.2 hδ
    have hc : 0 ≤ 2 * frozenUniformMeanConstant := by
      nlinarith [frozenUniformMeanConstant_pos]
    exact hm.trans (mul_le_mul_of_nonneg_left (by linarith) hc)
  have hsetint : IntegrableOn (normalizedFrozenMean X μ E)
      (Icc (-δ) δ) (stationaryMarginLaw E π) := hint.integrableOn
  have hconstint : IntegrableOn (fun _ : ℝ =>
      2 * frozenUniformMeanConstant * (1 + δ))
      (Icc (-δ) δ) (stationaryMarginLaw E π) := (integrable_const _).integrableOn
  have hmono := setIntegral_mono_on hsetint hconstint measurableSet_Icc hpoint
  calc
    ∫ r in Icc (-δ) δ, normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
        (2 * frozenUniformMeanConstant * (1 + δ)) *
          (stationaryMarginLaw E π).real (Icc (-δ) δ) := by
      calc
        _ ≤ ∫ _r in Icc (-δ) δ,
            2 * frozenUniformMeanConstant * (1 + δ)
              ∂(stationaryMarginLaw E π) := hmono
        _ = _ := by rw [setIntegral_const, smul_eq_mul]; ring
    _ ≤ (2 * frozenUniformMeanConstant * (1 + δ)) *
        (2 * nativeFirstMarginConcentrationConstant 1 * δ) :=
      mul_le_mul_of_nonneg_left hmass hconst
    _ ≤ 8 * frozenUniformMeanConstant *
        nativeFirstMarginConcentrationConstant 1 * δ := by
      have hδ' : 1 + δ ≤ 2 := by linarith
      have hnc : 0 ≤ nativeFirstMarginConcentrationConstant 1 :=
        nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
      have hFC : 0 ≤ 4 * frozenUniformMeanConstant *
          nativeFirstMarginConcentrationConstant 1 := by
        positivity [frozenUniformMeanConstant_pos]
      calc
        2 * frozenUniformMeanConstant * (1 + δ) *
              (2 * nativeFirstMarginConcentrationConstant 1 * δ) =
            (4 * frozenUniformMeanConstant *
              nativeFirstMarginConcentrationConstant 1 * (1 + δ)) * δ := by ring
        _ ≤ (4 * frozenUniformMeanConstant *
              nativeFirstMarginConcentrationConstant 1 * 2) * δ := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hδ' hFC) hδ
        _ = 8 * frozenUniformMeanConstant *
            nativeFirstMarginConcentrationConstant 1 * δ := by ring

/-! A second stationary margin moment gives a uniform integrable tail for the
normalized frozen mean.  This is the far-cutoff estimate needed on the finite
budget side of the transfer; its right-hand side is independent of `E` and
the invariant law. -/
theorem normalizedFrozenMean_setIntegral_abs_gt_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E C : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hC : 1 ≤ C)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    ∫ r in {r : ℝ | C < |r|}, normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
      (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let : IsProbabilityMeasure ν := by
    exact isProbabilityMeasure_stationaryMarginLaw E π
  have hmE := normalizedFrozenMean_integrable_stationaryMarginLaw
    (X := X) (μ := μ) hX hi hG hE hπ
  have hπpow0 := nativeRestart_stationary_margin_pow_le hX hi hG hE hπ
      (k := 2) (by norm_num)
  have hπpow : Integrable (fun y : ℝ => |E - abs y| ^ 2) π :=
    stationary_margin_abs_pow_integrable hX hi hG hE hπ (k := 2) (by norm_num)
  have hνpow : Integrable (fun r : ℝ => |r| ^ 2) ν := by
    rw [show ν = stationaryMarginLaw E π by rfl, stationaryMarginLaw]
    apply (integrable_map_measure (continuous_abs.pow 2).aestronglyMeasurable
      (measurable_reflectedMargin E).aemeasurable).mpr
    simpa [Function.comp_def] using hπpow
  have hνpow_int : (∫ r, |r| ^ 2 ∂ν) ≤ stationaryMarginMomentBound 2 := by
    have hmap := MeasureTheory.integral_map (μ := π)
      (φ := fun y : ℝ => E - |y|)
      (measurable_reflectedMargin E).aemeasurable
      ((continuous_abs.pow 2).aestronglyMeasurable)
    have heq : (∫ r, |r| ^ 2 ∂ν) =
        ∫ y, |E - abs y| ^ 2 ∂π := by
      simpa [ν, stationaryMarginLaw, Function.comp_def] using hmap
    rw [heq]
    exact hπpow0
  have hdom : Integrable (fun r : ℝ =>
      (4 * frozenUniformMeanConstant / C) * |r| ^ 2) ν :=
    hνpow.const_mul _
  have hset := KernelLimit.measurableSet_abs_gt C
  have hpoint : ∀ r ∈ {r : ℝ | C < |r|},
      normalizedFrozenMean X μ E r ≤
        (4 * frozenUniformMeanConstant / C) * |r| ^ 2 := by
    intro r hr
    have ha : C < |r| := hr
    have ha0 : 0 ≤ |r| := abs_nonneg r
    have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
    have hCa : C ≤ |r| := ha.le
    have h1a : 1 + |r| ≤ 2 * |r| := by linarith
    have hsq : |r| ≤ |r| ^ 2 / C := by
      apply (le_div_iff₀ hC0).2
      nlinarith [mul_le_mul_of_nonneg_left hCa ha0]
    have hEone : Real.exp 1 ≤ E := by
      exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
    have hm := normalizedFrozenMean_le_linear (r := r) hX hi hG hEone
    have hmax : max r 0 ≤ |r| := max_le (le_abs_self r) ha0
    have hK : 0 ≤ 2 * frozenUniformMeanConstant := by
      nlinarith [frozenUniformMeanConstant_pos]
    calc
      normalizedFrozenMean X μ E r ≤
          2 * frozenUniformMeanConstant * (1 + max r 0) := hm
      _ ≤ 2 * frozenUniformMeanConstant * (1 + |r|) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      _ ≤ 4 * frozenUniformMeanConstant * |r| := by
        nlinarith
      _ ≤ (4 * frozenUniformMeanConstant / C) * |r| ^ 2 := by
        have hK4 : 0 ≤ 4 * frozenUniformMeanConstant := by
          nlinarith [frozenUniformMeanConstant_pos]
        have hstep := mul_le_mul_of_nonneg_left hsq hK4
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep
  have hmEν : Integrable (normalizedFrozenMean X μ E) ν := by
    simpa [ν] using hmE
  have hmono := setIntegral_mono_on hmEν.integrableOn hdom.integrableOn hset hpoint
  change (∫ r in {r : ℝ | C < |r|}, normalizedFrozenMean X μ E r ∂ν) ≤ _
  calc
    ∫ r in {r : ℝ | C < |r|}, normalizedFrozenMean X μ E r ∂ν ≤
        ∫ r in {r : ℝ | C < |r|},
          (4 * frozenUniformMeanConstant / C) * |r| ^ 2 ∂ν := hmono
    _ ≤ ∫ r, (4 * frozenUniformMeanConstant / C) * |r| ^ 2 ∂ν := by
      have hcoef : 0 ≤ 4 * frozenUniformMeanConstant / C := by
        positivity [frozenUniformMeanConstant_pos]
      exact setIntegral_le_integral hdom
        (ae_of_all _ fun r => mul_nonneg hcoef (sq_nonneg |r|))
    _ = (4 * frozenUniformMeanConstant / C) * (∫ r, |r| ^ 2 ∂ν) := by
      rw [integral_const_mul]
    _ ≤ (4 * frozenUniformMeanConstant / C) * stationaryMarginMomentBound 2 := by
      have hcoef : 0 ≤ 4 * frozenUniformMeanConstant / C := by
        positivity [frozenUniformMeanConstant_pos]
      exact mul_le_mul_of_nonneg_left hνpow_int hcoef

/-! On the negative middle annulus, the logarithmic carry estimate gives a
uniform `O(1 / log E)` bound.  This is the finite-budget estimate needed when
the zero neighbourhood has already been removed: unlike the refined Gaussian
tail bound below, it is useful at a fixed small cutoff `δ`. -/
theorem normalizedFrozenMean_setIntegral_Iio_neg_log_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E δ : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (hδ : 0 < δ)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    ∫ r in Iio (-δ), normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
      frozenNegativeCarryLogConstant / Real.log E *
        (1 + max (Real.log (1/δ)) 0) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let : IsProbabilityMeasure ν := by
    exact isProbabilityMeasure_stationaryMarginLaw E π
  have hmE := normalizedFrozenMean_integrable_stationaryMarginLaw
    (X := X) (μ := μ) hX hi hG hE hπ
  have hEm : (16 : ℝ) ≤ E := by
    have hthr : stationaryMarginThreshold ≤ E :=
      (le_max_left _ _).trans ((le_max_left _ _).trans hE)
    have hnum : (5120000 : ℝ) ≤ stationaryMarginThreshold := by
      norm_num [stationaryMarginThreshold]
    linarith
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hlogpos : 0 < Real.log E := by
    exact Real.log_pos (lt_of_lt_of_le (by norm_num) hEone)
  have hpoint : ∀ r ∈ Iio (-δ),
      normalizedFrozenMean X μ E r ≤
        frozenNegativeCarryLogConstant / Real.log E *
          (1 + max (Real.log (1/δ)) 0) := by
    intro r hr
    have hr' : r < -δ := hr
    have hc : 0 < -r := by linarith
    have hcδ : δ < -r := by linarith
    have hlogc : max (Real.log (1 / (-r))) 0 ≤
        max (Real.log (1 / δ)) 0 := by
      apply max_le_max_right
      have hinv : 1 / (-r) ≤ 1 / δ := by
        exact one_div_le_one_div_of_le hδ hcδ.le
      exact Real.log_le_log (by positivity) hinv
    have hraw := frozenPrefixLength_negative_mean_log_bound hX hi hG hc hEm
    have hraw' : (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤
        frozenNegativeCarryLogConstant * E *
          (1 + max (Real.log (1/δ)) 0) := by
      rw [show r = -(-r) by ring]
      calc
        (∫ ω, frozenPrefixLengthReal X (-(-r)) E ω ∂μ) ≤
            frozenNegativeCarryLogConstant * E *
              (1 + max (Real.log (1 / (-r))) 0) := hraw
        _ ≤ frozenNegativeCarryLogConstant * E *
              (1 + max (Real.log (1/δ)) 0) := by
          have hfac : 0 ≤ frozenNegativeCarryLogConstant * E := by
            exact mul_nonneg frozenNegativeCarryLogConstant_pos.le (by linarith)
          exact mul_le_mul_of_nonneg_left (by linarith [hlogc]) hfac
    unfold normalizedFrozenMean
    apply (div_le_iff₀ (mul_pos (by linarith : 0 < E) hlogpos)).2
    calc
      (∫ ω, frozenPrefixLengthReal X r E ω ∂μ) ≤
          frozenNegativeCarryLogConstant * E *
            (1 + max (Real.log (1/δ)) 0) := hraw'
      _ = (frozenNegativeCarryLogConstant / Real.log E *
          (1 + max (Real.log (1/δ)) 0)) * (E * Real.log E) := by
        field_simp
  have hconst : Integrable (fun _ : ℝ =>
      frozenNegativeCarryLogConstant / Real.log E *
        (1 + max (Real.log (1/δ)) 0)) ν := integrable_const _
  have hmEν : Integrable (normalizedFrozenMean X μ E) ν := by
    simpa [ν] using hmE
  have hmono := setIntegral_mono_on hmEν.integrableOn hconst.integrableOn
    measurableSet_Iio hpoint
  change (∫ r in Iio (-δ), normalizedFrozenMean X μ E r ∂ν) ≤ _
  calc
    ∫ r in Iio (-δ), normalizedFrozenMean X μ E r ∂ν ≤
        ∫ _r in Iio (-δ), frozenNegativeCarryLogConstant / Real.log E *
          (1 + max (Real.log (1/δ)) 0) ∂ν := hmono
    _ = (frozenNegativeCarryLogConstant / Real.log E *
          (1 + max (Real.log (1/δ)) 0)) * ν.real (Iio (-δ)) := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ frozenNegativeCarryLogConstant / Real.log E *
          (1 + max (Real.log (1/δ)) 0) := by
      have hcoef : 0 ≤ frozenNegativeCarryLogConstant / Real.log E *
          (1 + max (Real.log (1/δ)) 0) := by
        have hmax : 0 ≤ max (Real.log (1/δ)) 0 := le_max_right _ _
        positivity [frozenNegativeCarryLogConstant_pos]
      have hmass : ν.real (Iio (-δ)) ≤ 1 := measureReal_le_one
      simpa [mul_one] using mul_le_mul_of_nonneg_left hmass hcoef

/-! The refined stationary negative-margin tail separates the Gaussian tail
from the bad completion branch.  After multiplying by the bounded negative
margin reward this is the exact one-sided cutoff estimate needed before taking
the budget to infinity. -/
theorem normalizedFrozenMean_setIntegral_Iio_neg_le [SFinite μ]
    (hX : ∀ j, Measurable (X j)) (hi : iIndepFun X μ)
    (hG : ∀ j, μ.map (X j) = gaussianReal 0 1) {E t : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (ht : 0 ≤ t)
    {π : Measure ℝ} [IsProbabilityMeasure π]
    (hπ : (nativeRestartKernel X μ E).Invariant π) :
    ∫ r in Iio (-t), normalizedFrozenMean X μ E r
        ∂(stationaryMarginLaw E π) ≤
      2 * frozenUniformMeanConstant *
        (Real.exp (-t^2/2) +
          stationaryBadBranchConstant * stationaryScaleConstant *
            Real.log E / E) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let ν : Measure ℝ := stationaryMarginLaw E π
  let : IsProbabilityMeasure ν := by
    exact isProbabilityMeasure_stationaryMarginLaw E π
  have hmE := normalizedFrozenMean_integrable_stationaryMarginLaw
    (X := X) (μ := μ) hX hi hG hE hπ
  have hEone : Real.exp 1 ≤ E := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hE)
  have hEpos : 0 < E := by
    have hthr : stationaryMarginThreshold ≤ E :=
      (le_max_left _ _).trans ((le_max_left _ _).trans hE)
    have h' : (0 : ℝ) < stationaryMarginThreshold := by
      norm_num [stationaryMarginThreshold]
    exact lt_of_lt_of_le h' hthr
  have htail := measure_pi_nativeRestart_margin_refined_tail hX hi hG
    (E := E) hEpos hπ ht
  have hbad := measure_prod_nativeRestart_bad_branch_log_scale hX hi hG hE hπ
  have htailset : ν (Iio (-t)) =
      π {y : ℝ | t < nativeRestartExcess E y} := by
    rw [show ν = stationaryMarginLaw E π by rfl, stationaryMarginLaw,
      Measure.map_apply (measurable_reflectedMargin E) measurableSet_Iio]
    congr 1
    ext y
    change (E - |y| < -t) ↔ t < max (|y| - E) 0
    constructor
    · intro hy
      have hta : t < |y| - E := by linarith
      exact lt_of_lt_of_le hta (le_max_left _ _)
    · intro hy
      by_cases ha : |y| - E ≤ 0
      · have hz : max (|y| - E) 0 = 0 := max_eq_right ha
        rw [hz] at hy
        linarith
      · have hmax : max (|y| - E) 0 = |y| - E :=
          max_eq_left (le_of_not_ge ha)
        rw [hmax] at hy
        linarith
  have htailR : ν.real (Iio (-t)) ≤
      Real.exp (-t^2/2) +
        ((π.prod μ) (nativeRestartFavorableSet X E)ᶜ).toReal := by
    rw [Measure.real, htailset]
    have htop : ENNReal.ofReal (Real.exp (-t^2/2)) +
        (π.prod μ) (nativeRestartFavorableSet X E)ᶜ ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top _ _⟩
    have hto := ENNReal.toReal_mono htop htail
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ _),
      ENNReal.toReal_ofReal (Real.exp_pos _).le] at hto
    exact hto
  have hbadR : ((π.prod μ) (nativeRestartFavorableSet X E)ᶜ).toReal ≤
      stationaryBadBranchConstant * stationaryScaleConstant * Real.log E / E := by
    have hto := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
    have hlog : 0 ≤ Real.log E := Real.log_nonneg (by
      have h1 : (1 : ℝ) ≤ Real.exp 1 := by norm_num
      exact h1.trans hEone)
    have hscale : 0 ≤ stationaryScaleConstant := by
      unfold stationaryScaleConstant
      have hM := stationaryMarginMomentConstant_nonneg
      have hG' := stationaryEnvelopeMeanBound_nonneg
      nlinarith [frozenUniformMeanConstant_pos]
    have hnon : 0 ≤ stationaryBadBranchConstant * stationaryScaleConstant *
        Real.log E / E := by
      apply div_nonneg
      · exact mul_nonneg
          (mul_nonneg (stationaryBadBranchConstant_pos.le) hscale) hlog
      · exact hEpos.le
    rw [ENNReal.toReal_ofReal hnon] at hto
    exact hto
  have htailR' : ν.real (Iio (-t)) ≤
      Real.exp (-t^2/2) +
        stationaryBadBranchConstant * stationaryScaleConstant * Real.log E / E :=
    htailR.trans (by exact add_le_add_right hbadR _)
  have hpoint : ∀ r ∈ Iio (-t),
      normalizedFrozenMean X μ E r ≤ 2 * frozenUniformMeanConstant := by
    intro r hr
    have hm := normalizedFrozenMean_le_linear (r := r) hX hi hG hEone
    have hr' : r < -t := hr
    have hr0 : max r 0 = 0 := max_eq_right (by linarith [hr'])
    rw [hr0] at hm
    simpa using hm
  have hconst : Integrable (fun _ : ℝ =>
      2 * frozenUniformMeanConstant) ν := integrable_const _
  have hmEν : Integrable (normalizedFrozenMean X μ E) ν := by
    simpa [ν] using hmE
  have hmono := setIntegral_mono_on hmEν.integrableOn hconst.integrableOn
    measurableSet_Iio hpoint
  change (∫ r in Iio (-t), normalizedFrozenMean X μ E r ∂ν) ≤ _
  calc
    ∫ r in Iio (-t), normalizedFrozenMean X μ E r ∂ν ≤
        ∫ _r in Iio (-t), 2 * frozenUniformMeanConstant ∂ν := hmono
    _ = (2 * frozenUniformMeanConstant) * ν.real (Iio (-t)) := by
      rw [setIntegral_const, smul_eq_mul]
      ring
    _ ≤ (2 * frozenUniformMeanConstant) *
        (Real.exp (-t^2/2) +
          stationaryBadBranchConstant * stationaryScaleConstant * Real.log E / E) := by
      apply mul_le_mul_of_nonneg_left _ (by
        nlinarith [frozenUniformMeanConstant_pos])
      exact htailR'


end LeadingCoefficient
end SwingRepair
