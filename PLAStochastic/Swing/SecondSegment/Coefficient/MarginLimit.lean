import PLAStochastic.Swing.SecondSegment.Coefficient.Uniform
import PLAStochastic.Swing.SecondSegment.Coefficient.NearZero
import PLAStochastic.Swing.SecondSegment.MeanUpperBound
import PLAStochastic.Swing.Transient.MarginLaw

/-! # The first-entrance margin law and its weak limits

`second-coefficient.md`, §2.  The law `ρ_{1,E} = Law(R_{1,E})` of the actual
first margin is `nativeTransientMarginLaw X μ E 1`.  This file transports the
first-segment estimates to that law:

* the budget-free small-ball bound `ρ_{1,E}{|r| < s} ≤ 2C s` (Lemma H.2);
* `ρ_{1,E}[0, ∞) = O(E^{-1/4})` and `∫ r_+ dρ_{1,E} = O(E^{-1/2})` (C2.6, C2.9);
* the uniform first absolute moment;

and the mean identity `E L_{2,E}/E = ∫ g_E/E dρ_{1,E}`.  Along any filter on
which `ρ_{1,E} ⇒ ν`, the open-set half of the portmanteau theorem gives that
`ν` inherits the small-ball bound, is carried by `(-∞, 0)`, and has the same
first-moment tail; consequently `ℓ` is `ν`-integrable.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The law of the first margin -/

/-- The first transient margin law is the law of the actual first margin. -/
theorem map_nativeFirstMargin_eq_transientMarginLaw
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    μ.map (nativeFirstMargin X E) = nativeTransientMarginLaw X μ E 1 := by
  have hnext : Measurable (nativeFirstNext X E) :=
    (nativeRestartNext_measurable (fun k => X (1+k)) (fun k => hX (1+k)) E).comp
      ((hX 0).prodMk measurable_id)
  rw [nativeTransientMarginLaw, nativeTransientLaw_one hX hi hG hE,
    Measure.map_map (measurable_finiteMarginMap E) hnext]
  rfl

theorem transientMarginLaw_one_apply
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    {S : Set ℝ} (hS : MeasurableSet S) :
    nativeTransientMarginLaw X μ E 1 S =
      ENNReal.ofReal (μ.real {ω | nativeFirstMargin X E ω ∈ S}) := by
  have := hi.isProbabilityMeasure
  rw [← map_nativeFirstMargin_eq_transientMarginLaw hX hi hG hE,
    Measure.map_apply (nativeFirstMargin_measurable hX E) hS,
    ofReal_measureReal (measure_ne_top _ _)]
  rfl

/-- The budget-free small-ball bound of Lemma H.2 on `ρ_{1,E}`. -/
theorem transientMarginLaw_one_ball_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    nativeTransientMarginLaw X μ E 1 {r : ℝ | |r| < s} ≤
      ENNReal.ofReal (2 * nativeFirstMarginConcentrationConstant 1 * s) := by
  have hE0 : 0 < E := by linarith
  rw [transientMarginLaw_one_apply hX hi hG hE0
    (measurableSet_lt continuous_abs.measurable measurable_const)]
  apply ENNReal.ofReal_le_ofReal
  have := hi.isProbabilityMeasure
  have h := measureReal_nativeFirstMargin_abs_le hX hi hG hE (δ := s) (B := 1) hs hs1
  have hsub : {ω | nativeFirstMargin X E ω ∈ {r : ℝ | |r| < s}} ⊆
      {ω | |nativeFirstMargin X E ω| ≤ s} := by
    intro ω hω
    have hω' : |nativeFirstMargin X E ω| < s := hω
    show |nativeFirstMargin X E ω| ≤ s
    exact le_of_lt hω'
  calc μ.real {ω | nativeFirstMargin X E ω ∈ {r : ℝ | |r| < s}}
      ≤ μ.real {ω | |nativeFirstMargin X E ω| ≤ s} := measureReal_mono hsub
    _ ≤ nativeFirstMarginConcentrationConstant 1 * (2*s) := h
    _ = 2 * nativeFirstMarginConcentrationConstant 1 * s := by ring

/-- The constant of `ρ_{1,E}[0,∞) = O(E^{-1/4})`. -/
def firstMarginNonnegConstant : ℝ :=
  2*nativeFirstMarginConcentrationConstant 1+secondMarginPosConstant

/-- C2.9: the first margin is nonnegative only with probability `O(E^{-1/4})`. -/
theorem transientMarginLaw_one_Ici_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) :
    nativeTransientMarginLaw X μ E 1 (Ici 0) ≤
      ENNReal.ofReal (firstMarginNonnegConstant / Real.sqrt (Real.sqrt E)) := by
  rw [transientMarginLaw_one_apply hX hi hG (by linarith) measurableSet_Ici]
  exact ENNReal.ofReal_le_ofReal (measureReal_nativeFirstMargin_nonneg_le hX hi hG hE)

/-- C2.6: the mean positive part of the first margin is `O(E^{-1/2})`. -/
theorem integral_transientMarginLaw_one_pos_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) :
    Integrable (fun r : ℝ => max r 0) (nativeTransientMarginLaw X μ E 1) ∧
      (∫ r, max r 0 ∂(nativeTransientMarginLaw X μ E 1)) ≤
        secondMarginPosConstant / Real.sqrt E := by
  have hE0 : 0 < E := by linarith
  have hm : AEStronglyMeasurable (fun r : ℝ => max r 0) (nativeTransientMarginLaw X μ E 1) :=
    (measurable_id.max measurable_const).aestronglyMeasurable
  rw [← map_nativeFirstMargin_eq_transientMarginLaw hX hi hG hE0] at hm ⊢
  constructor
  · rw [integrable_map_measure hm (nativeFirstMargin_measurable hX E).aemeasurable]
    exact integrable_nativeFirstMargin_pos hX hi hG (by linarith)
  · rw [integral_map (nativeFirstMargin_measurable hX E).aemeasurable hm]
    exact integral_nativeFirstMargin_pos_le hX hi hG hE

/-- The uniform first absolute moment of `ρ_{1,E}`. -/
theorem integral_transientMarginLaw_one_abs_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) :
    Integrable (fun r : ℝ => |r|) (nativeTransientMarginLaw X μ E 1) ∧
      (∫ r, |r| ∂(nativeTransientMarginLaw X μ E 1)) ≤ nativeFirstMarginMomentBound 1 := by
  have hE0 : 0 < E := by linarith
  have hm : AEStronglyMeasurable (fun r : ℝ => |r|) (nativeTransientMarginLaw X μ E 1) :=
    continuous_abs.measurable.aestronglyMeasurable
  rw [← map_nativeFirstMargin_eq_transientMarginLaw hX hi hG hE0] at hm ⊢
  constructor
  · rw [integrable_map_measure hm (nativeFirstMargin_measurable hX E).aemeasurable]
    exact integrable_nativeFirstMargin_abs hX hi hG hE
  · rw [integral_map (nativeFirstMargin_measurable hX E).aemeasurable hm]
    have := integral_nativeFirstMargin_pow_le hX hi hG hE 1
    simpa only [pow_one] using this

/-- Markov's inequality for the far negative tail of `ρ_{1,E}`. -/
theorem transientMarginLaw_one_Iio_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 1 ≤ 2*E) {M : ℝ} (hM : 0 < M) :
    nativeTransientMarginLaw X μ E 1 (Iio (-M)) ≤
      ENNReal.ofReal (nativeFirstMarginMomentBound 1 / M) := by
  have := hi.isProbabilityMeasure
  have : IsProbabilityMeasure (nativeTransientMarginLaw X μ E 1) :=
    nativeTransientMarginLaw_isProbability hX E 1
  obtain ⟨hint, hle⟩ := integral_transientMarginLaw_one_abs_le hX hi hG hE
  set ρ := nativeTransientMarginLaw X μ E 1
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := ρ) (ae_of_all _ fun r => abs_nonneg r)
    hint M
  have hsub : Iio (-M) ⊆ {r : ℝ | M ≤ |r|} := by
    intro r hr
    have hr' : r < -M := hr
    show M ≤ |r|
    rw [abs_of_neg (by linarith)]
    linarith
  have hreal : ρ.real (Iio (-M)) ≤ nativeFirstMarginMomentBound 1 / M := by
    rw [le_div_iff₀ hM]
    calc ρ.real (Iio (-M)) * M ≤ M * ρ.real {r : ℝ | M ≤ |r|} := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left (measureReal_mono hsub) hM.le
      _ ≤ ∫ r, |r| ∂ρ := hmark
      _ ≤ _ := hle
  rw [← ofReal_measureReal (measure_ne_top ρ _)]
  exact ENNReal.ofReal_le_ofReal hreal

/-! ### The mean identity -/

/-- `E L_{2,E}/E = ∫ g_E/E dρ_{1,E}`. -/
theorem secondSegment_normalizedMean_eq_integral
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    (∫ ω, (nativeRecordingDurationNat X E 1 ω : ℝ) ∂μ) / E =
      ∫ r, secondSegmentFrozenMean X μ E r / E ∂(nativeTransientMarginLaw X μ E 1) := by
  have := hi.isProbabilityMeasure
  rw [secondSegment_mean_eq hX hi hG hE, ← map_nativeFirstMargin_eq_transientMarginLaw hX hi hG hE,
    integral_map (nativeFirstMargin_measurable hX E).aemeasurable
      ((secondSegmentFrozenMean_measurable hX E).div_const E).aestronglyMeasurable,
    integral_div]
  rfl

/-! ### Vanishing of the positive-side factor -/

theorem tendsto_one_add_log_div_sqrt_sqrt :
    Tendsto (fun E : ℝ => (1 + Real.log E) / Real.sqrt (Real.sqrt E)) atTop (𝓝 0) := by
  have hS : Tendsto (fun E : ℝ => Real.sqrt (Real.sqrt E)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hS
  have h2 := tendsto_inv_atTop_zero.comp hS
  have h3 := h2.add (h1.const_mul 4)
  rw [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with E hE
  have hS0 : 0 < Real.sqrt (Real.sqrt E) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hE)
  have hS4 : Real.sqrt (Real.sqrt E)^4 = E := by
    have h : Real.sqrt (Real.sqrt E)^4 = (Real.sqrt (Real.sqrt E)^2)^2 := by ring
    rw [h, Real.sq_sqrt (Real.sqrt_nonneg E), Real.sq_sqrt hE.le]
  have hlog : Real.log E = 4 * Real.log (Real.sqrt (Real.sqrt E)) := by
    conv_lhs => rw [← hS4]
    rw [Real.log_pow]
    push_cast
    ring
  simp only [Function.comp_apply, pow_one, one_mul, add_zero]
  rw [hlog]
  field_simp

/-! ### Weak limits of the first margin law -/

section Limit

variable {ι : Type*} {l : Filter ι} [l.NeBot] {budget : ι → ℝ} {ν : ProbabilityMeasure ℝ}

/-- The limit inherits the budget-free small-ball bound. -/
theorem firstMarginLimit_ball_le [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hbudget_top : Tendsto budget l atTop)
    (hν : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν))
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    (ν : Measure ℝ) {r : ℝ | |r| < s} ≤
      ENNReal.ofReal (2 * nativeFirstMarginConcentrationConstant 1 * s) := by
  apply measure_isOpen_le_of_eventually hν (isOpen_lt continuous_abs continuous_const)
  filter_upwards [hbudget_top.eventually (eventually_ge_atTop (1 : ℝ))] with i hi1
  exact transientMarginLaw_one_ball_le hX hi hG (by linarith) hs hs1

/-- The limit has no atom at the origin. -/
theorem firstMarginLimit_singleton_zero [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hbudget_top : Tendsto budget l atTop)
    (hν : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    (ν : Measure ℝ) {0} = 0 := by
  set C := nativeFirstMarginConcentrationConstant 1
  have hC : 0 ≤ C := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  set s : ℝ := min 1 ((ε : ℝ) / (2*C + 1)) with hsdef
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsub : ({0} : Set ℝ) ⊆ {r : ℝ | |r| < s} := by
    intro r hr
    rw [mem_singleton_iff] at hr
    show |r| < s
    rw [hr, abs_zero]
    exact hs0
  refine (measure_mono hsub).trans
    ((firstMarginLimit_ball_le hX hi hG hbudget_top hν hs0.le hs1).trans ?_)
  rw [← ENNReal.ofReal_coe_nnreal]
  apply ENNReal.ofReal_le_ofReal
  have h1 : s ≤ (ε : ℝ) / (2*C + 1) := min_le_right _ _
  have h2 : 2*C*s ≤ (2*C + 1)*s := by nlinarith
  calc 2*C*s ≤ (2*C + 1)*s := h2
    _ ≤ (2*C + 1)*((ε : ℝ) / (2*C + 1)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ε := by field_simp

/-- The limit carries no mass on `(0, ∞)`. -/
theorem firstMarginLimit_Ioi_zero [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hbudget_top : Tendsto budget l atTop)
    (hν : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    (ν : Measure ℝ) (Ioi 0) = 0 := by
  have hS : Tendsto (fun i => Real.sqrt (Real.sqrt (budget i))) l atTop :=
    (Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop).comp hbudget_top
  have ha : Tendsto (fun i => firstMarginNonnegConstant / Real.sqrt (Real.sqrt (budget i))) l
      (𝓝 0) := tendsto_const_nhds.div_atTop hS
  apply measure_isOpen_eq_zero_of_tendsto hν isOpen_Ioi ha
  filter_upwards [hbudget_top.eventually (eventually_ge_atTop (16 : ℝ))] with i hi16
  exact (measure_mono Ioi_subset_Ici_self).trans (transientMarginLaw_one_Ici_le hX hi hG hi16)

/-- The limit is carried by the open negative half-line. -/
theorem firstMarginLimit_Ici_zero [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hbudget_top : Tendsto budget l atTop)
    (hν : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    (ν : Measure ℝ) (Ici 0) = 0 := by
  rw [← Ioi_insert, insert_eq]
  refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
  rw [firstMarginLimit_singleton_zero hX hi hG hbudget_top hν,
    firstMarginLimit_Ioi_zero hX hi hG hbudget_top hν, add_zero]

theorem firstMarginLimit_ae_neg [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hbudget_top : Tendsto budget l atTop)
    (hν : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    ∀ᵐ r ∂(ν : Measure ℝ), r < 0 := by
  rw [ae_iff]
  have h : {r : ℝ | ¬ r < 0} = Ici 0 := by ext r; simp
  rw [h]
  exact firstMarginLimit_Ici_zero hX hi hG hbudget_top hν

/-- The limit inherits the far negative tail bound. -/
theorem firstMarginLimit_Iio_le [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (hbudget_top : Tendsto budget l atTop)
    (hν : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν))
    {M : ℝ} (hM : 0 < M) :
    (ν : Measure ℝ) (Iio (-M)) ≤ ENNReal.ofReal (nativeFirstMarginMomentBound 1 / M) := by
  apply measure_isOpen_le_of_eventually hν isOpen_Iio
  filter_upwards [hbudget_top.eventually (eventually_ge_atTop (1 : ℝ))] with i hi1
  exact transientMarginLaw_one_Iio_le hX hi hG (by linarith) hM

end Limit

/-! ### Integrability of the kernel against a limit law -/

/-- On the negative half-line, `ℓ ≤ C + C·1_{|r|<1}(1 + log₊(1/|r|))`. -/
theorem secondSegmentLimitKernel_le_nearZero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    secondSegmentLimitKernel X μ r ≤ frozenNegativeCarryLogConstant *
      (1 + {r : ℝ | |r| < 1}.indicator (fun r => 1 + nearZeroLogWeight r) r) := by
  have h := secondSegmentLimitKernel_neg_le_log hX hi hG (c := -r) (by linarith)
  rw [neg_neg] at h
  have hK := frozenNegativeCarryLogConstant_pos
  have hw : max (Real.log (1/(-r))) 0 ≤
      {r : ℝ | |r| < 1}.indicator (fun r => 1 + nearZeroLogWeight r) r := by
    have habs : |r| = -r := abs_of_neg hr
    by_cases h1 : |r| < 1
    · rw [Set.indicator_of_mem (show r ∈ {r : ℝ | |r| < 1} from h1)]
      unfold nearZeroLogWeight
      rw [habs]
      linarith
    · rw [Set.indicator_of_notMem (show r ∉ {r : ℝ | |r| < 1} from h1)]
      have h0 := nearZeroLogWeight_eq_zero (not_lt.mp h1)
      unfold nearZeroLogWeight at h0
      rw [habs] at h0
      rw [h0]
  calc secondSegmentLimitKernel X μ r ≤ frozenNegativeCarryLogConstant *
        (1 + max (Real.log (1/(-r))) 0) := h
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK.le

/-- `ℓ` is integrable against every law carried by `(-∞, 0)` with a small-ball bound. -/
theorem secondSegmentLimitKernel_integrable_of_ball
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hneg : ∀ᵐ r ∂ρ, r < 0) {D : ℝ} (hD : 0 ≤ D)
    (hball : ∀ s, 0 < s → s ≤ 1 → ρ {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*D*s)) :
    Integrable (secondSegmentLimitKernel X μ) ρ := by
  have := hi.isProbabilityMeasure
  obtain ⟨hint, -⟩ := integral_indicator_one_add_nearZeroLogWeight_le (ρ := ρ) hD one_pos hball
  have hdom : Integrable (fun r => frozenNegativeCarryLogConstant *
      (1 + {r : ℝ | |r| < 1}.indicator (fun r => 1 + nearZeroLogWeight r) r)) ρ :=
    ((integrable_const 1).add hint).const_mul _
  refine hdom.mono' (secondSegmentLimitKernel_stronglyMeasurable hX).aestronglyMeasurable ?_
  filter_upwards [hneg] with r hr
  rw [Real.norm_of_nonneg (secondSegmentLimitKernel_nonneg hX hi hG r)]
  exact secondSegmentLimitKernel_le_nearZero hX hi hG hr

end SwingRepair
