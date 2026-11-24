import PLAStochastic.Swing.StationaryLimit.Slope.FiniteMoments
import PLAStochastic.Swing.SecondSegment.FrozenMeanBridge

/-! # The limiting conditional kernel `ℓ(r) = E[2/A_r]` of the second segment

`second-coefficient.md`, C2.1 and C2.5.  For an incoming margin `r`, the actual
limiting slope is `A_r = sup_{n ≥ 0} (W_n - r)/(n+1)` (`swingLimitingSlope`).
The conditional linear kernel of the second segment is `ℓ(r) = E[2/A_r]`.

On the negative half-line the `n = 0` term gives `A_r ≥ -r`, so `2/A_r ≤ 2/|r|`;
together with the pathwise `1`-Lipschitz dependence of `A_r` on `r` this makes
`ℓ` finite, bounded by `2/|r|`, strictly positive and `2δ⁻²`-Lipschitz on
`(-∞, -δ]` (C2.5).  The frozen-carry lengths converge pathwise to
`2/frozenSlopeMagnitude`, which is the reflected slope; reflection invariance
of the Gaussian walk identifies its mean with `ℓ`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- `ℓ(r) = E[2/A_r]`: the conditional linear kernel of the second segment. -/
def secondSegmentLimitKernel (X : ℕ → Ω → ℝ) (μ : Measure Ω) (r : ℝ) : ℝ :=
  ∫ ω, 2 / swingLimitingSlope X r ω ∂μ

/-! ### Pathwise facts -/

omit [MeasurableSpace Ω] in
/-- A positive limiting slope is a genuine supremum, hence dominates the `n = 0` term. -/
theorem neg_le_swingLimitingSlope {r : ℝ} {ω : Ω} (h : 0 < swingLimitingSlope X r ω) :
    -r ≤ swingLimitingSlope X r ω := by
  have hb : BddAbove (range fun n : ℕ => (cumulativeSamples X n ω - r)/((n : ℝ)+1)) := by
    by_contra hb
    have h0 : swingLimitingSlope X r ω = 0 := Real.iSup_of_not_bddAbove hb
    linarith
  unfold swingLimitingSlope
  calc -r = (cumulativeSamples X 0 ω - r)/(((0 : ℕ) : ℝ)+1) := by simp
    _ ≤ _ := le_ciSup hb 0

omit [MeasurableSpace Ω] in
/-- On a regular path, `0 < 2/A_r ≤ 2/|r|` for every negative margin. -/
theorem two_div_swingLimitingSlope_bounds {r : ℝ} {ω : Ω} (hr : r < 0)
    (h : 0 < swingLimitingSlope X r ω) :
    0 < 2 / swingLimitingSlope X r ω ∧ 2 / swingLimitingSlope X r ω ≤ 2 / (-r) := by
  have hle := neg_le_swingLimitingSlope h
  refine ⟨div_pos (by norm_num) h, ?_⟩
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hle

omit [MeasurableSpace Ω] in
/-- On a regular path, `r ↦ 2/A_r` is `2δ⁻²`-Lipschitz on `(-∞, -δ]`. -/
theorem abs_two_div_swingLimitingSlope_sub_le {r s δ : ℝ} {ω : Ω} (hδ : 0 < δ)
    (hr : r ≤ -δ) (hs : s ≤ -δ)
    (hpos : ∀ t, 0 < swingLimitingSlope X t ω)
    (hlip : LipschitzWith 1 (fun t => swingLimitingSlope X t ω)) :
    |2 / swingLimitingSlope X r ω - 2 / swingLimitingSlope X s ω| ≤ 2 / δ^2 * |r - s| := by
  have hAr := neg_le_swingLimitingSlope (hpos r)
  have hAs := neg_le_swingLimitingSlope (hpos s)
  have hAr' : δ ≤ swingLimitingSlope X r ω := by linarith
  have hAs' : δ ≤ swingLimitingSlope X s ω := by linarith
  have hApos := hpos r
  have hBpos := hpos s
  have hd : |swingLimitingSlope X s ω - swingLimitingSlope X r ω| ≤ |r - s| := by
    have := hlip.dist_le_mul s r
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at this
    rw [abs_sub_comm r s]
    exact this
  have heq : 2 / swingLimitingSlope X r ω - 2 / swingLimitingSlope X s ω =
      2 * (swingLimitingSlope X s ω - swingLimitingSlope X r ω) /
        (swingLimitingSlope X r ω * swingLimitingSlope X s ω) := by
    field_simp
  rw [heq, abs_div, abs_mul, abs_of_pos (mul_pos hApos hBpos), abs_two]
  have hprod : δ^2 ≤ swingLimitingSlope X r ω * swingLimitingSlope X s ω := by
    rw [sq]
    exact mul_le_mul hAr' hAs' hδ.le hApos.le
  rw [div_le_iff₀ (mul_pos hApos hBpos)]
  have hδ2 : 0 < δ^2 := by positivity
  have h2 : 2 * |swingLimitingSlope X s ω - swingLimitingSlope X r ω| ≤ 2 * |r - s| := by
    linarith
  calc 2 * |swingLimitingSlope X s ω - swingLimitingSlope X r ω| ≤ 2 * |r - s| := h2
    _ = 2 / δ^2 * |r - s| * δ^2 := by field_simp
    _ ≤ 2 / δ^2 * |r - s| * (swingLimitingSlope X r ω * swingLimitingSlope X s ω) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)

/-! ### The kernel on the negative half-line -/

theorem two_div_swingLimitingSlope_measurable (hX : ∀ n, Measurable (X n)) (r : ℝ) :
    Measurable (fun ω => 2 / swingLimitingSlope X r ω) :=
  (swingLimitingSlope_measurable hX r).const_div 2

theorem two_div_swingLimitingSlope_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    Integrable (fun ω => 2 / swingLimitingSlope X r ω) μ := by
  have := hi.isProbabilityMeasure
  refine (integrable_const (2 / (-r))).mono'
    (two_div_swingLimitingSlope_measurable hX r).aestronglyMeasurable ?_
  filter_upwards [swingLimitingSlope_pos_ae hX hi hG r] with ω hω
  obtain ⟨h1, h2⟩ := two_div_swingLimitingSlope_bounds hr hω
  rw [Real.norm_of_nonneg h1.le]
  exact h2

theorem secondSegmentLimitKernel_nonneg
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    0 ≤ secondSegmentLimitKernel X μ r := by
  apply integral_nonneg_of_ae
  filter_upwards [swingLimitingSlope_pos_ae hX hi hG r] with ω hω
  exact (div_pos (by norm_num) hω).le

/-- `ℓ(r) ≤ 2/|r|` on the negative half-line. -/
theorem secondSegmentLimitKernel_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    secondSegmentLimitKernel X μ r ≤ 2 / |r| := by
  have := hi.isProbabilityMeasure
  rw [abs_of_neg hr]
  have h := integral_mono_ae (two_div_swingLimitingSlope_integrable hX hi hG hr)
    (integrable_const (2 / (-r))) (by
      filter_upwards [swingLimitingSlope_pos_ae hX hi hG r] with ω hω
      exact (two_div_swingLimitingSlope_bounds hr hω).2)
  simpa [secondSegmentLimitKernel] using h

/-- `ℓ(r) > 0` on the negative half-line. -/
theorem secondSegmentLimitKernel_pos
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r : ℝ} (hr : r < 0) :
    0 < secondSegmentLimitKernel X μ r := by
  have := hi.isProbabilityMeasure
  have hint := two_div_swingLimitingSlope_integrable hX hi hG hr
  have hnn : 0 ≤ᵐ[μ] fun ω => 2 / swingLimitingSlope X r ω := by
    filter_upwards [swingLimitingSlope_pos_ae hX hi hG r] with ω hω
    exact (div_pos (by norm_num) hω).le
  unfold secondSegmentLimitKernel
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsupp : ∀ᵐ ω ∂μ, ω ∈ Function.support (fun ω => 2 / swingLimitingSlope X r ω) := by
    filter_upwards [swingLimitingSlope_pos_ae hX hi hG r] with ω hω
    exact (div_pos (by norm_num) hω).ne'
  have hfull : μ (Function.support (fun ω => 2 / swingLimitingSlope X r ω))ᶜ = 0 :=
    ae_iff.mp hsupp
  have hm : MeasurableSet (Function.support (fun ω => 2 / swingLimitingSlope X r ω)) :=
    measurableSet_support (two_div_swingLimitingSlope_measurable hX r)
  rw [measure_compl hm (measure_ne_top _ _), measure_univ] at hfull
  have hle : μ (Function.support (fun ω => 2 / swingLimitingSlope X r ω)) ≤ 1 := prob_le_one
  have hne : μ (Function.support (fun ω => 2 / swingLimitingSlope X r ω)) ≠ 0 := by
    intro h0
    rw [h0, tsub_zero] at hfull
    exact one_ne_zero hfull
  exact pos_iff_ne_zero.mpr hne

/-- C2.5: `ℓ` is `2δ⁻²`-Lipschitz on `(-∞, -δ]`. -/
theorem abs_secondSegmentLimitKernel_sub_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {r s δ : ℝ} (hδ : 0 < δ)
    (hr : r ≤ -δ) (hs : s ≤ -δ) :
    |secondSegmentLimitKernel X μ r - secondSegmentLimitKernel X μ s| ≤ 2 / δ^2 * |r - s| := by
  have := hi.isProbabilityMeasure
  have hir := two_div_swingLimitingSlope_integrable hX hi hG
    (lt_of_le_of_lt hr (neg_lt_zero.mpr hδ))
  have his := two_div_swingLimitingSlope_integrable hX hi hG
    (lt_of_le_of_lt hs (neg_lt_zero.mpr hδ))
  unfold secondSegmentLimitKernel
  rw [← integral_sub hir his]
  calc |∫ ω, (2 / swingLimitingSlope X r ω - 2 / swingLimitingSlope X s ω) ∂μ|
      ≤ ∫ ω, |2 / swingLimitingSlope X r ω - 2 / swingLimitingSlope X s ω| ∂μ :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _ω, 2 / δ^2 * |r - s| ∂μ := by
        refine integral_mono_ae (hir.sub his).abs (integrable_const _) ?_
        filter_upwards [swingLimitingSlope_all_margins_ae hX hi hG] with ω hω
        exact abs_two_div_swingLimitingSlope_sub_le hδ hr hs hω.1 hω.2.1
    _ = 2 / δ^2 * |r - s| := by simp

/-- `ℓ` is continuous on the open negative half-line. -/
theorem secondSegmentLimitKernel_continuousOn
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ContinuousOn (secondSegmentLimitKernel X μ) (Iio 0) := by
  intro r hr
  have hr' : r < 0 := hr
  set δ : ℝ := -r/2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hlip : LipschitzOnWith (Real.toNNReal (2 / δ^2)) (secondSegmentLimitKernel X μ)
      (Iic (-δ)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    exact abs_secondSegmentLimitKernel_sub_le hX hi hG hδ hx hy
  have hmem : Iic (-δ) ∈ 𝓝 r := Iic_mem_nhds (by rw [hδdef]; linarith)
  exact (hlip.continuousOn.continuousAt hmem).continuousWithinAt

/-- `ℓ` is jointly measurable as a parametric integral. -/
theorem secondSegmentLimitKernel_stronglyMeasurable [SFinite μ]
    (hX : ∀ n, Measurable (X n)) :
    StronglyMeasurable (secondSegmentLimitKernel X μ) := by
  have hj : StronglyMeasurable (Function.uncurry fun (r : ℝ) (ω : Ω) =>
      2 / swingLimitingSlope X r ω) :=
    ((swingLimitingSlope_joint_measurable hX).const_div 2).stronglyMeasurable
  exact hj.integral_prod_right

/-! ### Reflection: the frozen slope has the same mean kernel -/

/-- The frozen magnitude is the limiting slope of the reflected walk, whose law is
the original one; hence `E[2/frozenSlopeMagnitude X r] = ℓ(r)`. -/
theorem integral_two_div_frozenSlopeMagnitude
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (r : ℝ) :
    (∫ ω, 2 / frozenSlopeMagnitude X r ω ∂μ) = secondSegmentLimitKernel X μ r := by
  let coord : ℕ → (ℕ → ℝ) → ℝ := fun j z => z j
  have hcoord : ∀ j, Measurable (coord j) := fun j => measurable_pi_apply j
  set Φ : (ℕ → ℝ) → ℝ := fun z => 2 / swingLimitingSlope coord r z with hΦdef
  have hΦ : Measurable Φ := (swingLimitingSlope_measurable hcoord r).const_div 2
  have hid := (negSequence_identDistrib hX hi hG).comp hΦ
  have hint := hid.integral_eq
  have hneg : ∀ ω, Φ (fun j => -X j ω) = 2 / frozenSlopeMagnitude X r ω := by
    intro ω
    have h1 : swingLimitingSlope coord r (fun j => -X j ω) =
        swingLimitingSlope (fun n ω => -X n ω) r ω := rfl
    have h2 := swingLimitingSlope_eq_frozen_reflection (fun n ω => -X n ω) r ω
    simp only [neg_neg] at h2
    simp only [hΦdef, h1, h2]
  have hpos : ∀ ω, Φ (fun j => X j ω) = 2 / swingLimitingSlope X r ω := fun ω => rfl
  calc (∫ ω, 2 / frozenSlopeMagnitude X r ω ∂μ) = ∫ ω, Φ (fun j => -X j ω) ∂μ := by
        simp only [hneg]
    _ = ∫ ω, Φ (fun j => X j ω) ∂μ := by simpa only [Function.comp_def] using hint
    _ = secondSegmentLimitKernel X μ r := by simp only [hpos]; rfl

end SwingRepair
