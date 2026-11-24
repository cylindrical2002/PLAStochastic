import PLAStochastic.Swing.ConstantEvaluation.Fluctuation.LadderMeanBound
import PLAStochastic.Swing.Gaussian.HalfLine.SmallDriftOvershootMean

/-! # The ascending ladder height at small drift

For drifts `a ≤ 1/2` (in particular on `[0, 1/2]`) the strict ascending ladder height
`H_a` of the Gaussian walk with drift `a` has a second moment bounded independently
of `a`: before the ladder epoch the walk is `≤ 0`, so the crossing increment is a
Gaussian excess over a level `≥ -1/2`, whose moments are uniformly bounded
(`gaussianExcessLaw_uniform_moments`).  The library proves this bound for the
half-line exit with nonnegative drift; the same slice argument only needs the drift
to be at least `-1/2`, which is what the ascending height needs (`H_a` is the
half-line overshoot of `-X` with drift `-a`).

Consequences:

* `gaussianAscendingLadderHeight_sq_lintegral_le`: `𝔼H_a² ≤ C₂` for `a ≤ 1/2`;
* `tendsto_lintegral_abs_ladderHeight_sub_zero`: along any `a_k → 0` with `a_k ≤ 1/2`,
  `𝔼|H_{a_k} - H_0| → 0` (Vitali: pathwise convergence plus the uniform second moment).
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-! ### The half-line slice bound for drift `≥ -1/2` -/

/-- One exit slice: the overshoot is a fresh Gaussian excess over a level `≥ -1/2`
whenever the drift is `≥ -1/2`. -/
theorem gaussianHalfLineExitSlice_lintegral_le_of_ge
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (ha : -(1/2 : ℝ) ≤ a) (n : ℕ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in gaussianHalfLineExitSlice X x a n, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤
      C * μ (gaussianHalfLineExitSlice X x a n) := by
  have := hi.isProbabilityMeasure
  let r := fun ω => gaussianDriftWalk X x a n ω + a
  have hr : Measurable[incrementIndexSpace X (Iio n)] r :=
    (gaussianDriftWalk_measurable_past X x a n).add_const a
  have hnegG : μ.map (fun ω => -X n ω) = gaussianReal 0 1 := by
    calc
      _ = (μ.map (X n)).map (fun z : ℝ => -z) :=
        (Measure.map_map measurable_neg (hX n)).symm
      _ = _ := by rw [hG, gaussianReal_map_neg, neg_zero]
  have hnegMeas : Measurable[MeasurableSpace.comap (X n) inferInstance] (fun ω => -X n ω) :=
    (show Measurable[MeasurableSpace.comap (X n) inferInstance] (X n) from
      measurable_iff_comap_le.mpr le_rfl).neg
  have hnegInd := indep_of_indep_of_le_left (currentIncrement_indep_past hX hi n) hnegMeas.comap_le
  have he : gaussianHalfLineExitSlice X x a n =
      gaussianHalfLineSurvives X x a n ∩ {ω | r ω < -X n ω} := by
    ext ω
    change (ω ∈ gaussianHalfLineSurvives X x a n ∧ gaussianDriftWalk X x a (n + 1) ω < 0) ↔ _
    rw [gaussianDriftWalk_succ]
    change (_ ∧ _ < 0) ↔ (_ ∧ r ω < -X n ω)
    dsimp only [r]
    constructor <;> rintro ⟨hs, ho⟩ <;> exact ⟨hs, by linarith⟩
  have ho : ∀ ω ∈ gaussianHalfLineExitSlice X x a n,
      gaussianHalfLineOvershoot X x a ω = -X n ω - r ω := by
    intro ω hω
    rw [gaussianHalfLineOvershoot_of_slice hω, gaussianDriftWalk_succ]
    dsimp only [r]
    ring
  calc
    _ = ∫⁻ ω in gaussianHalfLineExitSlice X x a n, f (-X n ω-r ω) ∂μ :=
      setLIntegral_congr_fun (gaussianHalfLineExitSlice_measurable hX x a n)
        (fun ω hω => congrArg f (ho ω hω))
    _ ≤ _ := by
      rw [he]
      apply past_freshGaussian_excess_lintegral_le (incrementIndexSpace_le hX _) (hX n).neg
        hnegG hnegInd hr (gaussianHalfLineSurvives_measurable_past X x a n) _ hf hC hb
      intro ω hω
      have hs := hω n le_rfl
      dsimp only [r]
      linarith

/-- The finite-exit event: the slices sum up. -/
theorem gaussianHalfLineFinite_lintegral_le_of_ge
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : -(1/2 : ℝ) ≤ a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω in {ω | gaussianHalfLineExit X x a ω ≠ ⊤}, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤
      C * μ {ω | gaussianHalfLineExit X x a ω ≠ ⊤} := by
  rw [gaussianHalfLineFinite_eq_iUnion hx,
    lintegral_iUnion (gaussianHalfLineExitSlice_measurable hX x a)
      (gaussianHalfLineExitSlice_disjoint X x a),
    measure_iUnion (gaussianHalfLineExitSlice_disjoint X x a)
      (gaussianHalfLineExitSlice_measurable hX x a), ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum (fun n =>
    gaussianHalfLineExitSlice_lintegral_le_of_ge hX hi hG ha n hf hC hb)

/-- The whole-space bound for `f` vanishing at `0` (the overshoot is `0` when there is no exit). -/
theorem gaussianHalfLineOvershoot_lintegral_le_of_ge
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a : ℝ} (hx : 0 ≤ x) (ha : -(1/2 : ℝ) ≤ a)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hf0 : f 0 = 0)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ r : ℝ, -(1/2 : ℝ) ≤ r → (∫⁻ u, f u ∂gaussianExcessLaw r) ≤ C) :
    (∫⁻ ω, f (gaussianHalfLineOvershoot X x a ω) ∂μ) ≤ C := by
  have := hi.isProbabilityMeasure
  have hm : MeasurableSet {ω | gaussianHalfLineExit X x a ω ≠ ⊤} :=
    ((gaussianHalfLineExit_isStoppingTime hX x a).measurable' (measurableSet_singleton ⊤)).compl
  have he : ∀ ω, f (gaussianHalfLineOvershoot X x a ω) =
      {ω | gaussianHalfLineExit X x a ω ≠ ⊤}.indicator
        (fun ω => f (gaussianHalfLineOvershoot X x a ω)) ω := by
    intro ω
    by_cases hω : gaussianHalfLineExit X x a ω = ⊤
    · simp [hω, gaussianHalfLineOvershoot, hf0]
    · simp [hω]
  calc
    _ = ∫⁻ ω in {ω | gaussianHalfLineExit X x a ω ≠ ⊤},
        f (gaussianHalfLineOvershoot X x a ω) ∂μ := by
      calc
        _ = ∫⁻ ω, {ω | gaussianHalfLineExit X x a ω ≠ ⊤}.indicator
            (fun ω => f (gaussianHalfLineOvershoot X x a ω)) ω ∂μ := lintegral_congr he
        _ = _ := lintegral_indicator hm _
    _ ≤ C * μ {ω | gaussianHalfLineExit X x a ω ≠ ⊤} :=
      gaussianHalfLineFinite_lintegral_le_of_ge hX hi hG hx ha hf hC hb
    _ ≤ C * 1 := by gcongr; exact prob_le_one
    _ = C := mul_one _

/-! ### The ascending ladder height -/

/-- **Uniform second moment at small drift**: `𝔼H_a² ≤ C₂` for every `a ≤ 1/2`. -/
theorem gaussianAscendingLadderHeight_sq_lintegral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : a ≤ 1/2) :
    (∫⁻ ω, ENNReal.ofReal (gaussianAscendingLadderHeight X a ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (gaussianExcessExpMomentBound 2) := by
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  unfold gaussianAscendingLadderHeight
  exact gaussianHalfLineOvershoot_lintegral_le_of_ge hXn hin hGn le_rfl (by linarith)
    (f := fun u => ENNReal.ofReal (u ^ 2)) (by fun_prop) (by norm_num) ENNReal.ofReal_ne_top
    (fun r hr => by
      have hm := (gaussianExcessLaw_uniform_moments hr).2.1
      rw [← ofReal_integral_eq_lintegral_ofReal hm.1 (ae_of_all _ (fun u => sq_nonneg u))]
      exact ENNReal.ofReal_le_ofReal hm.2)

theorem gaussianAscendingLadderHeight_sq_integrable_of_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : a ≤ 1/2) :
    Integrable (fun ω => gaussianAscendingLadderHeight X a ω ^ 2) μ := by
  have hm : Measurable fun ω => gaussianAscendingLadderHeight X a ω ^ 2 :=
    (gaussianAscendingLadderHeight_measurable hX a).pow_const 2
  refine (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable
    (ae_of_all _ fun ω => sq_nonneg _)).mp ?_
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (gaussianAscendingLadderHeight_sq_lintegral_le hX hi hG ha)

/-- **`L¹` convergence at the zero-drift boundary**: along any `a_k → 0` with
`a_k ≤ 1/2`, `𝔼|H_{a_k} - H_0| → 0`. -/
theorem tendsto_lintegral_abs_ladderHeight_sub_zero
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℕ → ℝ} (ha : ∀ k, a k ≤ 1/2)
    (hlim : Tendsto a atTop (𝓝 0)) :
    Tendsto (fun k => ∫⁻ ω, ENNReal.ofReal
        |gaussianAscendingLadderHeight X (a k) ω - gaussianAscendingLadderHeight X 0 ω| ∂μ)
      atTop (𝓝 0) := by
  have := hi.isProbabilityMeasure
  obtain ⟨hXn, hin, hGn⟩ := iidGaussian_neg hX hi hG
  have hmeas : ∀ k, AEStronglyMeasurable (gaussianAscendingLadderHeight X (a k)) μ :=
    fun k => (gaussianAscendingLadderHeight_measurable hX (a k)).aestronglyMeasurable
  have hui : UniformIntegrable (fun k => gaussianAscendingLadderHeight X (a k)) 1 μ :=
    BrownianAffine.uniformIntegrable_of_uniform_second_moment hmeas
      (gaussianExcessExpMomentBound_pos 2).le
      (fun k => gaussianAscendingLadderHeight_sq_lintegral_le hX hi hG (ha k))
  have hneg : Tendsto (fun k => -a k) atTop (𝓝 0) := by
    simpa using hlim.neg
  have hc : ∀ᵐ ω ∂μ, Tendsto (fun k => gaussianAscendingLadderHeight X (a k) ω) atTop
      (𝓝 (gaussianAscendingLadderHeight X 0 ω)) := by
    filter_upwards [gaussianHalfLine_small_drift_ae hXn hin hGn (x := fun _ : ℕ => (0 : ℝ))
      (a := fun k => -a k) (w := 0) tendsto_const_nhds hneg
      (Eventually.of_forall fun _ => le_rfl) le_rfl] with ω hω
    rw [gaussianAscendingLadderHeight_zero_eq]
    exact hω.2
  have hL := tendsto_Lp_finite_of_tendsto_ae le_rfl (by norm_num) hmeas
    (hui.memLp_of_ae_tendsto hc) hui.2.1 hc
  refine hL.congr fun k => ?_
  rw [eLpNorm_one_eq_lintegral_enorm]
  refine lintegral_congr fun ω => ?_
  rw [Pi.sub_apply, Real.enorm_eq_ofReal_abs]

end SwingRepair
