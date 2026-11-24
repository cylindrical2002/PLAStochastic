import PLAStochastic.Swing.Ladder.Drift.PathwiseContinuity

/-! # `L¹` continuity of the ladder height in the drift

Pointwise continuity plus the already proved uniform second moment give
`E|H_{a'} - H_a| → 0`, and hence the `L¹` convergence of the ladder tails that
the equilibrium overshoot density is built from.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- Above a level the excess is dominated by the square over the level. -/
theorem max_sub_le_sq_div {u T : ℝ} (hu : 0 ≤ u) (hT : 0 < T) :
    max (u - T) 0 ≤ u^2/T := by
  rcases le_total u T with h | h
  · rw [max_eq_right (by linarith)]
    positivity
  · rw [max_eq_left (by linarith)]
    rw [le_div_iff₀ hT]
    nlinarith

/-- The truncation tail is uniformly small on a compact positive drift interval. -/
theorem gaussianAscendingLadderHeight_truncation_tail_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ M a : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a) (haM : a ≤ M) {T : ℝ} (hT : 0 < T) :
    (∫ ω, max (gaussianAscendingLadderHeight X a ω - T) 0 ∂μ) ≤
      gaussianAscendingLadderMomentBound δ M 2 / T := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hsq := gaussianAscendingLadderHeight_pow_integrable hX hi hG hδ hδa haM 2
  have hmajor : Integrable
      (fun ω => gaussianAscendingLadderHeight X a ω ^ 2 / T) μ := hsq.div_const T
  have hmeas : Measurable (fun ω => max (gaussianAscendingLadderHeight X a ω - T) 0) :=
    ((gaussianAscendingLadderHeight_measurable hX a).sub measurable_const).max measurable_const
  have hpoint : ∀ ω, max (gaussianAscendingLadderHeight X a ω - T) 0 ≤
      gaussianAscendingLadderHeight X a ω ^ 2 / T :=
    fun ω => max_sub_le_sq_div (gaussianAscendingLadderHeight_nonneg (X := X) a ω) hT
  have hint : Integrable (fun ω => max (gaussianAscendingLadderHeight X a ω - T) 0) μ := by
    refine hmajor.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hpoint ω
  calc (∫ ω, max (gaussianAscendingLadderHeight X a ω - T) 0 ∂μ)
      ≤ ∫ ω, gaussianAscendingLadderHeight X a ω ^ 2 / T ∂μ :=
        integral_mono hint hmajor hpoint
    _ = (∫ ω, gaussianAscendingLadderHeight X a ω ^ 2 ∂μ)/T := by
        rw [integral_div]
    _ ≤ gaussianAscendingLadderMomentBound δ M 2 / T :=
        div_le_div_of_nonneg_right
          (gaussianAscendingLadderHeight_pow_integral_le hX hi hG hδ hδa haM 2) hT.le

omit [MeasurableSpace Ω] in
/-- Splitting an absolute difference at a truncation level. -/
theorem abs_sub_le_truncated_add_tails (u v T : ℝ) :
    |u - v| ≤ |min u T - min v T| + max (u - T) 0 + max (v - T) 0 := by
  rcases le_total u T with hu' | hu' <;> rcases le_total v T with hv' | hv'
  · rw [min_eq_left hu', min_eq_left hv', max_eq_right (by linarith),
      max_eq_right (by linarith)]
    simp
  · rw [min_eq_left hu', min_eq_right hv', max_eq_right (by linarith),
      max_eq_left (by linarith)]
    rw [abs_sub_comm u T]
    rcases le_total u T with h | h <;>
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ T - u)] <;>
      rcases le_total u v with h2 | h2
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_right hu', min_eq_left hv', max_eq_left (by linarith),
      max_eq_right (by linarith)]
    rcases le_total u v with h2 | h2
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_right hu', min_eq_right hv', max_eq_left (by linarith),
      max_eq_left (by linarith)]
    simp only [sub_self, abs_zero, zero_add]
    rcases le_total u v with h2 | h2
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith

/-- The truncated ladder heights converge in `L¹` by dominated convergence. -/
theorem gaussianAscendingLadderHeight_truncated_l1_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    Tendsto (fun a' : ℝ => ∫ ω, |min (gaussianAscendingLadderHeight X a' ω) T -
        min (gaussianAscendingLadderHeight X a ω) T| ∂μ) (𝓝 a) (𝓝 0) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hzero : (∫ _ω : Ω, (0 : ℝ) ∂μ) = 0 := integral_zero _ _
  rw [← hzero]
  refine tendsto_integral_filter_of_dominated_convergence (bound := fun _ : Ω => 2*|T|) ?_ ?_ ?_ ?_
  · filter_upwards with a'
    exact ((((gaussianAscendingLadderHeight_measurable hX a').min measurable_const).sub
      ((gaussianAscendingLadderHeight_measurable hX a).min measurable_const)).abs).aestronglyMeasurable
  · filter_upwards with a'
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_abs]
    have h1 : |min (gaussianAscendingLadderHeight X a' ω) T| ≤ |T| := by
      rcases le_total (gaussianAscendingLadderHeight X a' ω) T with h | h
      · rw [min_eq_left h, abs_of_nonneg (gaussianAscendingLadderHeight_nonneg (X := X) a' ω)]
        exact le_trans h (le_abs_self T)
      · rw [min_eq_right h]
    have h2 : |min (gaussianAscendingLadderHeight X a ω) T| ≤ |T| := by
      rcases le_total (gaussianAscendingLadderHeight X a ω) T with h | h
      · rw [min_eq_left h, abs_of_nonneg (gaussianAscendingLadderHeight_nonneg (X := X) a ω)]
        exact le_trans h (le_abs_self T)
      · rw [min_eq_right h]
    calc |min (gaussianAscendingLadderHeight X a' ω) T -
            min (gaussianAscendingLadderHeight X a ω) T|
        ≤ |min (gaussianAscendingLadderHeight X a' ω) T| +
            |min (gaussianAscendingLadderHeight X a ω) T| := abs_sub _ _
      _ ≤ 2*|T| := by linarith
  · exact integrable_const _
  · filter_upwards [gaussianAscendingLadderHeight_tendsto_ae hX hi hG ha] with ω hω
    have hmin : Tendsto (fun a' : ℝ => min (gaussianAscendingLadderHeight X a' ω) T) (𝓝 a)
        (𝓝 (min (gaussianAscendingLadderHeight X a ω) T)) :=
      (continuous_id.min continuous_const).continuousAt.tendsto.comp hω
    have hsub := hmin.sub (tendsto_const_nhds
      (x := min (gaussianAscendingLadderHeight X a ω) T) (f := 𝓝 a))
    simpa using hsub.abs

omit [MeasurableSpace Ω] in
theorem abs_min_le_add (u T : ℝ) : |min u T| ≤ |u| + |T| := by
  rcases le_total u T with h | h
  · rw [min_eq_left h]
    linarith [abs_nonneg T]
  · rw [min_eq_right h]
    linarith [abs_nonneg u]

omit [MeasurableSpace Ω] in
theorem abs_max_sub_le (u T : ℝ) : |max (u - T) 0| ≤ |u - T| := by
  rcases le_total (u - T) 0 with h | h
  · rw [max_eq_right h, abs_zero]
    exact abs_nonneg _
  · rw [max_eq_left h]

/-- `L¹` continuity of the ladder height in the drift. -/
theorem gaussianAscendingLadderHeight_l1_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun a' : ℝ => ∫ ω, |gaussianAscendingLadderHeight X a' ω -
        gaussianAscendingLadderHeight X a ω| ∂μ) (𝓝 a) (𝓝 0) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set δ : ℝ := a/2 with hδdef
  set M : ℝ := 2*a with hMdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have haδ : δ ≤ a := by rw [hδdef]; linarith
  have haM : a ≤ M := by rw [hMdef]; linarith
  set B : ℝ := gaussianAscendingLadderMomentBound δ M 2 with hBdef
  have hB : 0 ≤ B := by
    have h1 : (0 : ℝ) ≤ ∫ ω, gaussianAscendingLadderHeight X a ω ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg _)
    exact h1.trans (gaussianAscendingLadderHeight_pow_integral_le hX hi hG hδ haδ haM 2)
  have hone : ∀ b : ℝ, δ ≤ b → b ≤ M → Integrable (gaussianAscendingLadderHeight X b) μ := by
    intro b hb1 hb2
    have h := gaussianAscendingLadderHeight_pow_integrable hX hi hG hδ hb1 hb2 1
    refine h.congr ?_
    filter_upwards with ω
    rw [pow_one]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set T : ℝ := max 1 (8*B/ε) with hTdef
  have hT1 : (1 : ℝ) ≤ T := le_max_left _ _
  have hT : 0 < T := lt_of_lt_of_le one_pos hT1
  have hTbig : 8*B/ε ≤ T := le_max_right _ _
  have hBT : 2*(B/T) ≤ ε/4 := by
    rw [div_le_iff₀ hε] at hTbig
    have hkey : 2*(B/T) = 2*B/T := by ring
    rw [hkey, div_le_iff₀ hT]
    nlinarith
  have hnbhd : ∀ᶠ a' : ℝ in 𝓝 a, a' ∈ Ioo δ M := by
    refine IsOpen.mem_nhds isOpen_Ioo ?_
    exact ⟨by rw [hδdef]; linarith, by rw [hMdef]; linarith⟩
  have hdct := gaussianAscendingLadderHeight_truncated_l1_tendsto hX hi hG ha T
  rw [Metric.tendsto_nhds] at hdct
  filter_upwards [hnbhd, hdct (ε/2) (by linarith)] with a' hmem hsmall
  have hint1 : Integrable (gaussianAscendingLadderHeight X a') μ :=
    hone a' hmem.1.le hmem.2.le
  have hint2 : Integrable (gaussianAscendingLadderHeight X a) μ := hone a haδ haM
  have hmin : ∀ b : ℝ, Integrable (gaussianAscendingLadderHeight X b) μ →
      Integrable (fun ω => min (gaussianAscendingLadderHeight X b ω) T) μ := by
    intro b hb
    refine Integrable.mono' (hb.abs.add (integrable_const |T|))
      ((gaussianAscendingLadderHeight_measurable hX b).min
        measurable_const).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_min_le_add _ _
  have hmaxint : ∀ b : ℝ, Integrable (gaussianAscendingLadderHeight X b) μ →
      Integrable (fun ω => max (gaussianAscendingLadderHeight X b ω - T) 0) μ := by
    intro b hb
    have hmaj : Integrable (fun ω => |gaussianAscendingLadderHeight X b ω - T|) μ :=
      (hb.sub (integrable_const T)).abs
    refine Integrable.mono' hmaj
      (((gaussianAscendingLadderHeight_measurable hX b).sub
        measurable_const).max measurable_const).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_max_sub_le _ _
  have hdiff : Integrable (fun ω => |gaussianAscendingLadderHeight X a' ω -
      gaussianAscendingLadderHeight X a ω|) μ := (hint1.sub hint2).abs
  have htrunc : Integrable (fun ω => |min (gaussianAscendingLadderHeight X a' ω) T -
      min (gaussianAscendingLadderHeight X a ω) T| ) μ :=
    ((hmin a' hint1).sub (hmin a hint2)).abs
  have htail1 := hmaxint a' hint1
  have htail2 := hmaxint a hint2
  have hmono : (∫ ω, |gaussianAscendingLadderHeight X a' ω -
      gaussianAscendingLadderHeight X a ω| ∂μ) ≤
      (∫ ω, |min (gaussianAscendingLadderHeight X a' ω) T -
        min (gaussianAscendingLadderHeight X a ω) T| ∂μ) +
      (∫ ω, max (gaussianAscendingLadderHeight X a' ω - T) 0 ∂μ) +
      (∫ ω, max (gaussianAscendingLadderHeight X a ω - T) 0 ∂μ) := by
    have hsum1 : Integrable (fun ω =>
        |min (gaussianAscendingLadderHeight X a' ω) T -
          min (gaussianAscendingLadderHeight X a ω) T| +
        max (gaussianAscendingLadderHeight X a' ω - T) 0) μ := htrunc.add htail1
    have hsum : Integrable (fun ω =>
        (|min (gaussianAscendingLadderHeight X a' ω) T -
          min (gaussianAscendingLadderHeight X a ω) T| +
        max (gaussianAscendingLadderHeight X a' ω - T) 0) +
        max (gaussianAscendingLadderHeight X a ω - T) 0) μ := hsum1.add htail2
    have hpt := integral_mono hdiff hsum (fun ω =>
      abs_sub_le_truncated_add_tails (gaussianAscendingLadderHeight X a' ω)
        (gaussianAscendingLadderHeight X a ω) T)
    rw [integral_add hsum1 htail2, integral_add htrunc htail1] at hpt
    exact hpt
  have ht1 := gaussianAscendingLadderHeight_truncation_tail_le hX hi hG hδ hmem.1.le hmem.2.le hT
  have ht2 := gaussianAscendingLadderHeight_truncation_tail_le hX hi hG hδ haδ haM hT
  rw [← hBdef] at ht1 ht2
  have hnn : (0 : ℝ) ≤ ∫ ω, |gaussianAscendingLadderHeight X a' ω -
      gaussianAscendingLadderHeight X a ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
  have hs : (∫ ω, |min (gaussianAscendingLadderHeight X a' ω) T -
      min (gaussianAscendingLadderHeight X a ω) T| ∂μ) < ε/2 := by
    have h := hsmall
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg (fun ω => abs_nonneg _))] at h
    exact h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  have hsplit : B/T + B/T = 2*(B/T) := by ring
  linarith

end SwingRepair
