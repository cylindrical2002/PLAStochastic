import PLAStochastic.Swing.SecondSegment.Coefficient.Remainder
import PLAStochastic.ForMathlib.Probability.Kernel.Invariant.WeakPropagation

/-! # The second-segment coefficient along a convergent entrance filter

`second-coefficient.md`, C2.1.  Let `ρ_{1,E} = Law(R_{1,E})` be the law of the
actual first margin, and suppose `ρ_{1,E} ⇒ ν` along a filter on which the
budget tends to `+∞`.  Then

`E L_{2,E} / E → ∫ ℓ dν`,  `ℓ(r) = E[2/A_r]`,

and the limit `ν` is carried by `(-∞, 0)`, has no atom at `0`, integrates `ℓ`,
and gives a strictly positive coefficient.

The proof writes `E L_{2,E}/E = ∫ g_E/E dρ_{1,E}` and splits with the window
`ψ` of `Window`: the windowed part converges by the uniform convergence C2.2
and weak convergence against the bounded continuous `ℓψ`; the remainders off
the window are bounded in `Remainder` by quantities that vanish as first the
budget grows and then `M → ∞`, `δ → 0`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- **C2.1.**  Along every filter on which the budget tends to `+∞` and the law of
the actual first margin converges weakly to `ν`, the normalised mean of the
actual second segment converges to `∫ ℓ dν`. -/
theorem secondSegment_normalizedMean_tendsto
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {budget : ι → ℝ}
    (hbudget_top : Tendsto budget l atTop) {ν : ProbabilityMeasure ℝ}
    (hν : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    Tendsto (fun i => (∫ ω, (nativeRecordingDurationNat X (budget i) 1 ω : ℝ) ∂μ) / budget i) l
      (𝓝 (∫ r, secondSegmentLimitKernel X μ r ∂(ν : Measure ℝ))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hν' : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν) := hν
  set ℓ : ℝ → ℝ := secondSegmentLimitKernel X μ with hℓdef
  set C1 : ℝ := nativeFirstMarginConcentrationConstant 1 with hC1def
  set m1 : ℝ := nativeFirstMarginMomentBound 1 with hm1def
  set K : ℝ := frozenNegativeCarryLogConstant with hKdef
  set Ku : ℝ := frozenUniformMeanConstant with hKudef
  set Cq : ℝ := firstMarginNonnegConstant + secondMarginPosConstant with hCqdef
  have hC1 : 0 ≤ C1 := nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hm1 : 0 ≤ m1 := nativeFirstMarginMomentBound_nonneg 1
  have hK : 0 < K := frozenNegativeCarryLogConstant_pos
  have hKu : 0 < Ku := frozenUniformMeanConstant_pos
  have hCq : 0 ≤ Cq := by
    have := secondMarginPosConstant_nonneg
    rw [hCqdef]
    unfold firstMarginNonnegConstant
    positivity
  -- the limit law
  have hνneg := firstMarginLimit_ae_neg hX hi hG hbudget_top hν'
  have hνball : ∀ s, 0 < s → s ≤ 1 →
      (ν : Measure ℝ) {r : ℝ | |r| < s} ≤ ENNReal.ofReal (2*C1*s) :=
    fun s hs hs1 => firstMarginLimit_ball_le hX hi hG hbudget_top hν' hs.le hs1
  have hℓint : Integrable ℓ (ν : Measure ℝ) :=
    secondSegmentLimitKernel_integrable_of_ball hX hi hG hνneg hC1 hνball
  -- the normalised mean as an integral against the first margin law
  have hq : (fun i => ∫ r, secondSegmentFrozenMean X μ (budget i) r / budget i
        ∂(nativeTransientMarginProb μ hX (budget i) 1 : Measure ℝ)) =ᶠ[l]
      fun i => (∫ ω, (nativeRecordingDurationNat X (budget i) 1 ω : ℝ) ∂μ) / budget i := by
    filter_upwards [hbudget_top.eventually (eventually_gt_atTop 0)] with i hi0
    rw [nativeTransientMarginProb_coe]
    exact (secondSegment_normalizedMean_eq_integral hX hi hG hi0).symm
  refine Tendsto.congr' hq ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- the far cutoff
  set M : ℝ := 1 + 200 * m1 / ε with hMdef
  have hM1 : 1 ≤ M := by
    have : 0 ≤ 200 * m1 / ε := by positivity
    rw [hMdef]
    linarith
  have hMfar : 25 * (m1 / M) ≤ ε/8 := by
    have hM0 : 0 < M := by linarith
    rw [← mul_div_assoc, div_le_iff₀ hM0, hMdef]
    have : ε/8 * (1 + 200 * m1 / ε) = ε/8 + 25 * m1 := by field_simp; ring
    rw [this]
    linarith
  -- the zero neighbourhood
  set η : ℝ := ε / (48 * (K * C1 + 1)) with hηdef
  have hη : 0 < η := by positivity
  set δ : ℝ := min 1 (η^2) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hsqrtδ : Real.sqrt δ ≤ η := by
    calc Real.sqrt δ ≤ Real.sqrt (η^2) := Real.sqrt_le_sqrt (min_le_right _ _)
      _ = η := Real.sqrt_sq hη.le
  have hδsqrt : δ ≤ Real.sqrt δ := by
    have h1 : Real.sqrt δ ≤ 1 := by
      rw [Real.sqrt_le_one]
      exact hδ1
    have h2 : δ = Real.sqrt δ * Real.sqrt δ := (Real.mul_self_sqrt hδ0.le).symm
    nlinarith [Real.sqrt_nonneg δ]
  have hnear : K * (2*C1*δ + 4*C1*Real.sqrt δ) ≤ ε/8 := by
    have h1 : 2*C1*δ + 4*C1*Real.sqrt δ ≤ 6*C1*η := by nlinarith
    have hηeq : η * (48 * (K * C1 + 1)) = ε := by rw [hηdef]; field_simp
    calc K * (2*C1*δ + 4*C1*Real.sqrt δ) ≤ K * (6*C1*η) := mul_le_mul_of_nonneg_left h1 hK.le
      _ ≤ ε/8 := by nlinarith [mul_nonneg (mul_nonneg hK.le hC1) hη.le]
  -- the eventual estimates
  have hunif := (Metric.tendstoUniformlyOn_iff.mp
    (secondSegmentFrozenMean_tendstoUniformlyOn hX hi hG (δ := δ/2) (M := M+1)
      (by positivity))) (ε/8) (by positivity)
  have hunif' := hbudget_top.eventually hunif
  set g : ℝ → ℝ := fun r => ℓ r * secondSegmentWindow δ M r with hgdef
  have hgc : Continuous g := continuous_secondSegmentLimitKernel_mul_window hX hi hG hδ0 M
  have hgb : ∀ r, |g r| ≤ 4/δ := abs_secondSegmentLimitKernel_mul_window_le hX hi hG hδ0 M
  have hweak := KernelLimit.tendsto_integral_of_tendsto hν' g (4/δ) hgc hgb
  have hweak' := hweak.eventually (Metric.ball_mem_nhds _ (show (0 : ℝ) < ε/8 by positivity))
  have hlogS := (tendsto_one_add_log_div_sqrt_sqrt.comp hbudget_top).const_mul (Ku * Cq)
  rw [mul_zero] at hlogS
  have hpos' := hlogS.eventually (Iio_mem_nhds (show (0 : ℝ) < ε/8 by positivity))
  filter_upwards [hunif', hweak', hpos', hbudget_top.eventually (eventually_ge_atTop (16 : ℝ))]
    with i hu hw hp h16
  simp only [Function.comp_apply] at hp
  rw [Real.dist_eq] at hw
  set E : ℝ := budget i with hEdef
  set ρ : Measure ℝ := (nativeTransientMarginProb μ hX E 1 : Measure ℝ) with hρdef
  have hρeq : ρ = nativeTransientMarginLaw X μ E 1 := rfl
  set f : ℝ → ℝ := fun r => secondSegmentFrozenMean X μ E r / E with hfdef
  set ψ : ℝ → ℝ := secondSegmentWindow δ M with hψdef
  obtain ⟨hfint, hR1⟩ := integral_frozenMean_mul_one_sub_window_le hX hi hG h16 hδ0 hδ1 hM1
  have hR2 := integral_kernel_mul_one_sub_window_le hX hi hG hνneg hC1 hνball hδ0 hδ1 hM1
    (T := m1 / M) (by positivity) (firstMarginLimit_Iio_le hX hi hG hbudget_top hν' (by linarith))
  rw [← hρeq] at hfint hR1
  have hE0 : 0 < E := by linarith
  have hf0 : ∀ r, 0 ≤ f r := fun r => div_nonneg (secondSegmentFrozenMean_nonneg X μ E r) hE0.le
  have hψm : Measurable ψ := (continuous_secondSegmentWindow δ M).measurable
  have hψb : ∀ r, ‖ψ r‖ ≤ 1 := fun r => by
    rw [Real.norm_of_nonneg (secondSegmentWindow_nonneg δ M r)]
    exact secondSegmentWindow_le_one δ M r
  have hψb' : ∀ r, ‖1 - ψ r‖ ≤ 1 := fun r => by
    rw [Real.norm_of_nonneg (by linarith [secondSegmentWindow_le_one δ M r])]
    linarith [secondSegmentWindow_nonneg δ M r]
  have hfψ : Integrable (fun r => f r * ψ r) ρ :=
    hfint.mul_bdd (c := 1) hψm.aestronglyMeasurable (ae_of_all _ hψb)
  have hf1ψ : Integrable (fun r => f r * (1 - ψ r)) ρ :=
    hfint.mul_bdd (c := 1) (measurable_const.sub hψm).aestronglyMeasurable (ae_of_all _ hψb')
  have hgρ : Integrable g ρ := KernelLimit.integrable_of_abs_le hgc.measurable hgb
  have hgν : Integrable g (ν : Measure ℝ) := KernelLimit.integrable_of_abs_le hgc.measurable hgb
  have hℓ1ψ : Integrable (fun r => ℓ r * (1 - ψ r)) (ν : Measure ℝ) :=
    hℓint.mul_bdd (c := 1) (measurable_const.sub hψm).aestronglyMeasurable (ae_of_all _ hψb')
  have hdecf : (∫ r, f r ∂ρ) = (∫ r, f r * ψ r ∂ρ) + ∫ r, f r * (1 - ψ r) ∂ρ := by
    rw [← integral_add hfψ hf1ψ]
    congr 1
    funext r
    ring
  have hdecℓ : (∫ r, ℓ r ∂(ν : Measure ℝ)) =
      (∫ r, g r ∂(ν : Measure ℝ)) + ∫ r, ℓ r * (1 - ψ r) ∂(ν : Measure ℝ) := by
    rw [← integral_add hgν hℓ1ψ]
    congr 1
    funext r
    simp only [hgdef, hψdef]
    ring
  have hwin := abs_integral_window_sub_le (ρ := ρ) (f := f) (g := ℓ) (M := M) hδ0
    (η := ε/8) (by positivity) hfψ hgρ (fun r hr => by
      have hr' : r ∈ Icc (-(M+1)) (-(δ/2)) := by
        obtain ⟨h1, h2⟩ := hr
        constructor <;> linarith
      have := hu r hr'
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this.le)
  have hR1nn : 0 ≤ ∫ r, f r * (1 - ψ r) ∂ρ :=
    integral_nonneg fun r => mul_nonneg (hf0 r) (by linarith [secondSegmentWindow_le_one δ M r])
  have hR2nn : 0 ≤ ∫ r, ℓ r * (1 - ψ r) ∂(ν : Measure ℝ) :=
    integral_nonneg fun r => mul_nonneg (secondSegmentLimitKernel_nonneg hX hi hG r)
      (by linarith [secondSegmentWindow_le_one δ M r])
  have hfar2 : 2 * (m1 / M) ≤ ε/8 := by
    have : 0 ≤ m1 / M := by positivity
    linarith
  change |(∫ r, f r ∂ρ) - ∫ r, ℓ r ∂(ν : Measure ℝ)| < ε
  rw [hdecf, hdecℓ]
  rw [abs_le] at hwin
  rw [abs_lt] at hw ⊢
  constructor <;> linarith [hwin.1, hwin.2, hw.1, hw.2]

/-! ### Properties of the limit law and of the coefficient -/

/-- **C2.1, companion facts.**  Every such limit `ν` is carried by `(-∞, 0)`, has no
atom at `0`, integrates `ℓ`, and gives a strictly positive coefficient. -/
theorem secondSegment_entranceLimit_properties
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {budget : ι → ℝ}
    (hbudget_top : Tendsto budget l atTop) {ν : ProbabilityMeasure ℝ}
    (hν : let _ : IsProbabilityMeasure μ := hi.isProbabilityMeasure
      Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν)) :
    (ν : Measure ℝ) (Ioi 0) = 0 ∧ (ν : Measure ℝ) {0} = 0 ∧
      Integrable (secondSegmentLimitKernel X μ) (ν : Measure ℝ) ∧
      0 < ∫ r, secondSegmentLimitKernel X μ r ∂(ν : Measure ℝ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hν' : Tendsto (fun i => nativeTransientMarginProb μ hX (budget i) 1) l (𝓝 ν) := hν
  have hC1 : 0 ≤ nativeFirstMarginConcentrationConstant 1 :=
    nativeFirstMarginConcentrationConstant_nonneg (by norm_num)
  have hνneg := firstMarginLimit_ae_neg hX hi hG hbudget_top hν'
  have hℓint : Integrable (secondSegmentLimitKernel X μ) (ν : Measure ℝ) :=
    secondSegmentLimitKernel_integrable_of_ball hX hi hG hνneg hC1
      (fun s hs hs1 => firstMarginLimit_ball_le hX hi hG hbudget_top hν' hs.le hs1)
  refine ⟨firstMarginLimit_Ioi_zero hX hi hG hbudget_top hν',
    firstMarginLimit_singleton_zero hX hi hG hbudget_top hν', hℓint, ?_⟩
  rw [integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (secondSegmentLimitKernel_nonneg hX hi hG)) hℓint]
  have hsub : Iio 0 ⊆ Function.support (secondSegmentLimitKernel X μ) :=
    fun r hr => (secondSegmentLimitKernel_pos hX hi hG hr).ne'
  have hIio : (ν : Measure ℝ) (Iio 0) = 1 := by
    rw [← compl_Ici, prob_compl_eq_one_sub measurableSet_Ici,
      firstMarginLimit_Ici_zero hX hi hG hbudget_top hν', tsub_zero]
  calc (0 : ℝ≥0∞) < 1 := one_pos
    _ = (ν : Measure ℝ) (Iio 0) := hIio.symm
    _ ≤ _ := measure_mono hsub

end SwingRepair
