import PLAStochastic.Swing.Entrance.Local.PairLimit

/-!
# Window estimates for the actual local residual (E10)–(E12)

Uniform forms of the three window estimates on the entrance scales `d_E = E^{1/4}`,
`q_E = ⌊E^{3/4}⌋`:

* (E10) `drift_window_uniform`: drifts `|c| ≤ M/E` change expectations of functionals of the
  first `q_E` increments bounded by `1` by at most `ε`, uniformly, for all large `E`;
* (E11) `entranceCrossing_late_conditional`: given the stopped σ-algebra of the cut, on the
  truncation event the actual local residual crosses its cut width within `q_E` steps with
  conditional probability at least `1 - ε`;
* (E12) `entranceLocal_max_conditional`: in the same sense, the local residual stays within
  `E/2` of its start on the whole window. The zero-drift input is Kolmogorov's inequality
  (`zeroDrift_maximal_le`).

The conditional statements have the form `μ(A ∩ bad) ≤ ε μ(A)` for every `𝓕_τ`-event
`A ⊆ entranceGood E δ M`.
-/

namespace SwingRepair

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- An event of the frozen state and the reflected future has, on a `𝓕_τ`-event `A`,
probability at most `t μ(A)` as soon as its frozen-state probability is at most `t` on `A`. -/
theorem entrance_measureReal_freeze_le (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 ≤ E)
    {T : Set ((ℝ × ℝ) × (ℕ → ℝ))} (hT : MeasurableSet T) {A : Set Ω}
    (hA : MeasurableSet[entranceCutSigma hX E] A) {t : ℝ}
    (hbound : ∀ ω ∈ A, μ.real {η | ((entranceCutWidth X E ω, entranceCutDrift X E ω),
      fun j => X j η) ∈ T} ≤ t) :
    μ.real (A ∩ {ω | ((entranceCutWidth X E ω, entranceCutDrift X E ω),
      entranceReflectedFuture X E ω) ∈ T}) ≤ t * μ.real A := by
  have := hi.isProbabilityMeasure
  have hκ := entranceCutIndex_isStoppingTime hX E
  have hAm : MeasurableSet A := hκ.measurableSpace_le _ hA
  set Z : Ω → ℝ × ℝ := fun ω => (entranceCutWidth X E ω, entranceCutDrift X E ω)
  have hZ : Measurable[entranceCutSigma hX E] Z :=
    (measurable_entranceCutWidth hX E).prodMk (measurable_entranceCutDrift hX E)
  have hZm : Measurable Z := hZ.mono hκ.measurableSpace_le le_rfl
  have hpair : Measurable fun ω => (Z ω, entranceReflectedFuture X E ω) :=
    hZm.prodMk (measurable_entranceReflectedFuture hX E)
  have hS : MeasurableSet {ω | (Z ω, entranceReflectedFuture X E ω) ∈ T} := hpair hT
  have hG1 : Measurable (T.indicator (1 : (ℝ × ℝ) × (ℕ → ℝ) → ℝ)) :=
    measurable_const.indicator hT
  have hGb : ∀ r, |T.indicator (1 : (ℝ × ℝ) × (ℕ → ℝ) → ℝ) r| ≤ 1 := by
    intro r
    by_cases hr : r ∈ T <;> simp [hr]
  have hfreeze := entrance_setIntegral_freeze hX hi hG hE hZ hG1 hGb hA
  have hseq : Measurable fun η (j : ℕ) => X j η := measurable_pi_lambda _ hX
  have hlhs : μ.real (A ∩ {ω | (Z ω, entranceReflectedFuture X E ω) ∈ T}) =
      ∫ ω in A, T.indicator 1 (Z ω, entranceReflectedFuture X E ω) ∂μ := by
    rw [Set.inter_comm, ← measureReal_restrict_apply hS, ← integral_indicator_one hS]
    rfl
  have hrhs : ∀ ω, ∫ η, T.indicator (1 : (ℝ × ℝ) × (ℕ → ℝ) → ℝ) (Z ω, fun j => X j η) ∂μ =
      μ.real {η | (Z ω, fun j => X j η) ∈ T} := by
    intro ω
    have hm : MeasurableSet {η | (Z ω, fun j => X j η) ∈ T} :=
      (measurable_const.prodMk hseq) hT
    rw [← integral_indicator_one hm]
    rfl
  rw [hlhs, hfreeze]
  calc ∫ ω in A, ∫ η, T.indicator (1 : (ℝ × ℝ) × (ℕ → ℝ) → ℝ) (Z ω, fun j => X j η) ∂μ ∂μ
      ≤ ‖∫ ω in A, ∫ η, T.indicator (1 : (ℝ × ℝ) × (ℕ → ℝ) → ℝ) (Z ω, fun j => X j η) ∂μ ∂μ‖ :=
        Real.le_norm_self _
    _ ≤ t * μ.real A := by
      refine norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) fun ω hω => ?_
      rw [hrhs, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact hbound ω hω

/-- (E11) Conditionally on the stopped σ-algebra, on the truncation event the actual local
residual crosses its cut width within the window `q_E`, up to probability `ε`. -/
theorem entranceCrossing_late_conditional (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (δ M : ℝ) :
    ∀ ε > 0, ∀ᶠ E in atTop, ∀ A : Set Ω, MeasurableSet[entranceCutSigma hX E] A →
      A ⊆ {ω | entranceGood (entrancePath X ω) E δ M} →
      μ.real (A ∩ {ω | (entranceWindow E : ℕ∞) < entranceCrossing (entrancePath X ω) E
        (entranceCutNat (entrancePath X ω) E)}) ≤ ε * μ.real A := by
  intro ε hε
  have := hi.isProbabilityMeasure
  have ht : 0 < ε / 2 := half_pos hε
  filter_upwards [(tendsto_entranceDriftError M gaussianAbsMean).eventually (Iic_mem_nhds ht),
    eventually_zeroDrift_late_le hX hi hG ht, eventually_gt_atTop 0]
    with E hE1 hE2 hEpos A hA hAgood
  set q := entranceWindow E
  let T : Set ((ℝ × ℝ) × (ℕ → ℝ)) := {r | (q : ℕ∞) < levelCrossing (driftPath r.2 r.1.2) r.1.1}
  have hT : MeasurableSet T := by
    have := measurable_levelCrossing_driftPath
      (MeasurableSet.of_discrete (s := {t : ℕ∞ | (q : ℕ∞) < t}))
    exact this
  have hset : A ∩ {ω | (q : ℕ∞) < entranceCrossing (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E)} =
      A ∩ {ω | ((entranceCutWidth X E ω, entranceCutDrift X E ω),
        entranceReflectedFuture X E ω) ∈ T} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, T]
    constructor
    · rintro ⟨hω, h⟩
      rw [entranceCrossing_eq_driftCrossing (entranceGood_cut_bounds hEpos (hAgood hω)).1] at h
      exact ⟨hω, h⟩
    · rintro ⟨hω, h⟩
      rw [entranceCrossing_eq_driftCrossing (entranceGood_cut_bounds hEpos (hAgood hω)).1]
      exact ⟨hω, h⟩
  rw [hset]
  refine entrance_measureReal_freeze_le hX hi hG hEpos.le hT hA fun ω hω => ?_
  obtain ⟨-, -, hD2, hb⟩ := entranceGood_cut_bounds hEpos (hAgood hω)
  have h := driftLate_le hX hi hG (entranceCutWidth X E ω) (entranceCutDrift X E ω) q
  have herr := (driftError_mono hb q).trans hE1
  have hP0 := hE2 _ hD2
  change μ.real {η | (q : ℕ∞) < levelCrossing (driftPath (fun j => X j η)
    (entranceCutDrift X E ω)) (entranceCutWidth X E ω)} ≤ ε
  linarith

/-- (E12) Conditionally on the stopped σ-algebra, on the truncation event the actual local
residual stays within `E/2` on the window `q_E`, up to probability `ε`. -/
theorem entranceLocal_max_conditional (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (δ M : ℝ) :
    ∀ ε > 0, ∀ᶠ E in atTop, ∀ A : Set Ω, MeasurableSet[entranceCutSigma hX E] A →
      A ⊆ {ω | entranceGood (entrancePath X ω) E δ M} →
      μ.real (A ∩ {ω | ∃ j ≤ entranceWindow E, E / 2 < |entranceLocal (entrancePath X ω) E
        (entranceCutNat (entrancePath X ω) E) j|}) ≤ ε * μ.real A := by
  intro ε hε
  have := hi.isProbabilityMeasure
  have h1 := tendsto_entranceWindow_div
  have h2 : Tendsto (fun E : ℝ => 16 * ((entranceWindow E : ℝ) / E) * E⁻¹) atTop (𝓝 0) := by
    simpa using (h1.const_mul 16).mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h3 : Tendsto (fun E : ℝ => M * ((entranceWindow E : ℝ) / E)) atTop (𝓝 0) := by
    simpa using h1.const_mul M
  filter_upwards [h2.eventually (Iic_mem_nhds hε), h3.eventually (Iic_mem_nhds one_pos),
    eventually_ge_atTop 4] with E hE1 hE2 hE4 A hA hAgood
  have hEpos : 0 < E := by linarith
  set q := entranceWindow E
  let T : Set ((ℝ × ℝ) × (ℕ → ℝ)) := {r | ∃ j ≤ q, E / 2 < |driftPath r.2 r.1.2 j|}
  have hT : MeasurableSet T := by
    refine measurableSet_setOfPred.mpr (Measurable.exists fun j => measurable_const.and ?_)
    refine measurableSet_setOfPred.mp (measurableSet_lt measurable_const ?_)
    exact (measurable_driftPath_apply (fun i => (measurable_pi_apply i).comp measurable_snd)
      (measurable_snd.comp measurable_fst) j).abs
  have hset : A ∩ {ω | ∃ j ≤ q, E / 2 < |entranceLocal (entrancePath X ω) E
      (entranceCutNat (entrancePath X ω) E) j|} =
      A ∩ {ω | ((entranceCutWidth X E ω, entranceCutDrift X E ω),
        entranceReflectedFuture X E ω) ∈ T} := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, T]
    constructor
    · rintro ⟨hω, h⟩
      rw [entranceLocal_eq_driftPath (entranceGood_cut_bounds hEpos (hAgood hω)).1] at h
      exact ⟨hω, h⟩
    · rintro ⟨hω, h⟩
      rw [entranceLocal_eq_driftPath (entranceGood_cut_bounds hEpos (hAgood hω)).1]
      exact ⟨hω, h⟩
  rw [hset]
  refine entrance_measureReal_freeze_le hX hi hG hEpos.le hT hA fun ω hω => ?_
  obtain ⟨-, -, -, hb⟩ := entranceGood_cut_bounds hEpos (hAgood hω)
  set b := entranceCutDrift X E ω
  have hbq : |b| * q ≤ E / 4 := by
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have : |b| * q ≤ M / E * q := mul_le_mul_of_nonneg_right hb hq0
    have h' : M / E * q = M * ((q : ℝ) / E) := by ring
    linarith
  have hsub : {η | ((entranceCutWidth X E ω, b), fun j => X j η) ∈ T} ⊆
      {η | ∃ k ≤ q, E / 4 ≤ |cumulativeSamples X k η|} := by
    rintro η ⟨j, hj, hlt⟩
    refine ⟨j, hj, ?_⟩
    have hpath : driftPath (fun j => X j η) b j = cumulativeSamples X j η - b * j := rfl
    have hbj : |b * j| ≤ E / 4 := by
      rw [abs_mul, Nat.abs_cast]
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hj) (abs_nonneg b)).trans hbq
    rw [hpath] at hlt
    have := abs_sub (cumulativeSamples X j η) (b * j)
    linarith
  have hK := zeroDrift_maximal_le hX hi hG (by linarith : (0 : ℝ) < E / 4) q
  calc μ.real {η | ((entranceCutWidth X E ω, b), fun j => X j η) ∈ T}
      ≤ μ.real {η | ∃ k ≤ q, E / 4 ≤ |cumulativeSamples X k η|} := measureReal_mono hsub
    _ ≤ q / (E / 4) ^ 2 := hK
    _ = 16 * ((q : ℝ) / E) * E⁻¹ := by field_simp; ring
    _ ≤ ε := hE1

end

end SwingRepair
