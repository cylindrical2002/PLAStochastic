import PLAStochastic.Swing.SecondSegment.MeanUpperBound

/-! # The matching lower bound of Theorem 3.4

On one Gaussian envelope event the pathwise candidate-line bound forces a
segment of length proportional to the budget, and Lemma G.1 keeps the actual
first margin inside a fixed window with probability at least one half.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- One fixed window, independent of the budget. -/
def secondSegmentCutoff : ℝ :=
  1+2*nativeFirstMarginMomentBound 1+Real.sqrt (2*nativeGaussianEnvelopeTailConstant)

theorem nativeFirstMarginMomentBound_nonneg (k : ℕ) : 0 ≤ nativeFirstMarginMomentBound k := by
  have h1 := nativeFirstMarginTailConstant_pos
  have h2 := expTailMomentSum_nonneg (1/51200) k
  dsimp [nativeFirstMarginMomentBound]
  positivity

theorem secondSegmentCutoff_ge_one : 1 ≤ secondSegmentCutoff := by
  have h1 := nativeFirstMarginMomentBound_nonneg 1
  have h2 : 0 ≤ Real.sqrt (2*nativeGaussianEnvelopeTailConstant) := Real.sqrt_nonneg _
  dsimp [secondSegmentCutoff]
  linarith

theorem secondSegmentCutoff_pos : 0 < secondSegmentCutoff := by
  linarith [secondSegmentCutoff_ge_one]

theorem secondSegmentCutoff_ge_moment : 2*nativeFirstMarginMomentBound 1 ≤ secondSegmentCutoff := by
  have h2 : 0 ≤ Real.sqrt (2*nativeGaussianEnvelopeTailConstant) := Real.sqrt_nonneg _
  dsimp [secondSegmentCutoff]
  linarith

/-- The Gaussian envelope stays below the window with probability at least one half. -/
theorem measureReal_envelope_good
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    1/2 ≤ μ.real {ω | nativeGaussianEnvelope X ω ≤ secondSegmentCutoff} := by
  have hprob := hi.isProbabilityMeasure
  have hM1 := secondSegmentCutoff_ge_one
  have hCenv := nativeGaussianEnvelope_tail_constant_pos
  have htail := nativeGaussianEnvelope_tail_bound hX hi hG (t := secondSegmentCutoff) hM1
  have hsq : 2*nativeGaussianEnvelopeTailConstant ≤ secondSegmentCutoff^2 := by
    have h1 := nativeFirstMarginMomentBound_nonneg 1
    have hnn : 0 ≤ Real.sqrt (2*nativeGaussianEnvelopeTailConstant) := Real.sqrt_nonneg _
    have hsqeq : Real.sqrt (2*nativeGaussianEnvelopeTailConstant)^2 =
        2*nativeGaussianEnvelopeTailConstant :=
      Real.sq_sqrt (by linarith [hCenv] : (0:ℝ) ≤ 2*nativeGaussianEnvelopeTailConstant)
    have hs : Real.sqrt (2*nativeGaussianEnvelopeTailConstant) ≤ secondSegmentCutoff := by
      dsimp [secondSegmentCutoff]
      linarith
    nlinarith
  have hlog : Real.log (2*nativeGaussianEnvelopeTailConstant) ≤
      2*nativeGaussianEnvelopeTailConstant := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2*nativeGaussianEnvelopeTailConstant by
      positivity)
    linarith
  have hexp : nativeGaussianEnvelopeTailConstant*Real.exp (-secondSegmentCutoff^2) ≤ 1/2 := by
    have hle : Real.exp (-secondSegmentCutoff^2) ≤
        Real.exp (-Real.log (2*nativeGaussianEnvelopeTailConstant)) :=
      Real.exp_le_exp.mpr (by linarith)
    have heq : Real.exp (-Real.log (2*nativeGaussianEnvelopeTailConstant)) =
        1/(2*nativeGaussianEnvelopeTailConstant) := by
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      ring
    rw [heq] at hle
    have hmul := mul_le_mul_of_nonneg_left hle hCenv.le
    have hval : nativeGaussianEnvelopeTailConstant*(1/(2*nativeGaussianEnvelopeTailConstant)) =
        1/2 := by field_simp
    rw [hval] at hmul
    exact hmul
  have hmeas : MeasurableSet {ω | secondSegmentCutoff < nativeGaussianEnvelope X ω} :=
    measurableSet_lt measurable_const (nativeGaussianEnvelope_measurable hX)
  have hcompl : {ω | nativeGaussianEnvelope X ω ≤ secondSegmentCutoff} =
      {ω | secondSegmentCutoff < nativeGaussianEnvelope X ω}ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
  have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp
  rw [hcompl, measureReal_compl hmeas, huniv]
  linarith

/-- On the envelope event the candidate line forces a long actual segment. -/
theorem nativeRestartMean_lower
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (x : ℝ) :
    E/(4*(nativeRestartExcess E x+2*secondSegmentCutoff)) ≤ nativeRestartMean X μ E x := by
  have hprob := hi.isProbabilityMeasure
  have hMpos := secondSegmentCutoff_pos
  have hexc : 0 ≤ nativeRestartExcess E x := le_max_right _ _
  have hB : 0 < nativeRestartExcess E x+2*secondSegmentCutoff := by linarith
  set c : ℝ := E/(2*(nativeRestartExcess E x+2*secondSegmentCutoff)) with hc
  have hcnn : 0 ≤ c := by positivity
  set A : Set Ω := {ω | nativeGaussianEnvelope X ω ≤ secondSegmentCutoff} with hA
  have hAmeas : MeasurableSet A :=
    measurableSet_le (nativeGaussianEnvelope_measurable hX) measurable_const
  have hdom : ∀ᵐ ω ∂μ, A.indicator (fun _ => c) ω ≤ (nativeRestartLengthNat X E x ω : ℝ) := by
    filter_upwards [nativeGaussianEnvelope_bounds_ae hX hi hG,
      nativeRestartLength_ae_finite hX hi hG hE x] with ω hω hfin
    by_cases hmem : ω ∈ A
    · rw [Set.indicator_of_mem hmem]
      have hmem' : nativeGaussianEnvelope X ω ≤ secondSegmentCutoff := hmem
      have hWb : ∀ n, |cumulativeSamples X n ω| ≤ secondSegmentCutoff*((n : ℝ)+1) := by
        intro n
        refine (hω n).trans ?_
        exact mul_le_mul_of_nonneg_right hmem' (by positivity)
      have hlow := nativeRestartLengthNat_scale_lower X hE.le hMpos.le ω hWb hB hfin
      rw [hc, div_le_iff₀ (by linarith : (0:ℝ) < 2*(nativeRestartExcess E x+2*secondSegmentCutoff))]
      nlinarith [hlow.2]
    · rw [Set.indicator_of_notMem hmem]
      exact Nat.cast_nonneg _
  have hindint : Integrable (A.indicator (fun _ => c)) μ := (integrable_const c).indicator hAmeas
  have hNint := nativeRestartLengthNat_integrable hX hi hG hE x
  have hmono := integral_mono_ae hindint hNint hdom
  rw [integral_indicator_const _ hAmeas, smul_eq_mul] at hmono
  have hgood := measureReal_envelope_good hX hi hG
  have hfin : E/(4*(nativeRestartExcess E x+2*secondSegmentCutoff)) ≤ μ.real A*c := by
    have hval : E/(4*(nativeRestartExcess E x+2*secondSegmentCutoff)) = (1/2)*c := by
      rw [hc]
      field_simp
      ring
    rw [hval]
    exact mul_le_mul_of_nonneg_right hgood hcnn
  exact hfin.trans hmono

/-- Markov's inequality for the absolute first margin. -/
theorem measureReal_nativeFirstMargin_abs_gt_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E δ : ℝ} (hE : 1 ≤ 2*E) :
    δ*μ.real {ω | δ < |nativeFirstMargin X E ω|} ≤ ∫ ω, |nativeFirstMargin X E ω| ∂μ := by
  have hprob := hi.isProbabilityMeasure
  set S : Set Ω := {ω | δ < |nativeFirstMargin X E ω|} with hS
  have hSm : MeasurableSet S :=
    measurableSet_lt measurable_const (nativeFirstMargin_measurable hX E).abs
  have hint := integrable_nativeFirstMargin_abs hX hi hG hE
  have hindint : Integrable (S.indicator (fun _ => δ)) μ := (integrable_const δ).indicator hSm
  have hdom : ∀ ω, S.indicator (fun _ => δ) ω ≤ |nativeFirstMargin X E ω| := by
    intro ω
    by_cases hω : ω ∈ S
    · rw [Set.indicator_of_mem hω]
      exact le_of_lt hω
    · rw [Set.indicator_of_notMem hω]
      exact abs_nonneg _
  have hmono := integral_mono hindint hint hdom
  rwa [integral_indicator_const _ hSm, smul_eq_mul, mul_comm] at hmono

/-- Theorem 3.4 (lower bound): the actual second segment has mean at least `cE`. -/
theorem secondSegment_mean_ge
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 16 ≤ E) :
    E/(24*secondSegmentCutoff) ≤ ∫ ω, (nativeRecordingDurationNat X E 1 ω : ℝ) ∂μ := by
  have hprob := hi.isProbabilityMeasure
  have hE0 : (0 : ℝ) < E := by linarith
  have hE2 : (1 : ℝ) ≤ 2*E := by linarith
  have hMpos := secondSegmentCutoff_pos
  set M : ℝ := secondSegmentCutoff with hM
  -- the good margin window
  set B : Set Ω := {ω | -M ≤ nativeFirstMargin X E ω} with hB
  have hBmeas : MeasurableSet B :=
    measurableSet_le measurable_const (nativeFirstMargin_measurable hX E)
  have hmomentbound : (∫ ω, |nativeFirstMargin X E ω| ∂μ) ≤ nativeFirstMarginMomentBound 1 := by
    simpa using integral_nativeFirstMargin_pow_le hX hi hG hE2 1
  have hmark := measureReal_nativeFirstMargin_abs_gt_le hX hi hG (δ := M) hE2
  have hbad : μ.real {ω | M < |nativeFirstMargin X E ω|} ≤ 1/2 := by
    have hstep : M*μ.real {ω | M < |nativeFirstMargin X E ω|} ≤ nativeFirstMarginMomentBound 1 :=
      hmark.trans hmomentbound
    have hcut := secondSegmentCutoff_ge_moment
    rw [← hM] at hcut
    nlinarith [hstep, hcut, hMpos]
  have hBgood : 1/2 ≤ μ.real B := by
    have hsub : Bᶜ ⊆ {ω | M < |nativeFirstMargin X E ω|} := by
      intro ω hω
      have hlt : nativeFirstMargin X E ω < -M := lt_of_not_ge hω
      show M < |nativeFirstMargin X E ω|
      rw [abs_of_neg (by linarith)]
      linarith
    have hcompl := measureReal_compl (μ := μ) hBmeas
    have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp
    have hle := (measureReal_mono (μ := μ) hsub).trans hbad
    rw [hcompl, huniv] at hle
    linarith
  -- the pointwise lower bound on the good window
  have hlow : ∀ ω ∈ B, E/(12*M) ≤ nativeRestartMean X μ E (nativeFirstNext X E ω) := by
    intro ω hω
    have hmargin : -M ≤ nativeFirstMargin X E ω := hω
    have habs : |nativeFirstNext X E ω| = E-nativeFirstMargin X E ω := by
      rw [nativeFirstMargin]
      ring
    have hexc : nativeRestartExcess E (nativeFirstNext X E ω) ≤ M := by
      rw [nativeRestartExcess, habs]
      exact max_le (by linarith) hMpos.le
    have hstep := nativeRestartMean_lower hX hi hG hE0 (nativeFirstNext X E ω)
    refine le_trans ?_ hstep
    have hexcnn : 0 ≤ nativeRestartExcess E (nativeFirstNext X E ω) := le_max_right _ _
    apply div_le_div_of_nonneg_left hE0.le (by linarith) (by linarith)
  -- integrate
  have hindint : Integrable (B.indicator (fun _ => E/(12*M))) μ :=
    (integrable_const _).indicator hBmeas
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, ∀ x : ℝ, nativeRestartMean X μ E x ≤ Cb :=
    ⟨_, fun x => (nativeRestartMean_bounds hX hi hG hE0 x).2⟩
  have hhint : Integrable (fun ω => nativeRestartMean X μ E (nativeFirstNext X E ω)) μ := by
    refine Integrable.of_bound
      (((nativeRestartMean_measurable hX E).comp
        ((nativeRestartNext_measurable (fun k => X (1+k)) (fun k => hX (1+k)) E).comp
          ((hX 0).prodMk measurable_id))).aestronglyMeasurable) Cb ?_
    filter_upwards with ω
    have hb := nativeRestartMean_bounds hX hi hG hE0 (nativeFirstNext X E ω)
    rw [Real.norm_of_nonneg (by linarith [hb.1])]
    exact hCb _
  have hdom : ∀ ω, B.indicator (fun _ => E/(12*M)) ω ≤
      nativeRestartMean X μ E (nativeFirstNext X E ω) := by
    intro ω
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_mem hω]
      exact hlow ω hω
    · rw [Set.indicator_of_notMem hω]
      have hb := nativeRestartMean_bounds hX hi hG hE0 (nativeFirstNext X E ω)
      linarith [hb.1]
  have hmono := integral_mono hindint hhint hdom
  rw [integral_indicator_const _ hBmeas, smul_eq_mul] at hmono
  have hstart : (∫ ω, (nativeRecordingDurationNat X E 1 ω : ℝ) ∂μ) =
      ∫ ω, nativeRestartMean X μ E (nativeFirstNext X E ω) ∂μ := by
    rw [secondSegment_mean_eq hX hi hG hE0]
    exact integral_congr_ae (Eventually.of_forall fun ω =>
      (nativeRestartMean_eq_frozen_margin hX hi hG E (nativeFirstNext X E ω)).symm)
  rw [hstart]
  refine le_trans ?_ hmono
  have hval : E/(24*M) = (1/2)*(E/(12*M)) := by
    field_simp
    ring
  rw [hval]
  exact mul_le_mul_of_nonneg_right hBgood (by positivity)

end SwingRepair
