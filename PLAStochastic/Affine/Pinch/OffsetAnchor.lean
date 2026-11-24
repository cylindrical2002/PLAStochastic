import PLAStochastic.Affine.Pinch.CompletedStoppingTime

/-!
# Brownian pinch from every deterministic interior anchor offset

For `|η| < ε`, the actual path is fitted by lines starting at height η.
Finiteness follows from comparison with the origin-anchored budget ε + |η|.
The closed-budget hitting time is a true augmented stopping time, and strong
Markov removes any distinction between its first pinch and first failure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Deterministic change of the anchor height. -/
def offsetPath (f : C(ℝ, ℝ)) (η : ℝ) : C(ℝ, ℝ) := f - ContinuousMap.const ℝ η

@[simp] theorem offsetPath_apply (f : C(ℝ, ℝ)) (η t : ℝ) : offsetPath f η t = f t - η := rfl

theorem anchoredTimeError_le_offset_add (f : C(ℝ, ℝ)) (η : ℝ) (T : ℝ≥0) :
    anchoredTimeError f T ≤ anchoredTimeError (offsetPath f η) T + |η| := by
  have hs := (anchoredError_le_iff_exists_fit T.property (intervalPath (offsetPath f η) T)).mp
    (le_refl (anchoredError (intervalPath (offsetPath f η) T)))
  obtain ⟨a, ha⟩ := hs
  have hfit : anchoredError (intervalPath f T) ≤
      anchoredError (intervalPath (offsetPath f η) T) + |η| := by
    apply (anchoredError_le_iff_exists_fit T.property (intervalPath f T)).mpr
    refine ⟨a, fun t => ?_⟩
    calc
      |f t - a * (t : ℝ)| = |(f t - η - a * (t : ℝ)) + η| := by congr 1; ring
      _ ≤ |f t - η - a * (t : ℝ)| + |η| := abs_add_le _ _
      _ ≤ _ := add_le_add (ha t) le_rfl
  exact (anchoredTimeError_eq_interval T.property f).trans_le
    (hfit.trans_eq (congrArg (· + |η|) (anchoredTimeError_eq_interval T.property (offsetPath f η)).symm))

theorem offsetLifetime_le_larger_origin (f : C(ℝ, ℝ)) (η ε : ℝ) :
    anchoredLifetime (offsetPath f η) ε ≤ anchoredLifetime f (ε + |η|) := by
  apply le_iInf
  intro t
  split_ifs with ht
  · apply firstExceedance_le_of_exceeds
    have := anchoredTimeError_le_offset_add f η t
    linarith
  · exact le_top

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The continuous measurable version has genuinely adapted coordinates. -/
theorem adapted_continuousBrownian_coordinate (hB : IsBrownianReal B μ) :
    Adapted (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun t ω => continuousBrownianPath hB ω t) := by
  intro t A hA
  have hm : Measurable (fun ω => continuousBrownianPath hB ω t) :=
    (continuous_eval_const (t : ℝ)).measurable.comp (measurable_continuousBrownianPath hB)
  refine ⟨hm hA, ?_⟩
  have hn := (Filtration.stronglyAdapted_natural
    (fun s => (measurable_measurableBrownian hB.toIsPreBrownianReal s).stronglyMeasurable) t).measurable
  refine ⟨measurableBrownian hB.toIsPreBrownianReal t ⁻¹' A, hn hA, ?_⟩
  have heq : (fun ω => continuousBrownianPath hB ω t) =ᵐ[μ]
      measurableBrownian hB.toIsPreBrownianReal t := by
    filter_upwards [continuousBrownianPath_all_times_ae_eq hB,
      measurableBrownian_ae_eq hB.toIsPreBrownianReal t] with ω hp hm
    exact (hp t).trans hm.symm
  exact heq.preimage A

theorem adapted_continuousBrownian_offset_error (hB : IsBrownianReal B μ) (η : ℝ) :
    Adapted (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (fun T ω => anchoredTimeError (offsetPath (continuousBrownianPath hB ω) η) T) := by
  intro T
  have hsam : Measurable[augmentedBrownianFiltration hB.toIsPreBrownianReal T]
      (fun ω (s : ErrorSample) => continuousBrownianPath hB ω (T * errorSampleTime s) - η) := by
    refine @measurable_pi_lambda Ω ErrorSample (fun _ => ℝ)
      (augmentedBrownianFiltration hB.toIsPreBrownianReal T) (fun _ => inferInstance) _ (fun s => ?_)
    have hst : T * errorSampleTime s ≤ T :=
      mul_le_of_le_one_right T.property s.1.property.2
    exact ((adapted_continuousBrownian_coordinate hB (T * errorSampleTime s)).mono
      ((augmentedBrownianFiltration hB.toIsPreBrownianReal).mono hst) le_rfl).sub_const η
  have hm := measurable_sampledAnchoredError.comp hsam
  convert hm using 1
  funext ω
  change anchoredError (unitPath (offsetPath (continuousBrownianPath hB ω) η) T) = _
  rw [← sampledAnchoredError_eq]
  rfl

def offsetProcessLifetime (B : ℝ≥0 → Ω → ℝ) (η ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  anchoredLifetime (offsetPath (processPath B ω) η) ε

def brownianOffsetPinch (hB : IsBrownianReal B μ) (η ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  firstReach (fun t : ℝ≥0 => anchoredTimeError (offsetPath (continuousBrownianPath hB ω) η) t) ε

theorem brownianOffsetPinch_le_iff (hB : IsBrownianReal B μ) (η ε : ℝ) (T : ℝ≥0) (ω : Ω) :
    brownianOffsetPinch hB η ε ω ≤ (T : ℝ≥0∞) ↔
      ε ≤ anchoredTimeError (offsetPath (continuousBrownianPath hB ω) η) T :=
  firstReach_le_iff (anchoredTimeError_nnreal_monotone _)
    ((continuous_anchoredTimeError _).comp continuous_subtype_val) T

theorem brownianOffsetPinch_isStoppingTime (hB : IsBrownianReal B μ) (η ε : ℝ) :
    IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (brownianOffsetPinch hB η ε) := by
  intro T
  have heq : {ω | brownianOffsetPinch hB η ε ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ε ≤ anchoredTimeError (offsetPath (continuousBrownianPath hB ω) η) T} := by
    ext ω
    exact brownianOffsetPinch_le_iff hB η ε T ω
  rw [heq]
  exact measurableSet_le measurable_const (adapted_continuousBrownian_offset_error hB η T)

theorem brownianOffsetPinch_ae_pos (hB : IsBrownianReal B μ) {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, 0 < brownianOffsetPinch hB η ε ω := by
  filter_upwards [continuousBrownianPath_all_times_ae_eq hB, hB.eval_zero_ae_eq_zero] with ω hp hz
  apply lt_of_not_ge
  intro h
  have hx := (brownianOffsetPinch_le_iff hB η ε 0 ω).mp h
  rw [NNReal.coe_zero, anchoredTimeError_zero, offsetPath_apply, ← NNReal.coe_zero,
    hp 0, hz, zero_sub, abs_neg] at hx
  exact hη.not_ge hx

theorem offsetProcessLifetime_ae_ne_top (hB : IsBrownianReal B μ) {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, offsetProcessLifetime B η ε ω ≠ ⊤ := by
  have hε : 0 < ε + |η| := by have := abs_nonneg η; linarith
  filter_upwards [anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hω
  exact ne_top_of_le_ne_top hω (offsetLifetime_le_larger_origin (processPath B ω) η ε)

theorem brownianOffsetPinch_ae_ne_top (hB : IsBrownianReal B μ) {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, brownianOffsetPinch hB η ε ω ≠ ⊤ := by
  filter_upwards [continuousBrownianPath_ae_eq hB, offsetProcessLifetime_ae_ne_top hB hη]
    with ω hp hf
  have hle : brownianOffsetPinch hB η ε ω ≤ offsetProcessLifetime B η ε ω := by
    unfold brownianOffsetPinch
    rw [hp]
    exact firstReach_le_firstExceedance _ _
  exact ne_top_of_le_ne_top hf hle

theorem isBrownianReal_restart_offsetPinch (hB : IsBrownianReal B μ) {η ε : ℝ} (hη : |η| < ε) :
    IsBrownianReal (brownianRestartAt B (brownianOffsetPinch hB η ε)) μ :=
  Augmented.isBrownianReal_brownianRestartAt hB (brownianOffsetPinch_isStoppingTime hB η ε)
    (brownianOffsetPinch_ae_ne_top hB hη)

/-- No plateau remains at the first closed-budget hit for any interior offset. -/
theorem brownianOffsetPinch_ae_eq_lifetime (hB : IsBrownianReal B μ) {η ε : ℝ} (hη : |η| < ε) :
    brownianOffsetPinch hB η ε =ᵐ[μ] offsetProcessLifetime B η ε := by
  filter_upwards [continuousBrownianPath_ae_eq hB, continuousBrownianPath_all_times_ae_eq hB,
    hB.eval_zero_ae_eq_zero, brownianOffsetPinch_ae_ne_top hB hη,
    brownian_linear_oscillation_zero_ae (isBrownianReal_restart_offsetPinch hB hη)]
      with ω hp hpall hz hf ho
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : brownianOffsetPinch hB η ε ω = (σ : ℝ≥0∞) := hσ.symm
  have hu : (brownianOffsetPinch hB η ε ω).untopD 0 = σ := by rw [hσ']; rfl
  have hzero : |offsetPath (continuousBrownianPath hB ω) η 0| < ε := by
    rw [offsetPath_apply, ← NNReal.coe_zero, hpall 0, hz, zero_sub, abs_neg]
    exact hη
  have hosc : ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        0 < offsetPath (continuousBrownianPath hB ω) η ((σ + t : ℝ≥0) : ℝ) -
          offsetPath (continuousBrownianPath hB ω) η σ - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        offsetPath (continuousBrownianPath hB ω) η ((σ + t : ℝ≥0) : ℝ) -
          offsetPath (continuousBrownianPath hB ω) η σ - a * (t : ℝ) < 0) := by
    intro a δ hδ
    have heq (t : ℝ≥0) :
        offsetPath (continuousBrownianPath hB ω) η ((σ + t : ℝ≥0) : ℝ) -
          offsetPath (continuousBrownianPath hB ω) η σ - a * (t : ℝ) =
        brownianRestartAt B (brownianOffsetPinch hB η ε) t ω - a * (t : ℝ) := by
      simp only [offsetPath_apply, hpall, brownianRestartAt, brownianRestart, hu]
      ring
    simpa only [heq] using ho a δ hδ
  have heq := firstReach_eq_anchoredLifetime_of_oscillation
    (offsetPath (continuousBrownianPath hB ω) η) hzero hσ' hosc
  change brownianOffsetPinch hB η ε ω = anchoredLifetime (offsetPath (processPath B ω) η) ε
  rw [hσ', ← hp]
  exact heq.symm

/-- The original offset lifetime is a genuine stopping time after completion. -/
theorem offsetProcessLifetime_isStoppingTime_completed (hB : IsBrownianReal B μ)
    {η ε : ℝ} (hη : |η| < ε) :
    IsStoppingTime (completedBrownianFiltration hB.toIsPreBrownianReal)
      (offsetProcessLifetime B η ε) := by
  intro T
  have ht := (brownianOffsetPinch_isStoppingTime hB η ε) T
  apply EventuallyMeasurableSet.congr ht.2
  filter_upwards [brownianOffsetPinch_ae_eq_lifetime hB hη] with ω hω
  apply propext
  change offsetProcessLifetime B η ε ω ≤ (T : WithTop ℝ≥0) ↔
    brownianOffsetPinch hB η ε ω ≤ (T : WithTop ℝ≥0)
  rw [hω]

theorem isBrownianReal_restart_offsetLifetime (hB : IsBrownianReal B μ)
    {η ε : ℝ} (hη : |η| < ε) :
    IsBrownianReal (brownianRestartAt B (offsetProcessLifetime B η ε)) μ := by
  have hpre := (isBrownianReal_restart_offsetPinch hB hη).toIsPreBrownianReal.congr
    (C := brownianRestartAt B (offsetProcessLifetime B η ε)) (fun t => by
      filter_upwards [brownianOffsetPinch_ae_eq_lifetime hB hη] with ω hω
      simp only [brownianRestartAt, brownianRestart, hω])
  exact ⟨hpre, hB.cont.mono (fun _ hc =>
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const)⟩

theorem offsetProcessLifetime_ae_pos (hB : IsBrownianReal B μ) {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, 0 < offsetProcessLifetime B η ε ω := by
  filter_upwards [brownianOffsetPinch_ae_eq_lifetime hB hη, brownianOffsetPinch_ae_pos hB hη]
    with ω heq hp
  exact heq ▸ hp

theorem brownian_oscillation_after_offsetLifetime_ae (hB : IsBrownianReal B μ)
    {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        0 < B ((offsetProcessLifetime B η ε ω).untopD 0 + t) ω -
          B ((offsetProcessLifetime B η ε ω).untopD 0) ω - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        B ((offsetProcessLifetime B η ε ω).untopD 0 + t) ω -
          B ((offsetProcessLifetime B η ε ω).untopD 0) ω - a * (t : ℝ) < 0) :=
  brownian_linear_oscillation_zero_ae (isBrownianReal_restart_offsetLifetime hB hη)

theorem offsetProcessLifetime_unique_fit_ae (hB : IsBrownianReal B μ)
    {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, ∃ a : ℝ,
      (∀ t : ℝ≥0, t ≤ (offsetProcessLifetime B η ε ω).untopD 0 →
        |B t ω - η - a * (t : ℝ)| ≤ ε) ∧
      (∀ b : ℝ, (∀ t : ℝ≥0, t ≤ (offsetProcessLifetime B η ε ω).untopD 0 →
        |B t ω - η - b * (t : ℝ)| ≤ ε) → b = a) ∧
      |B ((offsetProcessLifetime B η ε ω).untopD 0) ω - η -
        a * (((offsetProcessLifetime B η ε ω).untopD 0 : ℝ≥0) : ℝ)| = ε := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    offsetProcessLifetime_ae_ne_top hB hη] with ω hc hz hf
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (offsetProcessLifetime B η ε ω).untopD 0 = σ := by rw [← hσ]; rfl
  have hpath (t : ℝ≥0) : offsetPath (processPath B ω) η t = B t ω - η := by
    rw [offsetPath_apply, processPath_apply_of_continuous hc]
  have hzero : |offsetPath (processPath B ω) η 0| < ε := by
    rw [← NNReal.coe_zero, hpath 0, hz, zero_sub, abs_neg]
    exact hη
  obtain ⟨a, ha, huq⟩ := existsUnique_anchored_fit_at_lifetime (offsetPath (processPath B ω) η) hzero hσ.symm
  have hboundary := anchored_fit_terminal_boundary (offsetPath (processPath B ω) η) hzero.le hσ.symm ha
  refine ⟨a, ?_, ?_, ?_⟩
  · intro t ht
    have ht' : t ≤ σ := by simpa only [hu] using ht
    have h := ha ⟨t, t.property, by exact_mod_cast ht'⟩
    simpa only [hpath] using h
  · intro b hb
    apply huq b
    intro t
    have ht : (⟨t, t.property.1⟩ : ℝ≥0) ≤ (offsetProcessLifetime B η ε ω).untopD 0 := by
      rw [hu]
      exact t.property.2
    have h := hb ⟨t, t.property.1⟩ ht
    rw [← hpath ⟨t, t.property.1⟩] at h
    exact h
  · simpa only [hu, hpath] using hboundary

theorem brownian_boundary_anchor_no_fit_after_offsetLifetime_ae (hB : IsBrownianReal B μ)
    {η ε : ℝ} (hη : |η| < ε) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        ε < |B ((offsetProcessLifetime B η ε ω).untopD 0 + t) ω -
          (B ((offsetProcessLifetime B η ε ω).untopD 0) ω + ε) - a * (t : ℝ)|) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        ε < |B ((offsetProcessLifetime B η ε ω).untopD 0 + t) ω -
          (B ((offsetProcessLifetime B η ε ω).untopD 0) ω - ε) - a * (t : ℝ)|) := by
  filter_upwards [brownian_oscillation_after_offsetLifetime_ae hB hη] with ω hω
  intro a δ hδ
  obtain ⟨⟨u, hu, huδ, hup⟩, ⟨v, hv, hvδ, hvn⟩⟩ := hω a δ hδ
  constructor
  · refine ⟨v, hv, hvδ, ?_⟩
    have := neg_le_abs (B ((offsetProcessLifetime B η ε ω).untopD 0 + v) ω -
      (B ((offsetProcessLifetime B η ε ω).untopD 0) ω + ε) - a * (v : ℝ))
    linarith
  · refine ⟨u, hu, huδ, ?_⟩
    have := le_abs_self (B ((offsetProcessLifetime B η ε ω).untopD 0 + u) ω -
      (B ((offsetProcessLifetime B η ε ω).untopD 0) ω - ε) - a * (u : ℝ))
    linarith

end BrownianAffine
