import PLAStochastic.Affine.Pinch.StoppingTime
import PLAStochastic.Affine.Process.Markov.StrongMarkovAugmented
import PLAStochastic.Affine.Process.Hitting.LinearOscillation

/-!
# The Brownian first pinch is the actual first feasibility failure

The closed-budget hitting time is proved to be an almost surely finite stopping
time. Its unique fitted line touches the terminal band. Strong Markov supplies
both-sign oscillations after that same stopping time, so no feasible extension
exists. Thus the closed hitting time and the actual strict-exceedance lifetime
are almost surely equal, without assuming a stopping-time property of the latter.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- A deterministic oscillation criterion rules out a plateau at the first
closed-budget hit. The Brownian oscillation hypothesis is proved below. -/
theorem firstReach_eq_anchoredLifetime_of_oscillation (f : C(ℝ, ℝ)) {ε : ℝ}
    (hzero : |f 0| < ε) {σ : ℝ≥0}
    (hσ : firstReach (fun t : ℝ≥0 => anchoredTimeError f t) ε = σ)
    (hosc : ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        0 < f ((σ + t : ℝ≥0) : ℝ) - f σ - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        f ((σ + t : ℝ≥0) : ℝ) - f σ - a * (t : ℝ) < 0)) :
    anchoredLifetime f ε = σ := by
  have hε : 0 < ε := (abs_nonneg _).trans_lt hzero
  have hc : Continuous (fun t : ℝ≥0 => anchoredTimeError f t) :=
    (continuous_anchoredTimeError f).comp continuous_subtype_val
  have herr : anchoredTimeError f σ = ε :=
    error_at_firstReach (anchoredTimeError_nnreal_monotone f) hc
      (by simpa only [NNReal.coe_zero, anchoredTimeError_zero] using hzero) hσ
  have herr' : anchoredError (intervalPath f σ) = ε :=
    (anchoredTimeError_eq_interval σ.property f).symm.trans herr
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit σ.property (intervalPath f σ)).mp herr'.le
  have hterminal := anchored_fit_firstReach_terminal_boundary f hzero hσ ha
  apply le_antisymm ?_ (hσ ▸ firstReach_le_firstExceedance _ _)
  by_contra h
  obtain ⟨T, hσT, hT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge h)
  have hσT' : σ < T := ENNReal.coe_lt_coe.mp hσT
  have heT := (le_anchoredLifetime_iff_of_initial f hzero.le T).mp hT.le
  have heT' : anchoredError (intervalPath f T) ≤ ε := by
    exact (anchoredTimeError_eq_interval T.property f) ▸ heT
  obtain ⟨b, hb⟩ := (anchoredError_le_iff_exists_fit T.property (intervalPath f T)).mp heT'
  have hba : b = a := anchored_feasible_slope_unique σ.property hε (intervalPath f σ)
    hzero herr' (fun t => hb ⟨t, t.property.1, t.property.2.trans hσT'.le⟩) ha
  subst b
  have hδ : 0 < T - σ := tsub_pos_iff_lt.mpr hσT'
  obtain ⟨hp, hn⟩ := hosc a (T - σ) hδ
  have hbound (t : ℝ≥0) (ht : t < T - σ) :
      |f ((σ + t : ℝ≥0) : ℝ) - a * ((σ + t : ℝ≥0) : ℝ)| ≤ ε := by
    apply hb ⟨σ + t, (σ + t).property, ?_⟩
    change (σ : ℝ) + (t : ℝ) ≤ (T : ℝ)
    have ht' : (t : ℝ) < ((T - σ : ℝ≥0) : ℝ) := ht
    rw [NNReal.coe_sub hσT'.le] at ht'
    linarith
  rcases eq_or_eq_neg_of_abs_eq hterminal with hs | hs
  · obtain ⟨t, _, ht, hv⟩ := hp
    have hb' := (abs_le.mp (hbound t ht)).2
    rw [NNReal.coe_add] at hb' hv
    nlinarith
  · obtain ⟨t, _, ht, hv⟩ := hn
    have hb' := (abs_le.mp (hbound t ht)).1
    rw [NNReal.coe_add] at hb' hv
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Strong Markov is applied to the proved, finite, augmented stopping time. -/
theorem isBrownianReal_restart_firstPinch (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    IsBrownianReal (brownianRestartAt B (brownianFirstPinch hB ε)) μ :=
  Augmented.isBrownianReal_brownianRestartAt hB (brownianFirstPinch_isStoppingTime hB ε)
    (brownianFirstPinch_ae_ne_top hB hε)

theorem brownian_oscillation_after_firstPinch_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        0 < B ((brownianFirstPinch hB ε ω).untopD 0 + t) ω -
          B ((brownianFirstPinch hB ε ω).untopD 0) ω - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        B ((brownianFirstPinch hB ε ω).untopD 0 + t) ω -
          B ((brownianFirstPinch hB ε ω).untopD 0) ω - a * (t : ℝ) < 0) :=
  brownian_linear_oscillation_zero_ae (isBrownianReal_restart_firstPinch hB hε)

/-- The measurable stopping-time version equals the original actual lifetime,
not just a random variable with the same distribution. -/
theorem brownianFirstPinch_ae_eq_lifetime (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    brownianFirstPinch hB ε =ᵐ[μ] anchoredProcessLifetime B ε := by
  filter_upwards [continuousBrownianPath_ae_eq hB, continuousBrownianPath_all_times_ae_eq hB,
    hB.eval_zero_ae_eq_zero, brownianFirstPinch_ae_ne_top hB hε,
    brownian_oscillation_after_firstPinch_ae hB hε] with ω hp hpall hz hf ho
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hσ' : brownianFirstPinch hB ε ω = (σ : ℝ≥0∞) := hσ.symm
  have hu : (brownianFirstPinch hB ε ω).untopD 0 = σ := by
    rw [hσ']
    rfl
  have hzero : |continuousBrownianPath hB ω 0| < ε := by
    rw [← NNReal.coe_zero, hpall 0, hz, abs_zero]
    exact hε
  have hosc : ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        0 < continuousBrownianPath hB ω ((σ + t : ℝ≥0) : ℝ) - continuousBrownianPath hB ω σ - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        continuousBrownianPath hB ω ((σ + t : ℝ≥0) : ℝ) - continuousBrownianPath hB ω σ - a * (t : ℝ) < 0) := by
    intro a δ hδ
    simpa only [hu, hpall] using ho a δ hδ
  have heq := firstReach_eq_anchoredLifetime_of_oscillation (continuousBrownianPath hB ω)
    hzero hσ' hosc
  change brownianFirstPinch hB ε ω = anchoredLifetime (processPath B ω) ε
  rw [hσ', ← hp]
  exact heq.symm

end BrownianAffine
