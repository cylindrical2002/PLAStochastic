import PLAStochastic.Affine.Pinch.FirstPinch

/-!
# The original actual lifetime is a pinch stopping time after completion

The original continuous-path functional is not declared measurable in the raw
natural filtration. Its proved stopping-time version agrees almost surely.
Completion makes the original lifetime itself a stopping time, while the
Brownian law and oscillation of its actual restarted path follow from that
almost-sure equality before any random-time evaluation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Full completion of every filtration time by ambient null sets. Its ambient
sigma-algebra is exactly the one used by `μ.completion`; the measure is unchanged
on all sets. Right-continuous augmentation is not needed for this closed hit. -/
def completedFiltration (ℱ : Filtration ℝ≥0 mΩ) (μ : Measure Ω) :
    Filtration ℝ≥0 (eventuallyMeasurableSpace mΩ (ae μ)) where
  seq t := eventuallyMeasurableSpace (ℱ t) (ae μ)
  mono' := by
    intro s t hst A hA
    obtain ⟨D, hD, heq⟩ := hA
    exact ⟨D, ℱ.mono hst _ hD, heq⟩
  le' t A hA := by
    obtain ⟨D, hD, heq⟩ := hA
    exact ⟨D, ℱ.le t _ hD, heq⟩

def completedBrownianFiltration (hB : IsPreBrownianReal B μ) :
    Filtration ℝ≥0 (eventuallyMeasurableSpace mΩ (ae μ)) :=
  completedFiltration (brownianNaturalFiltration hB) μ

/-- The actual strict-exceedance lifetime itself is a stopping time in the
completed natural filtration. This conclusion uses the proved pinch identity. -/
theorem anchoredProcessLifetime_isStoppingTime_completed (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IsStoppingTime (completedBrownianFiltration hB.toIsPreBrownianReal)
      (anchoredProcessLifetime B ε) := by
  intro T
  have ht := (brownianFirstPinch_isStoppingTime hB ε) T
  apply EventuallyMeasurableSet.congr ht.2
  filter_upwards [brownianFirstPinch_ae_eq_lifetime hB hε] with ω hω
  apply propext
  change anchoredProcessLifetime B ε ω ≤ (T : WithTop ℝ≥0) ↔
    brownianFirstPinch hB ε ω ≤ (T : WithTop ℝ≥0)
  rw [hω]

/-- Actual restart law at the original lifetime, obtained by equality with the
proved finite stopping time. No new Markov or conditional-law hypothesis enters. -/
theorem isBrownianReal_restart_anchoredLifetime (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    IsBrownianReal (brownianRestartAt B (anchoredProcessLifetime B ε)) μ := by
  have hpre := (isBrownianReal_restart_firstPinch hB hε).toIsPreBrownianReal.congr
    (C := brownianRestartAt B (anchoredProcessLifetime B ε)) (fun t => by
      filter_upwards [brownianFirstPinch_ae_eq_lifetime hB hε] with ω hω
      simp only [brownianRestartAt, brownianRestart, hω])
  exact ⟨hpre, hB.cont.mono (fun _ hc =>
    (hc.comp (continuous_const.add continuous_id)).sub continuous_const)⟩

/-- Both signs occur after the original lifetime, simultaneously for all real
slopes and all positive future intervals. -/
theorem brownian_oscillation_after_anchoredLifetime_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        0 < B ((anchoredProcessLifetime B ε ω).untopD 0 + t) ω -
          B ((anchoredProcessLifetime B ε ω).untopD 0) ω - a * (t : ℝ)) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        B ((anchoredProcessLifetime B ε ω).untopD 0 + t) ω -
          B ((anchoredProcessLifetime B ε ω).untopD 0) ω - a * (t : ℝ) < 0) :=
  brownian_linear_oscillation_zero_ae (isBrownianReal_restart_anchoredLifetime hB hε)

/-- At the actual finite lifetime there is exactly one feasible slope, and
its terminal residual lies on the boundary of the original budget. -/
theorem anchoredProcessLifetime_unique_fit_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∃ a : ℝ,
      (∀ t : ℝ≥0, t ≤ (anchoredProcessLifetime B ε ω).untopD 0 →
        |B t ω - a * (t : ℝ)| ≤ ε) ∧
      (∀ b : ℝ, (∀ t : ℝ≥0, t ≤ (anchoredProcessLifetime B ε ω).untopD 0 →
        |B t ω - b * (t : ℝ)| ≤ ε) → b = a) ∧
      |B ((anchoredProcessLifetime B ε ω).untopD 0) ω -
        a * (((anchoredProcessLifetime B ε ω).untopD 0 : ℝ≥0) : ℝ)| = ε := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hc hz hf
  obtain ⟨σ, hσ⟩ := WithTop.ne_top_iff_exists.mp hf
  have hu : (anchoredProcessLifetime B ε ω).untopD 0 = σ := by rw [← hσ]; rfl
  have hzero : |processPath B ω 0| < ε := by
    rw [← NNReal.coe_zero, processPath_apply_of_continuous hc 0, hz, abs_zero]
    exact hε
  obtain ⟨a, ha, huq⟩ := existsUnique_anchored_fit_at_lifetime (processPath B ω) hzero hσ.symm
  have hboundary := anchored_fit_terminal_boundary (processPath B ω) hzero.le hσ.symm ha
  refine ⟨a, ?_, ?_, ?_⟩
  · intro t ht
    have ht' : t ≤ σ := by simpa only [hu] using ht
    have h := ha ⟨t, t.property, by exact_mod_cast ht'⟩
    simpa only [processPath_apply_of_continuous hc] using h
  · intro b hb
    apply huq b
    intro t
    have ht : (⟨t, t.property.1⟩ : ℝ≥0) ≤ (anchoredProcessLifetime B ε ω).untopD 0 := by
      rw [hu]
      exact t.property.2
    have h := hb ⟨t, t.property.1⟩ ht
    rw [← processPath_apply_of_continuous hc ⟨t, t.property.1⟩] at h
    exact h
  · simpa only [hu, processPath_apply_of_continuous hc] using hboundary

/-- Neither fitted boundary anchor admits a line of any positive future
length after the actual pinch lifetime. -/
theorem brownian_boundary_anchor_no_fit_after_lifetime_ae (hB : IsBrownianReal B μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, ∀ a : ℝ, ∀ δ : ℝ≥0, 0 < δ →
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        ε < |B ((anchoredProcessLifetime B ε ω).untopD 0 + t) ω -
          (B ((anchoredProcessLifetime B ε ω).untopD 0) ω + ε) - a * (t : ℝ)|) ∧
      (∃ t : ℝ≥0, 0 < t ∧ t < δ ∧
        ε < |B ((anchoredProcessLifetime B ε ω).untopD 0 + t) ω -
          (B ((anchoredProcessLifetime B ε ω).untopD 0) ω - ε) - a * (t : ℝ)|) := by
  filter_upwards [brownian_oscillation_after_anchoredLifetime_ae hB hε] with ω hω
  intro a δ hδ
  obtain ⟨⟨u, hu, huδ, hup⟩, ⟨v, hv, hvδ, hvn⟩⟩ := hω a δ hδ
  constructor
  · refine ⟨v, hv, hvδ, ?_⟩
    have := neg_le_abs (B ((anchoredProcessLifetime B ε ω).untopD 0 + v) ω -
      (B ((anchoredProcessLifetime B ε ω).untopD 0) ω + ε) - a * (v : ℝ))
    linarith
  · refine ⟨u, hu, huδ, ?_⟩
    have := le_abs_self (B ((anchoredProcessLifetime B ε ω).untopD 0 + u) ω -
      (B ((anchoredProcessLifetime B ε ω).untopD 0) ω - ε) - a * (u : ℝ))
    linarith

end BrownianAffine
