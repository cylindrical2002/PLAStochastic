import PLAStochastic.Affine.Lifetime.Pathwise

/-!
# The unique line at a finite anchored lifetime

These are deterministic statements about the actual continuous-path fitting
functional. The initial residual may be any value strictly inside the band.
The first strict exceedance is not identified here with the first time that
the cone becomes a singleton: arbitrary continuous paths may have plateaus.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

/-- A positive minimax error with an interior initial residual admits only one
feasible anchored slope. Two different slopes would give a strictly better
midpoint line, uniformly by compactness. -/
theorem anchored_feasible_slope_unique {T ε : ℝ} (hT : 0 ≤ T) (hε : 0 < ε)
    (f : Path T) (hzero : |f ⟨0, le_rfl, hT⟩| < ε)
    (herr : anchoredError f = ε) {a b : ℝ}
    (ha : ∀ t : Icc (0 : ℝ) T, |f t - a * (t : ℝ)| ≤ ε)
    (hb : ∀ t : Icc (0 : ℝ) T, |f t - b * (t : ℝ)| ≤ ε) : a = b := by
  suffices hlt : ∀ a b : ℝ, a < b →
      (∀ t : Icc (0 : ℝ) T, |f t - a * (t : ℝ)| ≤ ε) →
      (∀ t : Icc (0 : ℝ) T, |f t - b * (t : ℝ)| ≤ ε) → False by
    rcases lt_trichotomy a b with h | h | h
    · exact (hlt a b h ha hb).elim
    · exact h
    · exact (hlt b a h hb ha).elim
  intro a b hab ha hb
  have hd : dist f (((a + b) / 2) • timePath T) < ε := by
    apply (ContinuousMap.dist_lt_iff hε).mpr
    intro t
    simp only [ContinuousMap.smul_apply, timePath, ContinuousMap.coe_mk, smul_eq_mul,
      Real.dist_eq]
    by_cases ht : (t : ℝ) = 0
    · have heq : t = ⟨0, le_rfl, hT⟩ := Subtype.ext ht
      simpa only [ht, mul_zero, sub_zero, heq] using hzero
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (Ne.symm ht)
      have habt := mul_lt_mul_of_pos_right hab htpos
      have ha' := abs_le.mp (ha t)
      have hb' := abs_le.mp (hb t)
      apply abs_lt.mpr
      constructor <;> nlinarith
  have hle : anchoredError f ≤ dist f (((a + b) / 2) • timePath T) :=
    Metric.infDist_le_dist_of_mem (Submodule.mem_span_singleton.mpr ⟨(a + b) / 2, rfl⟩)
  exact (herr ▸ hle).not_gt hd

/-- The exact closed tail also holds for an interior nonzero initial residual. -/
theorem le_anchoredLifetime_iff_of_initial (f : C(ℝ, ℝ)) {ε : ℝ}
    (hzero : |f 0| ≤ ε) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ anchoredLifetime f ε ↔ anchoredTimeError f t ≤ ε := by
  apply le_firstExceedance_iff (anchoredTimeError_nnreal_monotone f)
    ((continuous_anchoredTimeError f).comp continuous_subtype_val)
  simpa only [NNReal.coe_zero, anchoredTimeError_zero] using hzero

/-- At a finite endpoint the continuous error equals the budget. -/
theorem anchoredTimeError_at_lifetime (f : C(ℝ, ℝ)) {ε : ℝ}
    (hzero : |f 0| ≤ ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ) :
    anchoredTimeError f σ = ε := by
  have hle : anchoredTimeError f σ ≤ ε :=
    (le_anchoredLifetime_iff_of_initial f hzero σ).mp hσ.ge
  apply le_antisymm hle
  by_contra h
  have hlt : anchoredTimeError f σ < ε := lt_of_not_ge h
  have hn : {t : ℝ≥0 | anchoredTimeError f t < ε} ∈ 𝓝 σ :=
    (isOpen_lt ((continuous_anchoredTimeError f).comp continuous_subtype_val)
      continuous_const).mem_nhds hlt
  obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds hn (exists_gt σ)
  obtain ⟨v, hσv, hvu⟩ := exists_between hu
  have hv : anchoredTimeError f v ≤ ε := (hsub ⟨hσv.le, hvu⟩).le
  have hvσ := (le_anchoredLifetime_iff_of_initial f hzero v).mpr hv
  rw [hσ] at hvσ
  exact hσv.not_ge (ENNReal.coe_le_coe.mp hvσ)

/-- The unique feasible line exists at every finite anchored lifetime whose
initial residual is strictly inside the band. -/
theorem existsUnique_anchored_fit_at_lifetime (f : C(ℝ, ℝ)) {ε : ℝ}
    (hzero : |f 0| < ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ) :
    ∃! a : ℝ, ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε := by
  have hε : 0 < ε := (abs_nonneg _).trans_lt hzero
  have herr : anchoredError (intervalPath f σ) = ε := by
    exact (anchoredTimeError_eq_interval σ.property f).symm.trans
      (anchoredTimeError_at_lifetime f hzero.le hσ)
  obtain ⟨a, ha⟩ := (anchoredError_le_iff_exists_fit σ.property (intervalPath f σ)).mp herr.le
  refine ⟨a, ha, fun b hb => ?_⟩
  exact anchored_feasible_slope_unique σ.property hε (intervalPath f σ) hzero herr hb ha

/-- If a line fits through the last feasible time, its residual there lies on
the boundary. A strict terminal residual would extend this same line. -/
theorem anchored_fit_terminal_boundary (f : C(ℝ, ℝ)) {ε : ℝ}
    (hzero : |f 0| ≤ ε) {σ : ℝ≥0} (hσ : anchoredLifetime f ε = σ)
    {a : ℝ} (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε) :
    |f σ - a * (σ : ℝ)| = ε := by
  have hle : |f σ - a * (σ : ℝ)| ≤ ε := ha ⟨σ, σ.property, le_rfl⟩
  apply le_antisymm hle
  by_contra h
  have hlt : |f σ - a * (σ : ℝ)| < ε := lt_of_not_ge h
  have hn : {t : ℝ | |f t - a * t| < ε} ∈ 𝓝 (σ : ℝ) :=
    (isOpen_lt (f.continuous.sub (continuous_const.mul continuous_id)).abs
      continuous_const).mem_nhds hlt
  obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds hn (exists_gt (σ : ℝ))
  obtain ⟨v, hσv, hvu⟩ := exists_between hu
  have hv0 : 0 ≤ v := σ.property.trans hσv.le
  have hfit : ∀ t : Icc (0 : ℝ) v, |f t - a * (t : ℝ)| ≤ ε := by
    intro t
    by_cases ht : (t : ℝ) ≤ σ
    · exact ha ⟨t, t.property.1, ht⟩
    · exact (hsub ⟨le_of_lt (lt_of_not_ge ht), t.property.2.trans_lt hvu⟩).le
  have herr : anchoredTimeError f v ≤ ε := by
    rw [anchoredTimeError_eq_interval hv0 f]
    exact (anchoredError_le_iff_exists_fit hv0 (intervalPath f v)).mpr ⟨a, hfit⟩
  have hvσ := (le_anchoredLifetime_iff_of_initial f hzero ⟨v, hv0⟩).mpr herr
  rw [hσ] at hvσ
  exact hσv.not_ge (ENNReal.coe_le_coe.mp hvσ)

end BrownianAffine
