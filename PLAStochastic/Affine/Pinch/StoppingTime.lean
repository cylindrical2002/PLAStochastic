import PLAStochastic.Affine.Process.Markov.AugmentedFiltration
import PLAStochastic.Affine.Pinch.UniqueLine
import PLAStochastic.Affine.Lifetime.ToleranceMoments

/-!
# The actual first closed-budget hitting time is a stopping time

This uses a proved measurable continuous path version and its augmented natural
filtration. The closed-budget hitting time is not silently replaced by the
first strict exceedance. Equality with the latter requires Brownian oscillation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- First time the continuous monotone error reaches the closed budget. -/
def firstReach (D : ℝ≥0 → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if ε ≤ D t then (t : ℝ≥0∞) else ⊤

theorem firstReach_le_of_reaches {D : ℝ≥0 → ℝ} {ε : ℝ} {t : ℝ≥0}
    (ht : ε ≤ D t) : firstReach D ε ≤ (t : ℝ≥0∞) :=
  (iInf_le _ t).trans_eq (if_pos ht)

theorem le_firstReach_of_error_lt {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hD : Monotone D) {t : ℝ≥0} (ht : D t < ε) :
    (t : ℝ≥0∞) ≤ firstReach D ε := by
  apply le_iInf
  intro s
  split_ifs with hs
  · exact_mod_cast (show t ≤ s by
      by_contra h
      exact ht.not_ge (hs.trans (hD (le_of_not_ge h))))
  · exact le_top

/-- Closed hitting gives a genuine stopping-time event at the same time T. -/
theorem firstReach_le_iff {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hmono : Monotone D) (hcont : Continuous D) (t : ℝ≥0) :
    firstReach D ε ≤ (t : ℝ≥0∞) ↔ ε ≤ D t := by
  refine ⟨fun ht => ?_, firstReach_le_of_reaches⟩
  by_contra h
  have hn : {s : ℝ≥0 | D s < ε} ∈ 𝓝 t :=
    (isOpen_lt hcont continuous_const).mem_nhds (lt_of_not_ge h)
  obtain ⟨u, hu, hsub⟩ := exists_Ico_subset_of_mem_nhds hn (exists_gt t)
  obtain ⟨v, htv, hvu⟩ := exists_between hu
  have hle := (le_firstReach_of_error_lt hmono (hsub ⟨htv.le, hvu⟩)).trans ht
  exact htv.not_ge (ENNReal.coe_le_coe.mp hle)

theorem firstReach_le_firstExceedance (D : ℝ≥0 → ℝ) (ε : ℝ) :
    firstReach D ε ≤ firstExceedance D ε := by
  apply le_iInf
  intro t
  split_ifs with ht
  · exact firstReach_le_of_reaches ht.le
  · exact le_top

/-- Continuity makes the finite first reached value equal the budget. -/
theorem error_at_firstReach {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hmono : Monotone D) (hcont : Continuous D) (hzero : D 0 < ε)
    {σ : ℝ≥0} (hσ : firstReach D ε = σ) : D σ = ε := by
  have hge := (firstReach_le_iff hmono hcont σ).mp hσ.le
  apply le_antisymm ?_ hge
  by_contra h
  obtain ⟨s, hsσ, hs⟩ := exists_earlier_exceedance hcont hzero.le (lt_of_not_ge h)
  have hle := firstReach_le_of_reaches hs.le
  rw [hσ] at hle
  exact hsσ.not_ge (ENNReal.coe_le_coe.mp hle)

/-- Mixing an earlier strict fit with a line that has a strict final-region
margin gives a strict fit on the full compact interval. -/
theorem anchoredError_lt_of_prefix_and_terminal_margin {T u ε d a b : ℝ}
    (hT : 0 ≤ T) (hd : 0 < d) (f : Path T)
    (ha : ∀ t : Icc (0 : ℝ) T, |f t - a * (t : ℝ)| ≤ ε)
    (hb : ∀ t : Icc (0 : ℝ) T, (t : ℝ) ≤ u → |f t - b * (t : ℝ)| < ε)
    (htail : ∀ t : Icc (0 : ℝ) T, u < (t : ℝ) → |f t - a * (t : ℝ)| < ε - d)
    (hε : 0 < ε) : anchoredError f < ε := by
  let C := |b - a| * T
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) hT
  let l := min (1 / 2 : ℝ) (d / (2 * (C + 1)))
  have hl : 0 < l := lt_min (by norm_num) (div_pos hd (by positivity))
  have hl1 : l ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hlC : l * C < d := by
    have hh : l * (2 * (C + 1)) ≤ d :=
      (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    nlinarith
  have hdist : dist f (((1 - l) * a + l * b) • timePath T) < ε := by
    apply (ContinuousMap.dist_lt_iff hε).mpr
    intro t
    simp only [ContinuousMap.smul_apply, timePath, ContinuousMap.coe_mk, smul_eq_mul,
      Real.dist_eq]
    by_cases ht : (t : ℝ) ≤ u
    · have ha' := abs_le.mp (ha t)
      have hb' := abs_lt.mp (hb t ht)
      have hlo := mul_pos hl (sub_pos.mpr hb'.1)
      have hhi := mul_pos hl (sub_pos.mpr hb'.2)
      have hlo' := mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr ha'.1)
      have hhi' := mul_nonneg (sub_nonneg.mpr hl1) (sub_nonneg.mpr ha'.2)
      apply abs_lt.mpr
      constructor <;> nlinarith
    · have htail' := htail t (lt_of_not_ge ht)
      have hbound : |l * (b - a) * (t : ℝ)| ≤ l * C := by
        rw [abs_mul, abs_mul, abs_of_pos hl, abs_of_nonneg t.property.1]
        simpa only [C, mul_assoc] using
          mul_le_mul_of_nonneg_left t.property.2 (mul_nonneg hl.le (abs_nonneg (b - a)))
      calc
        |f t - ((1 - l) * a + l * b) * (t : ℝ)| =
            |(f t - a * (t : ℝ)) - l * (b - a) * (t : ℝ)| := by congr 1; ring
        _ ≤ |f t - a * (t : ℝ)| + |l * (b - a) * (t : ℝ)| := abs_sub _ _
        _ < ε := by linarith
  exact lt_of_le_of_lt
    (Metric.infDist_le_dist_of_mem (Submodule.mem_span_singleton.mpr
      ⟨(1 - l) * a + l * b, rfl⟩)) hdist

/-- The line at the first closed-budget hitting time touches the band at its
terminal time. This uses strictly smaller errors at every earlier time. -/
theorem anchored_fit_firstReach_terminal_boundary (f : C(ℝ, ℝ)) {ε : ℝ}
    (hzero : |f 0| < ε) {σ : ℝ≥0}
    (hσ : firstReach (fun t : ℝ≥0 => anchoredTimeError f t) ε = σ)
    {a : ℝ} (ha : ∀ t : Icc (0 : ℝ) (σ : ℝ), |f t - a * (t : ℝ)| ≤ ε) :
    |f σ - a * (σ : ℝ)| = ε := by
  have hmono := anchoredTimeError_nnreal_monotone f
  have hc : Continuous (fun t : ℝ≥0 => anchoredTimeError f t) :=
    (continuous_anchoredTimeError f).comp continuous_subtype_val
  have hz : anchoredTimeError f (0 : ℝ≥0) < ε := by
    simpa only [NNReal.coe_zero, anchoredTimeError_zero] using hzero
  have herr := error_at_firstReach hmono hc hz hσ
  have hσpos : 0 < (σ : ℝ) := by
    by_contra h
    have hσ0 : σ = 0 := NNReal.coe_eq_zero.mp (le_antisymm (le_of_not_gt h) σ.property)
    rw [hσ0] at herr
    exact hz.ne herr
  have hle : |f σ - a * (σ : ℝ)| ≤ ε := ha ⟨σ, σ.property, le_rfl⟩
  apply le_antisymm hle
  by_contra h
  have hlt : |f σ - a * (σ : ℝ)| < ε := lt_of_not_ge h
  let d := (ε - |f σ - a * (σ : ℝ)|) / 2
  have hd : 0 < d := by dsimp only [d]; linarith
  have hmargin : |f σ - a * (σ : ℝ)| < ε - d := by dsimp only [d]; linarith
  have hn : {t : ℝ | |f t - a * t| < ε - d} ∈ 𝓝 (σ : ℝ) :=
    (isOpen_lt (f.continuous.sub (continuous_const.mul continuous_id)).abs
      continuous_const).mem_nhds hmargin
  obtain ⟨u, hu, htail⟩ := exists_Ioc_subset_of_mem_nhds' hn hσpos
  have hu0 := hu.1
  have huσ := hu.2
  have hu0' : 0 ≤ u := hu0
  have herru : anchoredTimeError f u < ε := by
    by_contra h
    have hle' := (firstReach_le_iff hmono hc (⟨u, hu0'⟩ : ℝ≥0)).mpr (le_of_not_gt h)
    rw [hσ] at hle'
    exact huσ.not_ge (ENNReal.coe_le_coe.mp hle')
  obtain ⟨b, hb⟩ := exists_anchored_minimizer (intervalPath f u)
  have hbstrict : ∀ t : Icc (0 : ℝ) u, |f t - b * (t : ℝ)| < ε := by
    have hd' : dist (intervalPath f u) (b • timePath u) < ε := by
      rw [← hb]
      exact (anchoredTimeError_eq_interval hu0' f).symm ▸ herru
    simpa only [Real.dist_eq, ContinuousMap.smul_apply, smul_eq_mul, timePath,
      ContinuousMap.coe_mk, intervalPath, ContinuousMap.restrict_apply] using
      (ContinuousMap.dist_lt_iff ((abs_nonneg _).trans_lt hzero)).mp hd'
  have hcontr : anchoredError (intervalPath f σ) < ε :=
    anchoredError_lt_of_prefix_and_terminal_margin σ.property hd (intervalPath f σ) ha
      (fun t ht => hbstrict ⟨t, t.property.1, ht⟩)
      (fun t ht => htail ⟨ht, t.property.2⟩) ((abs_nonneg _).trans_lt hzero)
  exact herr.not_lt ((anchoredTimeError_eq_interval σ.property f).trans_lt hcontr)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A first pinch defined from the actual path functional on its proved
measurable continuous version. It will be identified with the actual lifetime. -/
def brownianFirstPinch (hB : IsBrownianReal B μ) (ε : ℝ) (ω : Ω) : ℝ≥0∞ :=
  firstReach (fun t : ℝ≥0 => anchoredTimeError (continuousBrownianPath hB ω) t) ε

theorem brownianFirstPinch_le_iff (hB : IsBrownianReal B μ) (ε : ℝ) (T : ℝ≥0) (ω : Ω) :
    brownianFirstPinch hB ε ω ≤ (T : ℝ≥0∞) ↔
      ε ≤ anchoredTimeError (continuousBrownianPath hB ω) T :=
  firstReach_le_iff (anchoredTimeError_nnreal_monotone _)
    ((continuous_anchoredTimeError _).comp continuous_subtype_val) T

/-- This is a true stopping time in the explicitly defined augmented filtration. -/
theorem brownianFirstPinch_isStoppingTime (hB : IsBrownianReal B μ) (ε : ℝ) :
    IsStoppingTime (augmentedBrownianFiltration hB.toIsPreBrownianReal)
      (brownianFirstPinch hB ε) := by
  intro T
  have heq : {ω | brownianFirstPinch hB ε ω ≤ (T : WithTop ℝ≥0)} =
      {ω | ε ≤ anchoredTimeError (continuousBrownianPath hB ω) T} := by
    ext ω
    exact brownianFirstPinch_le_iff hB ε T ω
  rw [heq]
  exact measurableSet_le measurable_const (adapted_continuousBrownianError hB T)

theorem brownianFirstPinch_ae_pos (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, 0 < brownianFirstPinch hB ε ω := by
  filter_upwards [continuousBrownianPath_all_times_ae_eq hB, hB.eval_zero_ae_eq_zero] with ω hp hz
  apply lt_of_not_ge
  intro h
  have hx := (brownianFirstPinch_le_iff hB ε 0 ω).mp h
  rw [NNReal.coe_zero, anchoredTimeError_zero, ← NNReal.coe_zero, hp 0, hz, abs_zero] at hx
  exact hε.not_ge hx

theorem brownianFirstPinch_ae_ne_top (hB : IsBrownianReal B μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂μ, brownianFirstPinch hB ε ω ≠ ⊤ := by
  filter_upwards [continuousBrownianPath_ae_eq hB,
    anchoredProcessLifetime_tolerance_ae_ne_top hB hε] with ω hp hf
  have hle : brownianFirstPinch hB ε ω ≤ anchoredProcessLifetime B ε ω := by
    unfold brownianFirstPinch
    rw [hp]
    exact firstReach_le_firstExceedance _ _
  exact ne_top_of_le_ne_top hf hle

end BrownianAffine
