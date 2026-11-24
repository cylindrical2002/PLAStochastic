import PLAStochastic.Index.CEPS.Reward.TruncatedMark
import PLAStochastic.Index.CEPS.Reward.Moment

/-! # Truncated complex mark sources and renewal solutions converge -/

noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace PGM.WienerHopf

variable {g : ℝ → ℂ} {D θ : ℝ} {a : ℂ}

theorem rewardTestSource_truncatedMark_tendsto (hg : IsExpDensity g D θ)
    (ha : ‖a‖ < θ) (x : ℝ) :
    Tendsto (fun n => rewardTestSource g (truncatedMark a n) x) atTop
      (𝓝 (rewardSource g a x)) := by
  let B : ℝ → ℝ := (Ioi x).indicator
    (fun h => D * Real.exp (-‖a‖ * x) * Real.exp ((‖a‖ - θ) * h))
  have hIo : IntegrableOn (fun h : ℝ =>
      D * Real.exp (-‖a‖ * x) * Real.exp ((‖a‖ - θ) * h)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (show ‖a‖ - θ < 0 by linarith) x).const_mul _
  have hi : Integrable B := hIo.integrable_indicator measurableSet_Ioi
  change Tendsto (fun n => ∫ h, if x < h then truncatedMark a n (h - x) * g h else 0)
    atTop (𝓝 (∫ h, if x < h then cexp (-a * (h - x : ℝ)) * g h else 0))
  apply tendsto_integral_of_dominated_convergence B
    (fun n => (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (((measurable_truncatedMark a n).comp (measurable_id.sub measurable_const)).mul
        hg.measurable) measurable_const).aestronglyMeasurable) hi
  · intro n
    exact Eventually.of_forall fun h => by
      change ‖if x < h then truncatedMark a n (h - x) * g h else 0‖ ≤ B h
      by_cases hh : x < h
      · simp only [if_pos hh, B, indicator_of_mem (show h ∈ Ioi x from hh)]
        simpa only [one_mul] using rewardTestSource_integrand_le hg (B := 1) (κ := ‖a‖)
          (fun y hy => by simpa using norm_truncatedMark_le_exp a n hy) hh
      · simp only [if_neg hh, norm_zero, B, indicator_of_notMem (show h ∉ Ioi x from hh)]
        rfl
  · exact Eventually.of_forall fun h => by
      change Tendsto (fun n => if x < h then truncatedMark a n (h - x) * g h else 0)
        atTop (𝓝 (if x < h then cexp (-a * (h - x : ℝ)) * g h else 0))
      by_cases hh : x < h
      · simp only [if_pos hh]
        exact (truncatedMark_tendsto a (by linarith)).mul_const (g h)
      · simp only [if_neg hh]
        exact tendsto_const_nhds

theorem rewardTestSolution_truncatedMark_tendsto (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => rewardSolution g (rewardTestSource g (truncatedMark a n)) x) atTop
      (𝓝 (rewardSolution g (rewardSource g a) x)) := by
  let C := D / (θ - ‖a‖)
  let M := D * Real.exp (D * x)
  have hC : 0 ≤ C := div_nonneg hg.nonneg_D (by linarith)
  have hM : 0 ≤ M := mul_nonneg hg.nonneg_D (Real.exp_pos _).le
  have hSbound : ∀ n z, 0 ≤ z → ‖rewardTestSource g (truncatedMark a n) z‖ ≤ C := by
    intro n z hz
    have hb := norm_rewardTestSource_le hg (measurable_truncatedMark a n) (B := 1) (κ := ‖a‖)
      (fun y hy => by simpa using norm_truncatedMark_le_exp a n hy) ha z
    simp only [one_mul] at hb
    exact hb.trans (mul_le_of_le_one_right hC
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz)))
  have hu := halfBdd_renewalDensity hg hθ
  have ht : Tendsto (fun n => ∫ z in Ioo 0 x,
      renewalDensity g (x - z) * rewardTestSource g (truncatedMark a n) z) atTop
      (𝓝 (∫ z in Ioo 0 x, renewalDensity g (x - z) * rewardSource g a z)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M * C)
      (fun n => ((hu.measurable.comp (measurable_const.sub measurable_id)).mul
        (measurable_rewardTestSource hg (measurable_truncatedMark a n))).aestronglyMeasurable)
      (integrableOn_const (C := M * C) (isCompact_Icc.measure_lt_top.ne) |>.mono_set Ioo_subset_Icc_self)
    · intro n
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun z hz => by
        change ‖renewalDensity g (x - z) * rewardTestSource g (truncatedMark a n) z‖ ≤ M * C
        rw [norm_mul]
        have hU : ‖renewalDensity g (x - z)‖ ≤ M := by
          simpa only [max_eq_left hx] using norm_renewalDensity_le_of_le hg hθ
            (show x - z ≤ x by linarith [hz.1])
        exact mul_le_mul hU (hSbound n z hz.1.le) (norm_nonneg _) hM)
    · exact Eventually.of_forall fun z =>
        tendsto_const_nhds.mul (rewardTestSource_truncatedMark_tendsto hg ha z)
  change Tendsto (fun n => halfLine (rewardTestSource g (truncatedMark a n)) x +
    convC (renewalDensity g) (halfLine (rewardTestSource g (truncatedMark a n))) x)
    atTop (𝓝 (halfLine (rewardSource g a) x +
      convC (renewalDensity g) (halfLine (rewardSource g a)) x))
  simp_rw [halfLine_of_nonneg _ hx, convC_halfLine_eq_interval hu]
  exact (rewardTestSource_truncatedMark_tendsto hg ha x).add ht

end PGM.WienerHopf
