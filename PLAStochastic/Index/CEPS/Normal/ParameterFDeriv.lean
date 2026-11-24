import PLAStochastic.Index.CEPS.Normal.JointDerivative

/-! # Compact parameter integration with a continuous actual derivative -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

/-- A finite-dimensional parameter version. The derivative is an explicit
actual joint derivative; compactness supplies its local uniform bound.
-/
theorem cepsNormal_hasFDerivAt_parameterIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {U : Set E} (hU : IsOpen U) {F : E → ℝ → ℂ} {F' : E → ℝ → E →L[ℂ] ℂ}
    (hc : ContinuousOn (fun x : E × ℝ => F x.1 x.2) (U ×ˢ Icc 0 1))
    (hdc : ContinuousOn (fun x : E × ℝ => F' x.1 x.2) (U ×ˢ Icc 0 1))
    (hd : ∀ r ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, HasFDerivAt (fun r => F r s) (F' r s) r)
    {r₀ : E} (hr₀ : r₀ ∈ U) :
    HasFDerivAt (fun r => ∫ s in (0 : ℝ)..1, F r s)
      (∫ s in (0 : ℝ)..1, F' r₀ s) r₀ := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU r₀ hr₀
  let R := ε / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hsub : closedBall r₀ R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans hεU
  have hball : ball r₀ R ⊆ U := ball_subset_closedBall.trans hsub
  have hcompact := (isCompact_closedBall r₀ R).prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
    (hdc.mono (fun x hx => ⟨hsub hx.1, hx.2⟩))
  have hs : ∀ r ∈ U, ContinuousOn (F r) (Icc (0 : ℝ) 1) := fun r hr =>
    hc.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun _ ht => ⟨hr, ht⟩)
  have hs' : ContinuousOn (F' r₀) (Icc (0 : ℝ) 1) :=
    hdc.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun _ ht => ⟨hr₀, ht⟩)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := 0) (b := 1) (s := ball r₀ R) (bound := fun _ => M)
    (ball_mem_nhds r₀ hR)
  · filter_upwards [ball_mem_nhds r₀ hR] with r hr
    rw [uIoc_of_le zero_le_one]
    exact ((hs r (hball hr)).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · exact (hs r₀ hr₀).intervalIntegrable_of_Icc zero_le_one
  · rw [uIoc_of_le zero_le_one]
    exact (hs'.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun s hs r hr => ?_
    rw [uIoc_of_le zero_le_one] at hs
    exact hM (r, s) ⟨ball_subset_closedBall hr, Ioc_subset_Icc_self hs⟩
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun s hs r hr => ?_
    rw [uIoc_of_le zero_le_one] at hs
    exact hd r (hball hr) s (Ioc_subset_Icc_self hs)

theorem cepsNormal_hasDerivAt_parameterIntegral
    {U : Set ℂ} (hU : IsOpen U) {F D : ℂ → ℝ → ℂ}
    (hc : ContinuousOn (fun x : ℂ × ℝ => F x.1 x.2) (U ×ˢ Icc 0 1))
    (hdc : ContinuousOn (fun x : ℂ × ℝ => D x.1 x.2) (U ×ˢ Icc 0 1))
    (hd : ∀ r ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt (fun r => F r s) (D r s) r)
    {r₀ : ℂ} (hr₀ : r₀ ∈ U) :
    HasDerivAt (fun r => ∫ s in (0 : ℝ)..1, F r s)
      (∫ s in (0 : ℝ)..1, D r₀ s) r₀ := by
  let D' : ℂ → ℝ → ℂ →L[ℂ] ℂ := fun r s =>
    (ContinuousLinearMap.id ℂ ℂ).smulRight (D r s)
  have hdc' : ContinuousOn (fun x : ℂ × ℝ => D' x.1 x.2) (U ×ˢ Icc 0 1) := by
    have he : (fun x : ℂ × ℝ => D' x.1 x.2) =
        fun x => D x.1 x.2 • (ContinuousLinearMap.id ℂ ℂ) := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp [D', smul_eq_mul, mul_comm]
    rw [he]
    exact hdc.smul continuousOn_const
  have hmain := cepsNormal_hasFDerivAt_parameterIntegral (F := F) (F' := D')
    hU hc hdc' (fun r hr s hs => (hd r hr s hs).hasFDerivAt) hr₀
  have hint : IntervalIntegrable (D' r₀) volume 0 1 :=
    (hdc'.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun _ hs => ⟨hr₀, hs⟩)).intervalIntegrable_of_Icc zero_le_one
  apply hmain.hasDerivAt.congr_deriv
  rw [ContinuousLinearMap.intervalIntegral_apply hint]
  simp [D']

end PGM
