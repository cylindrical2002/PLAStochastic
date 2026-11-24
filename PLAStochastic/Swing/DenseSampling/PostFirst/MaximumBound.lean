import PLAStochastic.Swing.DenseSampling.Rejection.LocalizationErrors

/-! # A quantitative bound for the actual post-first maximum -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem integrable_nativeRejectionStateFailure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : ℕ → Ω → ℝ} (hY : ∀ j, AEMeasurable (Y j) μ)
    (γ : ℝ) {h : ℝ≥0} (hh : 0 < h) (n : ℕ) :
    Integrable (fun ω => nativeRejectionStateFailure (fun j => Y j ω) γ h n) μ := by
  apply Integrable.of_bound ((measurable_nativeRejectionStateFailure γ hh n).comp_aemeasurable
    (aemeasurable_pi_lambda _ hY)).aestronglyMeasurable 1
  apply ae_of_all
  intro ω
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs, abs_of_nonneg (nativeRejectionStateFailure_bounds _ _ _ _).1]
  exact (nativeRejectionStateFailure_bounds _ _ _ _).2

theorem integrable_brownianNativeHeightFailure {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ) (T K : ℝ) :
    Integrable (brownianNativeHeightFailure B T K) μ := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  apply Integrable.of_bound (aemeasurable_brownianNativeHeightFailure hB T K).aestronglyMeasurable 1
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (brownianNativeHeightFailure_bounds _ _ _ _).1]
  exact (brownianNativeHeightFailure_bounds _ _ _ _).2

/-- On the actual Brownian path, every positive maximum exceedance is charged
to a height exception, a boundary-state exception, or a real rejection cost. -/
theorem measureReal_nativePostFirstMaximum_le_localizations {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    {h : ℝ≥0} (hh : 0 < h) {a K M γ T : ℝ} (ha : 0 < a) {n N : ℕ}
    (hnT : (n : ℝ)*(h : ℝ) ≤ T) (hM : (2*K+2)/a ≤ M)
    (hN : ((N : ℝ)+1)*(h : ℝ) ≤ a) :
    μ.real {ω | a ≤ nativePostFirstMaximum (fun j => (j : ℝ)*(h : ℝ))
      (nativeStream (fun j => (j : ℝ)*(h : ℝ)) (fun j => B ((j : ℝ≥0)*h) ω) 1 n)} ≤
      (∫ ω, brownianNativeHeightFailure B T K ω ∂μ)+
      (∫ ω, nativeRejectionStateFailure (fun j => B ((j : ℝ≥0)*h) ω) γ h n ∂μ)+
      (∫ ω, ∑ b ∈ Finset.range (n+1), nativeRejectionLongCost
        (fun j => B ((j : ℝ≥0)*h) ω) M γ h N b ∂μ) := by
  let : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  let Y (j : ℕ) (ω : Ω) := B ((j : ℝ≥0)*h) ω
  let F (ω : Ω) := brownianNativeHeightFailure B T K ω+
    nativeRejectionStateFailure (fun j => Y j ω) γ h n+
    ∑ b ∈ Finset.range (n+1), nativeRejectionLongCost (fun j => Y j ω) M γ h N b
  have hI₁ := integrable_brownianNativeHeightFailure hB T K
  have hY : ∀ j, AEMeasurable (Y j) μ := fun _ => hB.aemeasurable _
  have hI₂ := integrable_nativeRejectionStateFailure hY γ hh n
  have hI₃ := integrable_finsetSum (Finset.range (n+1)) (fun b _ => integrable_nativeRejectionLongCost hY M γ hh N b)
  have hIF : Integrable F μ := (hI₁.add hI₂).add hI₃
  have hcost0 (ω : Ω) : 0 ≤ ∑ b ∈ Finset.range (n+1), nativeRejectionLongCost (fun j => Y j ω) M γ h N b :=
    Finset.sum_nonneg (fun b _ => (nativeRejectionLongCost_bounds _ _ _ _ _ _).1)
  have hF0 (ω : Ω) : 0 ≤ F ω := add_nonneg (add_nonneg
    (brownianNativeHeightFailure_bounds B T K ω).1 (nativeRejectionStateFailure_bounds _ _ _ _).1) (hcost0 ω)
  have hdom : {ω | a ≤ nativePostFirstMaximum (fun j => (j : ℝ)*(h : ℝ))
      (nativeStream (fun j => (j : ℝ)*(h : ℝ)) (fun j => B ((j : ℝ≥0)*h) ω) 1 n)} ≤ᵐ[μ]
      {ω | (1 : ℝ) ≤ F ω} := by
    filter_upwards [hB.cont] with ω hc hlong
    have h₁ := (brownianNativeHeightFailure_bounds B T K ω).1
    have h₂ := (nativeRejectionStateFailure_bounds (fun j => Y j ω) γ h n).1
    have h₃ := hcost0 ω
    by_cases hheight : ‖intervalPath (processPath B ω) T‖ ≤ K
    · by_cases hstate : ∀ b ≤ n, nativeRejectionAt (fun j => (j : ℝ)*(h : ℝ)) (fun j => Y j ω) 1 b →
          nativeRejectionState (fun j => (j : ℝ)*(h : ℝ)) (fun j => Y j ω) 1 b ≤ 2*γ
      · have hy : ∀ j ≤ n, |Y j ω| ≤ K := by
          intro j hj
          have hp := path_value_le_interval_norm (processPath B ω)
            (show (((j : ℝ≥0)*h : ℝ≥0) : ℝ) ∈ Icc (0 : ℝ) T from
              ⟨by positivity, (by simpa only [NNReal.coe_mul, NNReal.coe_natCast] using
                (mul_le_mul_of_nonneg_right (by exact_mod_cast hj : (j : ℝ) ≤ n) h.coe_nonneg).trans hnT)⟩)
          rw [processPath_apply_of_continuous hc] at hp
          exact hp.trans hheight
        have hs := nativePostFirstMaximum_long_le_rejection_sum (fun j => Y j ω) hh ha hy hM hN hstate hlong
        change 1 ≤ F ω
        dsimp only [F]
        linarith
      · have hf : nativeRejectionStateFailure (fun j => Y j ω) γ h n = 1 := if_neg hstate
        change 1 ≤ F ω
        dsimp only [F]
        rw [hf]
        linarith
    · have hf : brownianNativeHeightFailure B T K ω = 1 := if_neg hheight
      change 1 ≤ F ω
      dsimp only [F]
      rw [hf]
      linarith
  have hm := measureReal_le_integral_div_of_ae_dom (by norm_num : (0 : ℝ) < 1) hIF (ae_of_all _ hF0) hdom
  rw [div_one] at hm
  have hi : (∫ ω, F ω ∂μ) = (∫ ω, brownianNativeHeightFailure B T K ω ∂μ)+
      (∫ ω, nativeRejectionStateFailure (fun j => Y j ω) γ h n ∂μ)+
      (∫ ω, ∑ b ∈ Finset.range (n+1), nativeRejectionLongCost (fun j => Y j ω) M γ h N b ∂μ) := by
    exact (integral_add (hI₁.add hI₂) hI₃).trans (by dsimp only [Pi.add_apply]; rw [integral_add hI₁ hI₂])
  exact hm.trans_eq hi

end SwingRepair
