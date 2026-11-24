import PLAStochastic.Index.CEPS.Reward.ExponentialMoment

/-! # Truncated exponential marks and their probabilistic limit -/

noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace PGM.WienerHopf

def truncatedMark (a : ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  if 0 ≤ y ∧ y ≤ n then cexp (-a * y) else 0

theorem measurable_truncatedMark (a : ℂ) (n : ℕ) : Measurable (truncatedMark a n) := by
  unfold truncatedMark
  exact Measurable.ite measurableSet_Icc (by fun_prop) measurable_const

theorem norm_truncatedMark_le_exp (a : ℂ) (n : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    ‖truncatedMark a n y‖ ≤ Real.exp (‖a‖ * y) := by
  unfold truncatedMark
  split_ifs
  · rw [norm_cexp_mul_ofReal', neg_re, neg_neg]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      ((neg_le_abs _).trans (abs_re_le_norm a)) hy)
  · simpa using (Real.exp_pos (‖a‖ * y)).le

theorem norm_truncatedMark_le (a : ℂ) (n : ℕ) (y : ℝ) :
    ‖truncatedMark a n y‖ ≤ Real.exp (‖a‖ * n) := by
  by_cases hy : 0 ≤ y ∧ y ≤ n
  · exact (norm_truncatedMark_le_exp a n hy.1).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hy.2 (norm_nonneg _)))
  · simp only [truncatedMark, if_neg hy, norm_zero]
    exact (Real.exp_pos _).le

theorem truncatedMark_tendsto (a : ℂ) {y : ℝ} (hy : 0 ≤ y) :
    Tendsto (fun n => truncatedMark a n y) atTop (𝓝 (cexp (-a * y))) := by
  obtain ⟨N, hN⟩ := exists_nat_gt y
  have he : (fun n => truncatedMark a n y) =ᶠ[atTop] (fun _ => cexp (-a * y)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact if_pos ⟨hy, hN.le.trans (by exact_mod_cast hn)⟩
  exact tendsto_const_nhds.congr' he.symm

theorem passageTestReward_truncatedMark_tendsto (s a : ℂ) (x : ℝ) (ω : ℕ → ℝ) :
    Tendsto (fun n => passageTestReward s (truncatedMark a n) x ω) atTop
      (𝓝 (passageReward s a x ω)) := by
  by_cases h : firstEntry (Ioi x) ω < ⊤
  · simp only [passageTestReward, passageReward, if_pos h]
    exact tendsto_const_nhds.mul (truncatedMark_tendsto a (by
      exact sub_nonneg.mpr (entryValue_mem h).le))
  · simp only [passageTestReward, passageReward, if_neg h]
    exact tendsto_const_nhds

theorem norm_passageTestReward_truncatedMark_le {s : ℂ} (hs : ‖s‖ ≤ 1)
    (a : ℂ) (n : ℕ) (x : ℝ) (ω : ℕ → ℝ) :
    ‖passageTestReward s (truncatedMark a n) x ω‖ ≤ overshootExp ‖a‖ x ω := by
  by_cases h : firstEntry (Ioi x) ω < ⊤
  · simp only [passageTestReward, overshootExp, if_pos h, norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hs) (norm_nonneg _)).trans
      (by simpa using norm_truncatedMark_le_exp a n (sub_nonneg.mpr (entryValue_mem h).le))
  · simp [passageTestReward, overshootExp, h]

theorem norm_passageReward_le_overshootExp {s : ℂ} (hs : ‖s‖ ≤ 1)
    (a : ℂ) (x : ℝ) (ω : ℕ → ℝ) :
    ‖passageReward s a x ω‖ ≤ overshootExp ‖a‖ x ω := by
  exact le_of_tendsto (continuous_norm.tendsto _ |>.comp
    (passageTestReward_truncatedMark_tendsto s a x ω))
    (Eventually.of_forall fun n => norm_passageTestReward_truncatedMark_le hs a n x ω)

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ} {D θ : ℝ}

theorem integrable_passageReward_of_expDensity (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) 1) D θ) (hθ : 0 < θ)
    {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    Integrable (passageReward s a x) (pathLaw ρ) :=
  (integrable_overshootExp hf0 hfm hρ hg hθ ha hx).mono'
    ((measurable_passageReward s a).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    (Eventually.of_forall (norm_passageReward_le_overshootExp hs a x))

theorem passageTestTransform_truncatedMark_tendsto (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) 1) D θ) (hθ : 0 < θ)
    {s a : ℂ} (hs : ‖s‖ ≤ 1) (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n => passageTestTransform ρ s (truncatedMark a n) x) atTop
      (𝓝 (passageTransform ρ s a x)) := by
  apply tendsto_integral_of_dominated_convergence (overshootExp ‖a‖ x)
    (fun n => ((measurable_passageTestReward s (measurable_truncatedMark a n)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (integrable_overshootExp hf0 hfm hρ hg hθ ha hx)
  · exact fun n => Eventually.of_forall (norm_passageTestReward_truncatedMark_le hs a n x)
  · exact Eventually.of_forall (passageTestReward_truncatedMark_tendsto s a x)

end PGM.WienerHopf
