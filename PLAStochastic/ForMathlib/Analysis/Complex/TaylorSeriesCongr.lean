import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesBudget
import PLAStochastic.ForMathlib.Analysis.Asymptotics.SeriesApproxUnique

/-! # Finite Taylor-jet congruence from an analytic difference budget -/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries Asymptotics
namespace PGM

theorem exists_seriesApprox_of_analyticAt {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (N : ℕ) :
    ∃ K R : ℝ, 0 ≤ K ∧ 0 < R ∧ ∀ b : ℝ, 0 ≤ b → b < R →
      SeriesApprox (f b) (complexTaylorSeries f 0) N b K := by
  have hev : ∀ᶠ z : ℂ in 𝓝 0, DifferentiableAt ℂ f z ∧ ‖f z‖ < ‖f 0‖ + 1 :=
    (analyticAt_iff_eventually_differentiableAt.mp hf).and
      (hf.continuousAt.norm.eventually (isOpen_Iio.mem_nhds (show ‖f 0‖ < ‖f 0‖ + 1 by linarith)))
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨complexTaylorBudgetConstant N R (‖f 0‖ + 1), R / 2,
    complexTaylorBudgetConstant_nonneg N hR (by positivity), half_pos hR, ?_⟩
  intro b hb hbR
  have hbs : (b : ℂ) ∈ ball (0 : ℂ) ((R / 1) / 2) := by
    simpa only [div_one, mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_nonneg hb] using hbR
  simpa only [one_pow, mul_one] using
    seriesApprox_of_polynomial_disc (f := f) hR (le_refl (1 : ℝ))
      (by positivity : 0 ≤ ‖f 0‖ + 1) 0 N
      (by
        rw [div_one]
        intro z hz
        exact (hball hz).1.differentiableWithinAt)
      (by
        simp only [div_one, one_pow, mul_one]
        intro z hz
        exact (hball hz).2.le) hb hbs

theorem complexTaylorSeries_coeff_eq_of_difference_le {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (N : ℕ) {K R : ℝ}
    (hR : 0 < R) (hK : 0 ≤ K)
    (hfg : ∀ b : ℝ, 0 < b → b < R → ‖f b - g b‖ ≤ K * b ^ (N + 1)) :
    ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries g 0) := by
  obtain ⟨L, S, hL, hS, hgS⟩ := exists_seriesApprox_of_analyticAt hg N
  obtain ⟨Kf, T, _, hT, hfT⟩ := exists_seriesApprox_of_analyticAt hf N
  have happrox : ∀ b : ℝ, 0 < b → b < min R S →
      SeriesApprox (f b) (complexTaylorSeries g 0) N b (K + L) := by
    intro b hb hbRS
    have hgB := hgS b hb.le (hbRS.trans_le (min_le_right _ _))
    refine ⟨fun j hj => (hgB.1 j hj).trans (by linarith), ?_⟩
    calc
      _ ≤ ‖f b - g b‖ + ‖g b - truncEval (complexTaylorSeries g 0) N b‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ K * b ^ (N + 1) + L * b ^ (N + 1) :=
        add_le_add (hfg b hb (hbRS.trans_le (min_le_left _ _))) hgB.2
      _ = _ := by ring
  intro j hj
  exact seriesApprox_coeff_eq_of_small_scale hT (lt_min hR hS)
    (fun b hb hbT => hfT b hb.le hbT) happrox hj hj

theorem complexTaylorSeries_coeff_eq_of_isBigO {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (N : ℕ)
    (hfg : (fun b => f b - g b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1))) :
    ∀ j ≤ N, coeff j (complexTaylorSeries f 0) = coeff j (complexTaylorSeries g 0) := by
  obtain ⟨K, hK, hbound⟩ := hfg.exists_nonneg
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hbound.bound
  apply complexTaylorSeries_coeff_eq_of_difference_le hf hg N hR hK
  intro b hb hbR
  have hbs : (b : ℂ) ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball_zero_iff, norm_real, Real.norm_eq_abs, abs_of_pos hb] using hbR
  simpa only [Set.mem_ofPred_eq, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hb] using hball hbs

end PGM
