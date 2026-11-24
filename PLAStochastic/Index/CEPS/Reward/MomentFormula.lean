import PLAStochastic.Index.CEPS.Reward.Triangle
import PLAStochastic.Index.CEPS.Reward.Normalization

/-! # The main reward moment is a Laplace divided slope -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

theorem rewardTriangle_inner {g : ℝ → ℂ} {a β : ℂ} (hab : a + β ≠ 0)
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ z : ℝ, rewardTriangle g a β (z, h)) =
      (cexp (β * h) - cexp (-a * h)) * g h / (a + β) := by
  have he : ∀ z : ℝ, cexp (β * z) * cexp (-a * (h - z : ℝ)) =
      cexp (-a * h) * cexp ((a + β) * z) := by
    intro z
    rw [← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = ∫ z in Ioo 0 h, cexp (β * z) * cexp (-a * (h - z : ℝ)) * g h := by
      rw [← integral_indicator measurableSet_Ioo]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [rewardTriangle, indicator, mem_Ioo]
    _ = (cexp (-a * h) * g h) * ∫ z in Ioo 0 h, cexp ((a + β) * z) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro z _
      dsimp only
      rw [he]
      ring
    _ = (cexp (-a * h) * g h) *
        ((cexp ((a + β) * h) - 1) / (a + β)) := by
      rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hh,
        integral_exp_mul_complex hab]
      simp
    _ = _ := by
      have he' : cexp (-a * h) * cexp ((a + β) * h) = cexp (β * h) := by
        rw [← exp_add]
        congr 1
        ring
      calc
        _ = ((cexp (-a * h) * cexp ((a + β) * h) - cexp (-a * h)) * g h) /
            (a + β) := by ring
        _ = _ := by rw [he']

theorem laplaceC_eq_positiveIntegral {g : ℝ → ℂ} {D θ : ℝ}
    (hg : IsExpDensity g D θ) (β : ℂ) :
    laplaceC g β = ∫ h in Ioi (0 : ℝ), cexp (β * h) * g h := by
  rw [laplaceC]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro h hh
  rw [hg.eq_zero_of_nonpos h (by simpa using hh), mul_zero]

theorem rewardMoment_eq_quotient {g : ℝ → ℂ} {D θ κ : ℝ} (hg : IsExpDensity g D θ)
    {a β : ℂ} (ha : ‖a‖ ≤ κ) (hβ : ‖β‖ ≤ κ) (hκ : κ < θ) (hab : a + β ≠ 0) :
    rewardMoment β (rewardSource g a) = (laplaceC g β - laplaceC g (-a)) / (a + β) := by
  have hiβ := integrableOn_rewardMoment_tail hg.measurable
    (fun z _ => hg.norm_le z) hβ hκ (x := 0) le_rfl
  have hia := integrableOn_rewardMoment_tail hg.measurable
    (fun z _ => hg.norm_le z) (β := -a)
    (by simpa using ha) hκ (x := 0) le_rfl
  rw [rewardMoment_triangle_swap hg ha hβ hκ]
  calc
    _ = ∫ h in Ioi (0 : ℝ), (cexp (β * h) - cexp (-a * h)) * g h / (a + β) := by
      rw [← integral_indicator measurableSet_Ioi]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      by_cases hh : 0 < h
      · rw [indicator_of_mem (show h ∈ Ioi (0 : ℝ) from hh)]
        exact rewardTriangle_inner hab hh.le
      · rw [indicator_of_notMem (show h ∉ Ioi (0 : ℝ) from hh)]
        have hz : ∀ z : ℝ, ¬(0 < z ∧ z < h) := by
          intro z hz
          exact hh (hz.1.trans hz.2)
        simp only [rewardTriangle, hz, if_false, integral_zero]
    _ = _ := by
      rw [integral_div, laplaceC_eq_positiveIntegral hg β,
        laplaceC_eq_positiveIntegral hg (-a), ← integral_sub hiβ hia]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro h _
      dsimp only
      ring

variable {g : ℝ → ℂ} {D θ c K : ℝ} {β : ℂ} {L : ℂ → ℂ}

/-- The root case is paid by exact renewal normalization, rather than a singular quotient. -/
theorem rewardMoment_eq_dslope (h : ExpRenewalData g D θ c β L K)
    {a : ℂ} (ha : ‖a‖ ≤ c / 2) :
    rewardMoment β (rewardSource g a) = dslope (laplaceC g) β (-a) := by
  by_cases he : -a = β
  · have ha' : a = -β := by linear_combination -he
    rw [ha']
    have hn := rewardMoment_root_normalized h
    have hβ : |β.re| ≤ c := (abs_re_le_norm _).trans (h.root_le.trans (by linarith [h.c₀_pos]))
    have hne := h.dslope_ne_zero hβ
    change (dslope (laplaceC g) β β)⁻¹ * rewardMoment β (rewardSource g (-β)) = 1 at hn
    simpa only [neg_neg] using ((inv_mul_eq_one₀ hne).mp hn).symm
  · have hab : a + β ≠ 0 := by
      intro hz
      apply he
      linear_combination -hz
    rw [rewardMoment_eq_quotient h.density ha
      (h.root_le.trans (by linarith [h.c₀_pos])) (by linarith [h.c₀_lt, h.c₀_pos]) hab,
      dslope_of_ne _ he, slope_def_field, h.laplace_root]
    have hden : -a - β = -(a + β) := by ring
    rw [hden, div_neg]
    ring

end PGM.WienerHopf
