import PLAStochastic.Index.CEPS.Reward.Moment
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Fubini on the reward triangle

The exponential density envelope pays joint integrability on the unbounded
triangle before any interchange of integrals is used.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

def rewardTriangle (g : ℝ → ℂ) (a β : ℂ) (p : ℝ × ℝ) : ℂ :=
  if 0 < p.1 ∧ p.1 < p.2 then
    cexp (β * p.1) * cexp (-a * (p.2 - p.1 : ℝ)) * g p.2 else 0

variable {g : ℝ → ℂ} {D θ κ : ℝ} {a β : ℂ}

theorem measurable_rewardTriangle (hg : IsExpDensity g D θ) :
    Measurable (rewardTriangle g a β) := by
  apply Measurable.ite
    ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd))
  · exact (by fun_prop : Measurable (fun p : ℝ × ℝ =>
      cexp (β * p.1) * cexp (-a * (p.2 - p.1 : ℝ)))).mul
        (hg.measurable.comp measurable_snd)
  · exact measurable_const

theorem integrable_rewardTriangle (hg : IsExpDensity g D θ)
    (ha : ‖a‖ ≤ κ) (hβ : ‖β‖ ≤ κ) (hκ : κ < θ) :
    Integrable (rewardTriangle g a β) (volume.prod volume) := by
  let e := (θ - κ) / 2
  have he : 0 < e := by dsimp [e]; linarith
  let w : ℝ → ℝ := (Ioi 0).indicator (fun z => Real.exp (-e * z))
  have hw : Integrable w :=
    (integrableOn_exp_mul_Ioi (by linarith : -e < 0) 0).integrable_indicator measurableSet_Ioi
  have hB : Integrable (fun p : ℝ × ℝ => D * (w p.1 * w p.2)) (volume.prod volume) :=
    (hw.mul_prod hw).const_mul D
  refine hB.mono' (measurable_rewardTriangle hg).aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  have hD := hg.nonneg_D
  by_cases hp : 0 < p.1 ∧ p.1 < p.2
  · have hz : 0 ≤ p.1 := hp.1.le
    have hh : 0 < p.2 := hp.1.trans hp.2
    have hδ : 0 ≤ p.2 - p.1 := by linarith [hp.2]
    simp only [rewardTriangle, if_pos hp, norm_mul]
    rw [show w p.1 = Real.exp (-e * p.1) from
        indicator_of_mem (show p.1 ∈ Ioi (0 : ℝ) from hp.1) _,
      show w p.2 = Real.exp (-e * p.2) from
        indicator_of_mem (show p.2 ∈ Ioi (0 : ℝ) from hh) _]
    calc
      _ ≤ (Real.exp (κ * p.1) * Real.exp (κ * (p.2 - p.1))) *
          (D * Real.exp (-θ * p.2)) := by
        apply mul_le_mul _ (hg.norm_le _) (norm_nonneg _) (by positivity)
        apply mul_le_mul _ _ (norm_nonneg _) (Real.exp_pos _).le
        · rw [norm_cexp_mul_ofReal', neg_neg]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            ((re_le_norm _).trans hβ) hz)
        · rw [norm_cexp_mul_ofReal', neg_re, neg_neg]
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
            ((neg_le_abs _).trans ((abs_re_le_norm _).trans ha)) hδ)
      _ = D * Real.exp (-(θ - κ) * p.2) := by
        rw [← Real.exp_add]
        rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ D * (Real.exp (-e * p.1) * Real.exp (-e * p.2)) := by
        rw [← Real.exp_add]
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) hD
        dsimp [e]
        nlinarith [hp.2]
  · simp only [rewardTriangle, if_neg hp, norm_zero]
    exact mul_nonneg hD (mul_nonneg (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _)
      (indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _))

theorem rewardMoment_eq_triangle (g : ℝ → ℂ) (a β : ℂ) :
    rewardMoment β (rewardSource g a) =
      ∫ z : ℝ, ∫ h : ℝ, rewardTriangle g a β (z, h) := by
  rw [rewardMoment, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : 0 < z
  · rw [indicator_of_mem (show z ∈ Ioi (0 : ℝ) from hz), rewardSource, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [rewardTriangle, hz, true_and]
    split_ifs <;> simp [mul_assoc]
  · rw [indicator_of_notMem (show z ∉ Ioi (0 : ℝ) from hz)]
    simp only [rewardTriangle, hz, false_and, if_false, integral_zero]

theorem rewardMoment_triangle_swap (hg : IsExpDensity g D θ)
    (ha : ‖a‖ ≤ κ) (hβ : ‖β‖ ≤ κ) (hκ : κ < θ) :
    rewardMoment β (rewardSource g a) =
      ∫ h : ℝ, ∫ z : ℝ, rewardTriangle g a β (z, h) := by
  rw [rewardMoment_eq_triangle]
  exact integral_integral_swap (integrable_rewardTriangle hg ha hβ hκ)

end PGM.WienerHopf
