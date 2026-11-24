import PLAStochastic.Index.CEPS.Reward.Source
import Mathlib.Analysis.Calculus.MeanValue

/-! # The vanishing factor in the overshoot reward source -/

noncomputable section
open MeasureTheory Set Complex Metric Filter
namespace PGM.WienerHopf

theorem reward_exp_sub_exp_le {p q : ℂ} {A : ℝ} (hp : ‖p‖ ≤ A) (hq : ‖q‖ ≤ A) :
    ‖cexp p - cexp q‖ ≤ Real.exp A * ‖p - q‖ := by
  apply (convex_closedBall (0 : ℂ) A).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => Complex.differentiable_exp z) ?_
    (mem_closedBall_zero_iff.mpr hq) (mem_closedBall_zero_iff.mpr hp)
  intro z hz
  rw [Complex.deriv_exp, norm_exp]
  exact Real.exp_le_exp.mpr ((re_le_norm _).trans (mem_closedBall_zero_iff.mp hz))

theorem reward_exp_sub_root_le {a β : ℂ} {κ t : ℝ} (ha : ‖a‖ ≤ κ) (hβ : ‖β‖ ≤ κ)
    (ht : 0 ≤ t) :
    ‖cexp (-a * t) - cexp (β * t)‖ ≤ ‖a + β‖ * t * Real.exp (κ * t) := by
  have hn : ‖-a * (t : ℂ)‖ ≤ κ * t := by
    rw [norm_mul, norm_neg, norm_real, Real.norm_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right ha ht
  have hm : ‖β * (t : ℂ)‖ ≤ κ * t := by
    rw [norm_mul, norm_real, Real.norm_of_nonneg ht]
    exact mul_le_mul_of_nonneg_right hβ ht
  have he := reward_exp_sub_exp_le hn hm
  have hd : -a * (t : ℂ) - β * t = -(a + β) * t := by ring
  rw [hd, norm_mul, norm_neg, norm_real, Real.norm_of_nonneg ht] at he
  nlinarith only [he]

theorem reward_linear_le_exp {e : ℝ} (he : 0 < e) {t : ℝ} (_ht : 0 ≤ t) :
    t ≤ Real.exp (e * t) / e := by
  rw [le_div_iff₀ he]
  linarith [Real.add_one_le_exp (e * t)]

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem rewardSource_difference_integrand_le (hg : IsExpDensity g D θ)
    {a β : ℂ} {κ x h : ℝ} (ha : ‖a‖ ≤ κ) (hβ : ‖β‖ ≤ κ) (hκ : κ < θ) (hh : x < h) :
    ‖(cexp (-a * (h - x : ℝ)) - cexp (β * (h - x : ℝ))) * g h‖ ≤
      (‖a + β‖ * D / ((θ - κ) / 2) * Real.exp (-((θ + κ) / 2) * x)) *
        Real.exp (-((θ - κ) / 2) * h) := by
  let e := (θ - κ) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have ht : 0 ≤ h - x := by linarith
  have hD := hg.nonneg_D
  rw [norm_mul]
  calc
    _ ≤ (‖a + β‖ * (h - x) * Real.exp (κ * (h - x))) * (D * Real.exp (-θ * h)) :=
      mul_le_mul (reward_exp_sub_root_le ha hβ ht) (hg.norm_le h) (norm_nonneg _) (by positivity)
    _ ≤ (‖a + β‖ * (Real.exp (e * (h - x)) / e) * Real.exp (κ * (h - x))) *
        (D * Real.exp (-θ * h)) := by
      gcongr
      exact reward_linear_le_exp he ht
    _ = _ := by
      have hex : Real.exp (e * (h - x)) * Real.exp (κ * (h - x)) * Real.exp (-θ * h) =
          Real.exp (-((θ + κ) / 2) * x) * Real.exp (-e * h) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        dsimp [e]
        ring
      calc
        _ = (‖a + β‖ * D / e) *
            (Real.exp (e * (h - x)) * Real.exp (κ * (h - x)) * Real.exp (-θ * h)) := by ring
        _ = _ := by rw [hex]; dsimp [e]; ring

/-- The source difference vanishes linearly in `a+β`, with a class-uniform tail budget. -/
theorem norm_rewardSource_sub_root_le (hg : IsExpDensity g D θ)
    {a β : ℂ} {κ : ℝ} (ha : ‖a‖ ≤ κ) (hβ : ‖β‖ ≤ κ) (hκ : κ < θ) (x : ℝ) :
    ‖rewardSource g a x - rewardSource g (-β) x‖ ≤
      4 * D / (θ - κ) ^ 2 * ‖a + β‖ * Real.exp (-θ * x) := by
  let e := (θ - κ) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hi₁ := integrableOn_rewardSource_integrand hg ha hκ x
  have hi₂ := integrableOn_rewardSource_integrand hg (a := -β) (by simpa using hβ) hκ x
  have hd : IntegrableOn (fun h : ℝ =>
      (cexp (-a * (h - x : ℝ)) - cexp (β * (h - x : ℝ))) * g h) (Ioi x) := by
    refine (hi₁.sub hi₂).congr_fun ?_ measurableSet_Ioi
    intro h _
    simp only [Pi.sub_apply, neg_neg]
    ring
  have hB : IntegrableOn (fun h : ℝ =>
      (‖a + β‖ * D / e * Real.exp (-((θ + κ) / 2) * x)) * Real.exp (-e * h)) (Ioi x) :=
    (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  rw [rewardSource_eq_setIntegral, rewardSource_eq_setIntegral, ← integral_sub hi₁ hi₂]
  have hdiff : (∫ h in Ioi x, cexp (-a * (h - x : ℝ)) * g h -
      cexp (- -β * (h - x : ℝ)) * g h) =
      ∫ h in Ioi x, (cexp (-a * (h - x : ℝ)) - cexp (β * (h - x : ℝ))) * g h := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h _
    dsimp only
    rw [neg_neg]
    ring
  rw [hdiff]
  calc
    _ ≤ ∫ h in Ioi x, ‖(cexp (-a * (h - x : ℝ)) - cexp (β * (h - x : ℝ))) * g h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi x, (‖a + β‖ * D / e * Real.exp (-((θ + κ) / 2) * x)) * Real.exp (-e * h) := by
      apply integral_mono_ae hd.norm hB
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun h hh =>
        rewardSource_difference_integrand_le hg ha hβ hκ hh)
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x, div_neg]
      have hex : Real.exp (-((θ + κ) / 2) * x) * Real.exp (-e * x) = Real.exp (-θ * x) := by
        rw [← Real.exp_add]
        congr 1
        dsimp [e]
        ring
      calc
        _ = (‖a + β‖ * D / e ^ 2) *
            (Real.exp (-((θ + κ) / 2) * x) * Real.exp (-e * x)) := by field_simp
        _ = _ := by
          rw [hex]
          have hn : θ - κ ≠ 0 := by linarith
          dsimp [e]
          field_simp
          ring

end PGM.WienerHopf
