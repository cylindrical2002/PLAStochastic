import PLAStochastic.Index.CEPS.Reward.Solution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The overshoot reward source and its exponential envelope -/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

/-- Tail reward from the first positive ladder height. -/
def rewardSource (g : ℝ → ℂ) (a : ℂ) (x : ℝ) : ℂ :=
  ∫ h : ℝ, if x < h then cexp (-a * (h - x : ℝ)) * g h else 0

theorem rewardSource_eq_setIntegral (g : ℝ → ℂ) (a : ℂ) (x : ℝ) :
    rewardSource g a x = ∫ h in Ioi x, cexp (-a * (h - x : ℝ)) * g h := by
  change (∫ h, (Ioi x).indicator (fun h => cexp (-a * (h - x : ℝ)) * g h) h) = _
  exact integral_indicator measurableSet_Ioi

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem measurable_rewardSource (hg : IsExpDensity g D θ) (a : ℂ) :
    Measurable (rewardSource g a) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      if p.1 < p.2 then cexp (-a * (p.2 - p.1 : ℝ)) * g p.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      ((by fun_prop : Measurable (fun p : ℝ × ℝ => cexp (-a * (p.2 - p.1 : ℝ)))).mul
        (hg.measurable.comp measurable_snd)) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem rewardSource_integrand_le (hg : IsExpDensity g D θ) {a : ℂ} {a₀ x h : ℝ}
    (ha : ‖a‖ ≤ a₀) (hh : x < h) :
    ‖cexp (-a * (h - x : ℝ)) * g h‖ ≤
      D * Real.exp (-a₀ * x) * Real.exp ((a₀ - θ) * h) := by
  have hre : -a.re ≤ a₀ := (neg_le_abs _).trans ((abs_re_le_norm _).trans ha)
  rw [norm_mul, norm_cexp_mul_ofReal', neg_re, neg_neg]
  calc
    _ ≤ Real.exp (a₀ * (h - x)) * (D * Real.exp (-θ * h)) :=
      mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre (by linarith)))
        (hg.norm_le h) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_comm (Real.exp _), mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem integrableOn_rewardSource_integrand (hg : IsExpDensity g D θ) {a : ℂ} {a₀ : ℝ}
    (ha : ‖a‖ ≤ a₀) (haθ : a₀ < θ) (x : ℝ) :
    IntegrableOn (fun h => cexp (-a * (h - x : ℝ)) * g h) (Ioi x) := by
  have hB : IntegrableOn (fun h : ℝ => D * Real.exp (-a₀ * x) * Real.exp ((a₀ - θ) * h))
      (Ioi x) := (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  refine hB.mono' (((by fun_prop : Measurable (fun h : ℝ => cexp (-a * (h - x : ℝ)))).mul
    hg.measurable).aestronglyMeasurable) ?_
  exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun h hh =>
    rewardSource_integrand_le hg ha hh)

theorem norm_rewardSource_le (hg : IsExpDensity g D θ) {a : ℂ} {a₀ : ℝ}
    (ha : ‖a‖ ≤ a₀) (haθ : a₀ < θ) (x : ℝ) :
    ‖rewardSource g a x‖ ≤ D / (θ - a₀) * Real.exp (-θ * x) := by
  have hB : IntegrableOn (fun h : ℝ => D * Real.exp (-a₀ * x) * Real.exp ((a₀ - θ) * h))
      (Ioi x) := (integrableOn_exp_mul_Ioi (by linarith) x).const_mul _
  rw [rewardSource_eq_setIntegral]
  calc
    _ ≤ ∫ h in Ioi x, ‖cexp (-a * (h - x : ℝ)) * g h‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi x, D * Real.exp (-a₀ * x) * Real.exp ((a₀ - θ) * h) :=
      integral_mono_ae (integrableOn_rewardSource_integrand hg ha haθ x).norm hB
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun h hh =>
          rewardSource_integrand_le hg ha hh))
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) x]
      have he : Real.exp (-a₀ * x) * Real.exp ((a₀ - θ) * x) = Real.exp (-θ * x) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = -(D * (Real.exp (-a₀ * x) * Real.exp ((a₀ - θ) * x))) / (a₀ - θ) := by ring
        _ = -(D * Real.exp (-θ * x)) / (a₀ - θ) := by rw [he]
        _ = _ := by rw [show a₀ - θ = -(θ - a₀) by ring, div_neg]; ring

theorem halfBdd_rewardSource (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) {a : ℂ} {a₀ : ℝ}
    (ha : ‖a‖ ≤ a₀) (haθ : a₀ < θ) : HalfBdd (halfLine (rewardSource g a)) := by
  refine halfBdd_halfLine (measurable_rewardSource hg a) (fun X => ?_)
  refine ⟨D / (θ - a₀), by have := hg.nonneg_D; positivity, fun x hx _ => ?_⟩
  exact (norm_rewardSource_le hg ha haθ x).trans (mul_le_of_le_one_right
    (by have := hg.nonneg_D; positivity) (Real.exp_le_one_iff.mpr (by nlinarith)))

end PGM.WienerHopf
