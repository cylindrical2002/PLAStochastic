import PLAStochastic.Index.CEPS.Reward.Primitive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The spatial derivative of the exponential renewal reward

Continuity of the renewal density at the evaluation point is retained
explicitly. The primitive formula needs only exponential measurability.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

theorem HalfBdd.intervalIntegrable_exp_mul {u : ℝ → ℂ} (hu : HalfBdd u) (a : ℂ)
    {x : ℝ} (hx : 0 ≤ x) :
    IntervalIntegrable (fun z : ℝ => cexp (-a * z) * u z) volume 0 x := by
  have hE : HalfBdd (halfLine (fun y : ℝ => cexp (a * y))) := by
    simpa only [neg_neg] using halfBdd_exponential (-a)
  have hc : IntegrableOn (fun z : ℝ => cexp (-a * x) *
      (u z * halfLine (fun y : ℝ => cexp (a * y)) (x - z))) (Ioc 0 x) :=
    ((hu.integrable_convC_integrand hE x).const_mul _).integrableOn
  have hi : IntegrableOn (fun z : ℝ => cexp (-a * z) * u z) (Ioc 0 x) := by
    apply hc.congr_fun _ measurableSet_Ioc
    intro z hz
    dsimp only
    rw [halfLine_of_nonneg _ (by linarith [hz.2])]
    have he : cexp (-a * x) * cexp (a * (x - z : ℝ)) = cexp (-a * z) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    calc
      _ = (cexp (-a * x) * cexp (a * (x - z : ℝ))) * u z := by ring
      _ = _ := by rw [he]
  exact ⟨hi, by rw [Ioc_eq_empty_of_le hx]; exact integrableOn_empty⟩

variable {g : ℝ → ℂ} {D θ : ℝ}

/-- Classical spatial differentiability, with its local continuity premise visible. -/
theorem hasDerivAt_rewardSolution (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ)
    {a : ℂ} (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 < x)
    (hux : ContinuousAt (renewalDensity g) x) :
    HasDerivAt (rewardSolution g (rewardSource g a))
      (a * rewardSolution g (rewardSource g a) x - (1 - laplaceC g (-a)) * renewalDensity g x) x := by
  let A := laplaceC g (-a)
  let P : ℝ → ℂ := fun y => ∫ z in (0 : ℝ)..y, cexp (-a * z) * renewalDensity g z
  have hu := halfBdd_renewalDensity hg hθ
  have hmeas : Measurable (fun z : ℝ => cexp (-a * z) * renewalDensity g z) :=
    (by fun_prop : Measurable (fun z : ℝ => cexp (-a * z))).mul hu.measurable
  have hcont : ContinuousAt (fun z : ℝ => cexp (-a * z) * renewalDensity g z) x :=
    (by fun_prop : Continuous (fun z : ℝ => cexp (-a * z))).continuousAt.mul hux
  have hP : HasDerivAt P (cexp (-a * x) * renewalDensity g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable_exp_mul a hx.le)
      hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter hcont
  have hE : HasDerivAt (fun y : ℝ => cexp (a * y)) (a * cexp (a * x)) x := by
    have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
      simpa only [mul_one] using! ((hasDerivAt_id (x : ℂ)).const_mul a).comp_ofReal
    simpa only [mul_comm] using! (Complex.hasDerivAt_exp (a * x)).comp x hlin
  have hf := hE.mul ((hP.const_mul (A - 1)).const_add A)
  have he : cexp (a * x) * cexp (-a * x) = 1 := by
    rw [← exp_add]
    simp
  have hd : (a * cexp (a * x)) * (A + (A - 1) * P x) +
      cexp (a * x) * ((A - 1) * (cexp (-a * x) * renewalDensity g x)) =
      a * rewardSolution g (rewardSource g a) x - (1 - A) * renewalDensity g x := by
    rw [rewardSolution_primitive hg hθ ha hx.le]
    change _ = a * (cexp (a * x) * (A + (A - 1) * P x)) - (1 - A) * renewalDensity g x
    linear_combination (A - 1) * renewalDensity g x * he
  rw [hd] at hf
  apply hf.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
  exact rewardSolution_primitive hg hθ ha hy.le

end PGM.WienerHopf
