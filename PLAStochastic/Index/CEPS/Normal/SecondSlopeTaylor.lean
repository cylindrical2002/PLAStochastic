import PLAStochastic.Index.CEPS.Normal.FunctionalSlopeLiftLocal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Exact removable second divided difference and its collision value -/

noncomputable section
open Complex Set Metric Filter Topology MeasureTheory
namespace PGM

theorem second_dslope_taylor_identity (f : ℂ → ℂ) (a x : ℂ) :
    f (a + x) = f a + deriv f a * x + x ^ 2 * dslope (dslope f a) a (a + x) := by
  by_cases hx : x = 0
  · simp [hx]
  · have hax : a + x ≠ a := fun h => hx (add_eq_left.mp h)
    rw [dslope_of_ne _ hax, slope_def_field, dslope_of_ne _ hax, slope_def_field, dslope_same]
    field_simp
    ring

theorem second_dslope_zero_eq_half_deriv {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    dslope (dslope f 0) 0 0 = deriv (deriv f) 0 / 2 := by
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hf.eventually_analyticAt
  have hd : DifferentiableOn ℂ f (ball 0 r) :=
    fun z hz => (hb hz).differentiableAt.differentiableWithinAt
  have hz : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have hi : (∫ s in (0 : ℝ)..1, (s : ℂ)) = (1 : ℂ) / 2 := by
    rw [intervalIntegral.integral_ofReal, integral_id]
    norm_num
  rw [second_dslope_eq_integral_of_differentiableOn_ball hd hz hz hz]
  simp only [sub_self, mul_zero, zero_add]
  simp_rw [intervalIntegral.integral_mul_const, hi]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  ring

end PGM
