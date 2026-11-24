import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Identification of a probability density from a continuously differentiable CDF -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

theorem eq_withDensity_of_contDiff_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hcdf : ∀ t : ℝ, cdf μ t = F t) :
    μ = volume.withDensity (fun x => ENNReal.ofReal (deriv F x)) := by
  have hmono : Monotone F := by
    intro x y hxy
    rw [← hcdf x, ← hcdf y]
    exact monotone_cdf μ hxy
  have hnonneg : ∀ x : ℝ, 0 ≤ deriv F x := fun _ => hmono.deriv_nonneg
  apply μ.ext_of_Ioc
  intro a b hab
  have hint : IntervalIntegrable (deriv F) volume a b :=
    hF.continuous_deriv_one.intervalIntegrable _ _
  have hint' : IntegrableOn (deriv F) (Ioc a b) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hint
  rw [← measure_cdf μ, StieltjesFunction.measure_Ioc, hcdf, hcdf, withDensity_apply _ measurableSet_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun x => hnonneg x)]
  congr 1
  rw [← intervalIntegral.integral_of_le hab.le]
  exact (intervalIntegral.integral_deriv_eq_sub (fun x _ => hF.differentiable_one x) hint).symm

end MeasureTheory.Measure
