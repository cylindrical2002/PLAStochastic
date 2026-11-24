import PLAStochastic.ForMathlib.Probability.Hellinger.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual probability measures on the natural numbers as Hellinger densities

Counting measure is the common reference measure. This makes the count-law
comparison independent of choices of dominating probability measures.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem lintegral_nat_probability_mass (P : Measure ℕ) [IsProbabilityMeasure P] :
    (∫⁻ k, ENNReal.ofReal (P.real {k}) ∂Measure.count) = 1 := by
  rw [lintegral_count]
  simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have he := measure_iUnion (μ := P) (f := fun k : ℕ => ({k} : Set ℕ))
    (fun i j hij => Set.disjoint_singleton.2 hij) (fun _ => measurableSet_singleton _)
  have hu : (⋃ k : ℕ, ({k} : Set ℕ)) = univ := by ext x; simp
  rw [hu, measure_univ] at he
  exact he.symm

def ofNatProbability (P : Measure ℕ) [IsProbabilityMeasure P] :
    HellingerDensity (Measure.count : Measure ℕ) where
  density k := P.real {k}
  measurable := Measurable.of_discrete
  nonneg _ := measureReal_nonneg
  integrable := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      Measurable.of_discrete.aestronglyMeasurable (ae_of_all _ fun _ => measureReal_nonneg)).1
    rw [lintegral_nat_probability_mass]
    norm_num
  integral_eq_one := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => measureReal_nonneg)
      Measurable.of_discrete.aestronglyMeasurable, lintegral_nat_probability_mass]
    norm_num

theorem ofNatProbability_toMeasure (P : Measure ℕ) [IsProbabilityMeasure P] :
    (ofNatProbability P).toMeasure = P := by
  apply Measure.ext_of_singleton
  intro k
  rw [toMeasure, withDensity_apply _ (measurableSet_singleton k),
    lintegral_singleton]
  simp [ofNatProbability, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top P {k})]

end

end ProbabilityTheory.HellingerDensity
