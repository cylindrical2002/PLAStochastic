import PLAStochastic.ForMathlib.Probability.Hellinger.DataProcessing
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-!
# Hellinger distance between actual probability measures

Radon-Nikodym densities relative to the sum of the two measures provide an
always finite common reference. Arbitrary measurable pushforwards contract this
distance. The contraction can also start from a density relative to an infinite
reference measure, including counting measure.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

namespace HellingerDensity

def ofProbability (P μ : Measure α) [IsProbabilityMeasure P] [SigmaFinite μ]
    (hP : P ≪ μ) : HellingerDensity μ where
  density x := (P.rnDeriv μ x).toReal
  measurable := (Measure.measurable_rnDeriv P μ).ennreal_toReal
  nonneg _ := ENNReal.toReal_nonneg
  integrable := by
    simpa only [IntegrableOn, Measure.restrict_univ] using
      (Measure.integrableOn_toReal_rnDeriv (μ := P) (ν := μ)
        (s := univ) (measure_ne_top P univ))
  integral_eq_one := by
    rw [Measure.integral_toReal_rnDeriv hP, probReal_univ]

theorem ofProbability_toMeasure (P μ : Measure α)
    [IsProbabilityMeasure P] [SigmaFinite μ] (hP : P ≪ μ) :
    (ofProbability P μ hP).toMeasure = P := by
  rw [toMeasure]
  calc
    μ.withDensity (fun x => ENNReal.ofReal ((P.rnDeriv μ x).toReal)) =
        μ.withDensity (P.rnDeriv μ) := by
      apply withDensity_congr_ae
      filter_upwards [Measure.rnDeriv_lt_top P μ] with x hx
      exact ENNReal.ofReal_toReal hx.ne
    _ = P := Measure.withDensity_rnDeriv_eq P μ hP

def leftDensity (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    HellingerDensity (P + Q) :=
  ofProbability P (P + Q) (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))

def rightDensity (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    HellingerDensity (P + Q) :=
  ofProbability Q (P + Q) (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))

@[simp] theorem leftDensity_toMeasure (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : (leftDensity P Q).toMeasure = P :=
  ofProbability_toMeasure _ _ _

@[simp] theorem rightDensity_toMeasure (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : (rightDensity P Q).toMeasure = Q :=
  ofProbability_toMeasure _ _ _

end HellingerDensity

def measureHellinger (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : ℝ :=
  (HellingerDensity.leftDensity P Q).hellinger (HellingerDensity.rightDensity P Q)

theorem measureHellinger_nonneg (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : 0 ≤ measureHellinger P Q :=
  HellingerDensity.hellinger_nonneg _ _

theorem measureHellinger_sq_le_two (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] : measureHellinger P Q ^ 2 ≤ 2 :=
  HellingerDensity.hellinger_sq_le_two _ _

theorem measureHellinger_map_le_density {μ : Measure α} (p q : HellingerDensity μ)
    {F : α → β} (hF : Measurable F) :
    let : IsProbabilityMeasure (p.toMeasure.map F) :=
      Measure.isProbabilityMeasure_map hF.aemeasurable
    let : IsProbabilityMeasure (q.toMeasure.map F) :=
      Measure.isProbabilityMeasure_map hF.aemeasurable
    measureHellinger (p.toMeasure.map F) (q.toMeasure.map F) ≤ p.hellinger q := by
  let : IsProbabilityMeasure (p.toMeasure.map F) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  let : IsProbabilityMeasure (q.toMeasure.map F) :=
    Measure.isProbabilityMeasure_map hF.aemeasurable
  apply HellingerDensity.hellinger_le_of_map p q
    (HellingerDensity.leftDensity _ _) (HellingerDensity.rightDensity _ _) hF
  · exact (HellingerDensity.leftDensity_toMeasure _ _).symm
  · exact (HellingerDensity.rightDensity_toMeasure _ _).symm

theorem measureHellinger_le_density {μ : Measure α} (p q : HellingerDensity μ) :
    measureHellinger p.toMeasure q.toMeasure ≤ p.hellinger q := by
  simpa only [Measure.map_id] using measureHellinger_map_le_density p q measurable_id

theorem measureHellinger_map (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {F : α → β} (hF : Measurable F) :
    let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    let : IsProbabilityMeasure (Q.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    measureHellinger (P.map F) (Q.map F) ≤ measureHellinger P Q := by
  let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let : IsProbabilityMeasure (Q.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  have h := measureHellinger_map_le_density
    (HellingerDensity.leftDensity P Q) (HellingerDensity.rightDensity P Q) hF
  simp only [HellingerDensity.leftDensity_toMeasure,
    HellingerDensity.rightDensity_toMeasure] at h
  exact h

end

end ProbabilityTheory
