import PLAStochastic.Index.KEP.ReferenceScale.ActualScaleFamily

/-!
# Actual reference scale regularity from the weighted second norm

All density, classical derivative, weighted integrability, and logarithmic
change-of-variable inputs are discharged on the actual reference orbit. Only
the value of its actual weighted second norm remains in the bound. A uniform
polynomial estimate for that norm will therefore discharge the scale condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_actual_scale_bound_from_second_norm :
    ∃ theta K eps0 : ℝ, 0 < theta ∧ 0 < K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ j, 1 ≤ j → ∀ s : ℝ,
        let P : Measure ℝ := (kepReferenceLaw eps j : Measure ℝ)
        let : IsProbabilityMeasure (P.map (fun x => Real.exp s * x)) :=
          Measure.isProbabilityMeasure_map (measurable_const.mul measurable_id).aemeasurable
        measureHellinger (P.map (fun x => Real.exp s * x)) P ≤
          K * Real.sqrt (1 + kepReferenceWeightedSecondNorm theta eps j) *
            |s| ^ (2 / 3 : ℝ) := by
  obtain ⟨theta, eps0, ht, he0, hfamily⟩ := kepReference_actual_scale_bound_for_small_weights
  obtain ⟨K, hK, hbound⟩ := hfamily theta ht le_rfl
  exact ⟨theta, K, eps0, ht, hK, he0, hbound⟩

end

end PGM
