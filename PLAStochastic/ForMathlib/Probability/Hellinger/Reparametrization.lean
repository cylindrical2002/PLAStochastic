import PLAStochastic.ForMathlib.Probability.Hellinger.RadonNikodym
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Exact probability densities under an increasing C1 reparametrization

The Jacobian and the actual pushed-forward measure are proved together. The
input order isomorphism is globally defined, so there is no missing boundary
mass or unproved normalization assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def pullbackOrderIso (p : HellingerDensity (volume : Measure ℝ)) (e : ℝ ≃o ℝ)
    (d : ℝ → ℝ) (hd : ∀ x, HasDerivAt e (d x) x)
    (hdm : Measurable d) (hdpos : ∀ x, 0 < d x) : HellingerDensity (volume : Measure ℝ) where
  density x := d x * p.density (e x)
  measurable := hdm.mul (p.measurable.comp e.continuous.measurable)
  nonneg x := mul_nonneg (hdpos x).le (p.nonneg _)
  integrable := by
    have h := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hd x).hasDerivWithinAt) e.injective.injOn p.density
    simp only [image_univ, e.surjective.range_eq, integrableOn_univ,
      abs_of_pos (hdpos _), smul_eq_mul] at h
    exact h.mp p.integrable
  integral_eq_one := by
    have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (hd x).hasDerivWithinAt) e.injective.injOn p.density
    simp only [image_univ, e.surjective.range_eq, Measure.restrict_univ,
      abs_of_pos (hdpos _), smul_eq_mul] at h
    exact h.symm.trans p.integral_eq_one

theorem pullbackOrderIso_toMeasure (p : HellingerDensity (volume : Measure ℝ))
    (e : ℝ ≃o ℝ) (d : ℝ → ℝ) (hd : ∀ x, HasDerivAt e (d x) x)
    (hdm : Measurable d) (hdpos : ∀ x, 0 < d x) :
    (p.pullbackOrderIso e d hd hdm hdpos).toMeasure = p.toMeasure.map e.symm := by
  symm
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hcomp : Measurable (fun x : ℝ => φ (e.symm x)) := hφ.comp e.symm.continuous.measurable
  rw [lintegral_map hφ e.symm.continuous.measurable, toMeasure, toMeasure,
    lintegral_withDensity_eq_lintegral_mul _ p.measurable.ennreal_ofReal hcomp,
    lintegral_withDensity_eq_lintegral_mul _
      (p.pullbackOrderIso e d hd hdm hdpos).measurable.ennreal_ofReal hφ]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) e.injective.injOn
    (fun x => ENNReal.ofReal (p.density x) * φ (e.symm x))
  simp only [image_univ, e.surjective.range_eq, Measure.restrict_univ,
    abs_of_pos (hdpos _), OrderIso.symm_apply_apply] at h
  dsimp only [Pi.mul_apply]
  rw [h]
  apply lintegral_congr
  intro x
  change ENNReal.ofReal (d x) * (ENNReal.ofReal (p.density (e x)) * φ x) =
    ENNReal.ofReal (d x * p.density (e x)) * φ x
  rw [ENNReal.ofReal_mul (hdpos x).le, mul_assoc]

end

end ProbabilityTheory.HellingerDensity
