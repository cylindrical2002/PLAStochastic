import PLAStochastic.Index.CEPS.Scaled.EndpointLimits
import PLAStochastic.Index.CEPS.Scaled.UnmarkedDiscount

/-! # Identification of the filled endpoint with the physical primitive

The discount nonzero hypotheses are discharged on the actual unit discs.
These identifications are for positive physical scale away from zero mark;
the continuous limits and zero derivative are supplied by EndpointLimits.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMarkedDiscount_ne_zero_on_unit {t : ℂ} (ht : t ≠ 0)
    (hsmall : t ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) :
    cepsMarkedDiscount ρW t ≠ 0 := by
  have hl := ((cepsMarkedDiscountUnit_budget hW hθ hD).2.2.2 t hsmall).1
  have hu : cepsMarkedDiscountUnit ρW t ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hl)
  rw [cepsMarkedDiscountUnit_eq_div hW hθ hD ht] at hu
  exact (div_ne_zero_iff.mp hu).1

theorem cepsUnmarkedDiscount_ne_zero_on_unit {q : ℂ} (hq : q ≠ 0)
    (hsmall : q ∈ ball (0 : ℂ) cepsUnmarkedUnitRadius) :
    cepsUnmarkedDiscount q ≠ 0 := by
  have hl := (cepsUnmarkedDiscountUnit_budget.2.2.2 q hsmall).1
  have hu : cepsUnmarkedDiscountUnit q ≠ 0 := norm_pos_iff.mp
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hl)
  rw [cepsUnmarkedDiscountUnit_eq_div hq] at hu
  exact (div_ne_zero_iff.mp hu).1

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_eq_physical {b : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : z ≠ 0)
    (hsmall : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) (cepsMarkedUnitRadius D θ)) :
    cepsScaledMarkedEndpoint dom ρW b z =
      cepsMarkedDiscount ρW ((b : ℂ) ^ 2 * z) *
        cepsNormalHalfPrimitive (cepsCgf ρW)
          (fun (x : ℝ) q => cepsRootPlus D θ ρW x q)
          (fun (x : ℝ) q t => cepsD ρW x q t) (dom.canonL ρW)
          b (((b : ℂ) ^ 2 * z) * (1 + (b : ℂ))) ((b : ℂ) ^ 2 * z) (b : ℂ)⁻¹ := by
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have ht0 := mul_ne_zero (pow_ne_zero 2 hb0) hz
  have hd0 := cepsMarkedDiscount_ne_zero_on_unit hW hθ hD ht0 hsmall
  unfold cepsScaledMarkedEndpoint cepsScaledMarkedEndpointMean
  rw [Function.update_of_ne hz, cepsScaledMarkedDiscount_eq_div hW hθ hD z hb0]
  unfold CepsCanonDomain.halfMarkedPoleRemoved
  field_simp
  ring

theorem cepsScaledUnmarkedEndpointMean_eq_physical {b : ℝ} (hb : 0 < b)
    {z : ℂ} (hz : z ≠ 0)
    (hsmall : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) cepsUnmarkedUnitRadius) :
    cepsScaledUnmarkedEndpointMean dom ρW b z =
      (1 - cepsUnmarkedDiscount ((b : ℂ) ^ 2 * z) *
        cepsNormalHalfPrimitive (cepsCgf ρW)
          (fun (x : ℝ) q => cepsRootPlus D θ ρW x q)
          (fun (x : ℝ) q t => cepsD ρW x q t) (dom.canonL ρW)
          b ((b : ℂ) ^ 2 * z) 0 (b : ℂ)⁻¹) /
        cepsScaledUnmarkedDiscount z b := by
  have hb0 : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have hq0 := mul_ne_zero (pow_ne_zero 2 hb0) hz
  have hd0 := cepsUnmarkedDiscount_ne_zero_on_unit hq0 hsmall
  unfold cepsScaledUnmarkedEndpointMean
  rw [Function.update_of_ne hz, cepsScaledUnmarkedDiscount_eq_div z hb0]
  unfold CepsCanonDomain.halfZeroPoleRemoved cepsUnmarkedDiscount at *
  field_simp
  ring

end PGM
