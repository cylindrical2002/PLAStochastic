import PLAStochastic.ForMathlib.MeasureTheory.Integral.LogRadialSlice

/-!
# Almost-everywhere integrability on logarithmic radial slices

The full physical integrability passes through the actual radial measure and
the exponential change of variables. This supplies the genuine raywise
integration by parts hypotheses even when the test meets the physical origin.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem integrable_radialMeasure_log {k : ℕ} {G : ℝ → ℝ}
    (hG : Integrable G (radialMeasure k)) :
    Integrable (fun s => Real.exp (((k + 1 : ℕ) : ℝ) * s) * G (Real.exp s)) volume := by
  have hm : Measurable (fun r : ℝ => ENNReal.ofReal (r ^ k)) := by fun_prop
  have hi := (integrable_withDensity_iff_integrable_smul' hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hG
  have hi' : IntegrableOn (fun r => r ^ k * G r) (Ioi (0 : ℝ)) volume := by
    refine hi.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [ENNReal.toReal_ofReal (pow_nonneg hr.le k), smul_eq_mul]
  have hs := (ProbabilityTheory.HellingerDensity.integrable_exp_mul_comp_exp_iff _).mpr hi'
  convert hs using 1
  funext s
  rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem integrable_log_radial_sections {k : ℕ} {G : (Fin (k + 1) → ℝ) → ℝ}
    (hG : Integrable G volume) :
    ∀ᵐ u : Fin k → ℝ ∂volume, Integrable (fun s =>
      Real.exp (((k + 1 : ℕ) : ℝ) * s) *
        G (Real.exp s • (Fin.snoc u 1 : Fin (k + 1) → ℝ))) volume := by
  have hGr : Integrable G (((radialMeasure k).prod volume).map (radialMap k)) := by
    rw [map_radialMap]
    exact hG.restrict
  have hGc : Integrable (fun p => G (radialMap k p)) ((radialMeasure k).prod volume) :=
    (integrable_map_measure hGr.aestronglyMeasurable measurable_radialMap.aemeasurable).mp hGr
  filter_upwards [hGc.prod_left_ae] with u hu
  have hh := integrable_radialMeasure_log hu
  simpa only [radialMap_eq_smul] using hh

end

end PGM
