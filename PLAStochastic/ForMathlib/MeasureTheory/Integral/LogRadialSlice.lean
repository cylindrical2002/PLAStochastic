import PLAStochastic.ForMathlib.MeasureTheory.Integral.RadialSlice
import PLAStochastic.ForMathlib.Probability.Hellinger.LogCoordinates

/-!
# Logarithmic radial slicing with the full Jacobian

The last positive coordinate is `exp s`. Lebesgue integration on the positive
half-space becomes integration over direction and log radius, with Jacobian
`exp ((k+1)s)`. The formula keeps the original finite-dimensional integral and
requires no regularity of angular sets.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set
open scoped ENNReal

theorem integral_radialMeasure_eq_log {k : ℕ} (G : ℝ → ℝ) :
    (∫ r, G r ∂radialMeasure k) =
      ∫ s, Real.exp (((k + 1 : ℕ) : ℝ) * s) * G (Real.exp s) := by
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (s ^ k)) := by fun_prop
  rw [radialMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hpos : (∫ r in Ioi (0 : ℝ), (ENNReal.ofReal (r ^ k)).toReal • G r) =
      ∫ r in Ioi (0 : ℝ), r ^ k * G r := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simp only [ENNReal.toReal_ofReal (pow_nonneg hr.le k), smul_eq_mul]
  rw [hpos, ← ProbabilityTheory.HellingerDensity.integral_exp_mul_comp_exp]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    dsimp only
    rw [← mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring

theorem integral_eq_log_radial {k : ℕ} {G : (Fin (k + 1) → ℝ) → ℝ}
    (hG : Integrable G) (hzero : ∀ x, x (Fin.last k) ≤ 0 → G x = 0) :
    (∫ x, G x) = ∫ u : Fin k → ℝ, ∫ s,
      Real.exp (((k + 1 : ℕ) : ℝ) * s) *
        G (Real.exp s • (Fin.snoc u 1 : Fin (k + 1) → ℝ)) := by
  rw [integral_eq_radial hG hzero]
  apply integral_congr_ae
  exact ae_of_all _ fun u => integral_radialMeasure_eq_log _

end

end PGM
