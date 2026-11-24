import PLAStochastic.ForMathlib.Probability.Hellinger.Density
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Relative entropy dominates square Hellinger distance

The comparison is expressed directly on densities. The second density is
strictly positive, and the relative-entropy integrand is genuinely integrable.
Thus real-valued integrals cannot hide an infinite entropy as zero.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

theorem sqrt_sub_sq_le_entropy_integrand {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a * Real.log (a / b) + b - a := by
  rcases eq_or_lt_of_le ha with hzero | hapos
  · rw [← hzero]
    simp [Real.sq_sqrt hb.le]
  · have hsapos : 0 < Real.sqrt a := Real.sqrt_pos.mpr hapos
    have hsbpos : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
    have hl := Real.log_le_sub_one_of_pos (div_pos hsbpos hsapos)
    rw [Real.log_div hsbpos.ne' hsapos.ne', Real.log_sqrt hb.le,
      Real.log_sqrt ha] at hl
    have hm := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2 * a by positivity)
    have hmul : a * (Real.sqrt b / Real.sqrt a) = Real.sqrt a * Real.sqrt b := by
      calc
        a * (Real.sqrt b / Real.sqrt a) = (a / Real.sqrt a) * Real.sqrt b := by ring
        _ = _ := by rw [Real.div_sqrt]
    have hm' : a * (Real.log b - Real.log a) ≤
        2 * (Real.sqrt a * Real.sqrt b) - 2 * a := by
      calc
        a * (Real.log b - Real.log a) =
            (2 * a) * (Real.log b / 2 - Real.log a / 2) := by ring
        _ ≤ (2 * a) * (Real.sqrt b / Real.sqrt a - 1) := hm
        _ = 2 * (Real.sqrt a * Real.sqrt b) - 2 * a := by
          rw [mul_sub, show (2 * a) * (Real.sqrt b / Real.sqrt a) =
            2 * (a * (Real.sqrt b / Real.sqrt a)) by ring, hmul]
          ring
    rw [Real.log_div hapos.ne' hb.ne']
    have hsqa := Real.sq_sqrt ha
    have hsqb := Real.sq_sqrt hb.le
    nlinarith only [hm', hsqa, hsqb]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Relative entropy in the integrable case bounds the squared Hellinger distance. -/
theorem hellinger_sq_le_entropy (p q : HellingerDensity μ)
    (hq : ∀ x, 0 < q.density x)
    (hInt : Integrable (fun x => p.density x * Real.log (p.density x / q.density x)) μ) :
    p.hellinger q ^ 2 ≤ ∫ x, p.density x * Real.log (p.density x / q.density x) ∂μ := by
  rw [hellinger_sq]
  have hle := integral_mono (p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq
    ((hInt.add q.integrable).sub p.integrable)
    (fun x => sqrt_sub_sq_le_entropy_integrand (p.nonneg x) (hq x))
  simp only [Pi.add_apply, Pi.sub_apply] at hle
  have hsub := integral_sub (hInt.add q.integrable) p.integrable
  have hadd := integral_add hInt q.integrable
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, p.integral_eq_one, q.integral_eq_one] at hle
  linarith only [hle]

end

end ProbabilityTheory.HellingerDensity
