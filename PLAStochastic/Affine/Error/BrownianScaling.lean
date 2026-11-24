import PLAStochastic.Affine.Error.Measurable

/-!
# Brownian scaling of the actual fitting errors

The normalized process is Brownian by Mathlib's finite-dimensional Brownian
scaling theorem. The countable observation representation in `MeasurableErrors`
identifies its error law with the original Brownian error law. Its pathwise
error is then related to the original process by the proved amplitude identity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The usual normalized Brownian time dilation. -/
def normalizedBrownian (B : ℝ≥0 → Ω → ℝ) (c : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => (Real.sqrt (c : ℝ))⁻¹ * B (c * t) ω

theorem isBrownianReal_normalized (hB : IsBrownianReal B μ) {c : ℝ≥0} (hc : c ≠ 0) :
    IsBrownianReal (normalizedBrownian B c) μ := hB.smul hc

/-- The normalized and original unit-interval paths agree after their actual
time dilation and amplitude multiplication, outside a single null set. -/
theorem unitPath_normalized_ae (hB : IsBrownianReal B μ) {c : ℝ≥0} (hc : c ≠ 0)
    (T : ℝ≥0) :
    (fun ω => unitPath (processPath (normalizedBrownian B c) ω) (T : ℝ)) =ᵐ[μ]
      (fun ω => (Real.sqrt (c : ℝ))⁻¹ • unitPath (processPath B ω) ((c * T : ℝ≥0) : ℝ)) := by
  filter_upwards [hB.cont, (isBrownianReal_normalized hB hc).cont] with ω hω hCω
  ext u
  change unitPath (processPath (normalizedBrownian B c) ω) (T : ℝ) u =
    (Real.sqrt (c : ℝ))⁻¹ * unitPath (processPath B ω) ((c * T : ℝ≥0) : ℝ) u
  rw [unitPath_processPath_apply hCω, unitPath_processPath_apply hω]
  exact congrArg (fun t : ℝ≥0 => (Real.sqrt (c : ℝ))⁻¹ * B t ω)
    (mul_assoc c T (⟨u.1, u.property.1⟩ : ℝ≥0)).symm

theorem anchoredProcessError_normalized_ae (hB : IsBrownianReal B μ)
    {c : ℝ≥0} (hc : c ≠ 0) (T : ℝ≥0) :
    anchoredProcessError (normalizedBrownian B c) T =ᵐ[μ]
      (fun ω => (Real.sqrt (c : ℝ))⁻¹ * anchoredProcessError B (c * T) ω) := by
  filter_upwards [unitPath_normalized_ae hB hc T] with ω hω
  change anchoredError (unitPath (processPath (normalizedBrownian B c) ω) (T : ℝ)) = _
  rw [hω, anchoredError_smul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (c : ℝ)))]
  rfl

theorem optimalProcessError_normalized_ae (hB : IsBrownianReal B μ)
    {c : ℝ≥0} (hc : c ≠ 0) (T : ℝ≥0) :
    optimalProcessError (normalizedBrownian B c) T =ᵐ[μ]
      (fun ω => (Real.sqrt (c : ℝ))⁻¹ * optimalProcessError B (c * T) ω) := by
  filter_upwards [unitPath_normalized_ae hB hc T] with ω hω
  change optimalError (unitPath (processPath (normalizedBrownian B c) ω) (T : ℝ)) = _
  rw [hω, optimalError_smul,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (c : ℝ)))]
  rfl

/-- Brownian scaling for the actual anchored fitting error, for every positive
dilation and every nonnegative observation duration. -/
theorem identDistrib_anchoredProcessError_scaling (hB : IsBrownianReal B μ)
    {c : ℝ≥0} (hc : c ≠ 0) (T : ℝ≥0) :
    IdentDistrib (anchoredProcessError B (c * T))
      (fun ω => Real.sqrt (c : ℝ) * anchoredProcessError B T ω) μ μ := by
  have hs := (identDistrib_anchoredProcessError (isBrownianReal_normalized hB hc) hB T).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.sqrt (c : ℝ) * x))
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast (pos_of_ne_zero hc)
  have hroot : Real.sqrt (c : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcpos)
  have hae : (fun ω => Real.sqrt (c : ℝ) * anchoredProcessError (normalizedBrownian B c) T ω) =ᵐ[μ]
      anchoredProcessError B (c * T) := by
    filter_upwards [anchoredProcessError_normalized_ae hB hc T] with ω hω
    rw [hω, ← mul_assoc, mul_inv_cancel₀ hroot, one_mul]
  exact (IdentDistrib.of_ae_eq hs.aemeasurable_fst hae).symm.trans hs

/-- Brownian scaling for the actual unrestricted affine fitting error. -/
theorem identDistrib_optimalProcessError_scaling (hB : IsBrownianReal B μ)
    {c : ℝ≥0} (hc : c ≠ 0) (T : ℝ≥0) :
    IdentDistrib (optimalProcessError B (c * T))
      (fun ω => Real.sqrt (c : ℝ) * optimalProcessError B T ω) μ μ := by
  have hs := (identDistrib_optimalProcessError (isBrownianReal_normalized hB hc) hB T).comp
    (by fun_prop : Measurable (fun x : ℝ => Real.sqrt (c : ℝ) * x))
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast (pos_of_ne_zero hc)
  have hroot : Real.sqrt (c : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hcpos)
  have hae : (fun ω => Real.sqrt (c : ℝ) * optimalProcessError (normalizedBrownian B c) T ω) =ᵐ[μ]
      optimalProcessError B (c * T) := by
    filter_upwards [optimalProcessError_normalized_ae hB hc T] with ω hω
    rw [hω, ← mul_assoc, mul_inv_cancel₀ hroot, one_mul]
  exact (IdentDistrib.of_ae_eq hs.aemeasurable_fst hae).symm.trans hs

theorem identDistrib_anchoredProcessError_time (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IdentDistrib (anchoredProcessError B T)
      (fun ω => Real.sqrt (T : ℝ) * anchoredProcessError B 1 ω) μ μ := by
  simpa only [mul_one] using identDistrib_anchoredProcessError_scaling hB hT 1

theorem identDistrib_optimalProcessError_time (hB : IsBrownianReal B μ)
    {T : ℝ≥0} (hT : T ≠ 0) :
    IdentDistrib (optimalProcessError B T)
      (fun ω => Real.sqrt (T : ℝ) * optimalProcessError B 1 ω) μ μ := by
  simpa only [mul_one] using identDistrib_optimalProcessError_scaling hB hT 1

end BrownianAffine
