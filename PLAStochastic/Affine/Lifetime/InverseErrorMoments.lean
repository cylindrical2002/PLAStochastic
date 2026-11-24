import PLAStochastic.Affine.Lifetime.ToleranceMoments
import PLAStochastic.Affine.Error.BridgeInvariance

/-!
# Actual lifetime moments as inverse fitting-error moments

The distributional identities transfer the already-proved integrability.
No evaluated model moment or density is used as a hypothesis.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem identDistrib_anchoredUnitLifetime_inverse_square (hB : IsBrownianReal B μ) :
    IdentDistrib (anchoredUnitLifetime B)
      (fun ω => anchoredProcessError B 1 ω ^ (-2 : ℝ)) μ μ := by
  have heq : (fun ω => (((ENNReal.ofReal (anchoredProcessError B 1 ω)) ^ 2)⁻¹).toReal) =
      (fun ω => anchoredProcessError B 1 ω ^ (-2 : ℝ)) := by
    funext ω
    have hd : 0 ≤ anchoredProcessError B 1 ω := anchoredTimeError_nonneg (processPath B ω) 1
    rw [Real.rpow_neg hd, Real.rpow_two, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hd]
  simpa only [Function.comp_def, anchoredUnitLifetime, heq] using!
    (identDistrib_anchoredLifetime_unit hB).comp ENNReal.measurable_toReal

theorem identDistrib_optimalUnitLifetime_inverse_square (hB : IsBrownianReal B μ) :
    IdentDistrib (optimalUnitLifetime B)
      (fun ω => optimalProcessError B 1 ω ^ (-2 : ℝ)) μ μ := by
  have heq : (fun ω => (((ENNReal.ofReal (optimalProcessError B 1 ω)) ^ 2)⁻¹).toReal) =
      (fun ω => optimalProcessError B 1 ω ^ (-2 : ℝ)) := by
    funext ω
    have hd : 0 ≤ optimalProcessError B 1 ω := optimalTimeError_nonneg (processPath B ω) 1
    rw [Real.rpow_neg hd, Real.rpow_two, ENNReal.toReal_inv, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hd]
  simpa only [Function.comp_def, optimalUnitLifetime, heq] using!
    (identDistrib_optimalLifetime_unit hB).comp ENNReal.measurable_toReal

theorem anchored_inverse_error_moment (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => anchoredProcessError B 1 ω ^ (-2 * q)) μ ∧
      (∫ ω, anchoredUnitLifetime B ω ^ q ∂μ) =
        ∫ ω, anchoredProcessError B 1 ω ^ (-2 * q) ∂μ := by
  have h := (identDistrib_anchoredUnitLifetime_inverse_square hB).comp (measurable_id.pow_const q)
  have h' : IdentDistrib (fun ω => anchoredUnitLifetime B ω ^ q)
      (fun ω => anchoredProcessError B 1 ω ^ (-2 * q)) μ μ := by
    have hm (ω : Ω) : anchoredProcessError B 1 ω ^ (-2 * q) =
        (anchoredProcessError B 1 ω ^ (-2 : ℝ)) ^ q :=
      Real.rpow_mul (show 0 ≤ anchoredProcessError B 1 ω from
        anchoredTimeError_nonneg (processPath B ω) 1) _ _
    simpa only [Function.comp_def, id_eq, ← hm] using h
  exact ⟨h'.integrable_snd (anchoredUnitLifetime_integrable_rpow hB hq), h'.integral_eq⟩

theorem optimal_inverse_error_moment (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) μ ∧
      (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) =
        ∫ ω, optimalProcessError B 1 ω ^ (-2 * q) ∂μ := by
  have h := (identDistrib_optimalUnitLifetime_inverse_square hB).comp (measurable_id.pow_const q)
  have h' : IdentDistrib (fun ω => optimalUnitLifetime B ω ^ q)
      (fun ω => optimalProcessError B 1 ω ^ (-2 * q)) μ μ := by
    have hm (ω : Ω) : optimalProcessError B 1 ω ^ (-2 * q) =
        (optimalProcessError B 1 ω ^ (-2 : ℝ)) ^ q :=
      Real.rpow_mul (show 0 ≤ optimalProcessError B 1 ω from
        optimalTimeError_nonneg (processPath B ω) 1) _ _
    simpa only [Function.comp_def, id_eq, ← hm] using h
  exact ⟨h'.integrable_snd (optimalUnitLifetime_integrable_rpow hB hq), h'.integral_eq⟩

/-- The first bridge-moment equality in the paper, before slope integration. -/
theorem optimal_inverse_bridge_error_moment (hB : IsBrownianReal B μ) {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun ω => optimalError (bridgeUnitPath B ω) ^ (-2 * q)) μ ∧
      (∫ ω, optimalUnitLifetime B ω ^ q ∂μ) =
        ∫ ω, optimalError (bridgeUnitPath B ω) ^ (-2 * q) ∂μ := by
  simpa only [optimalError_bridgeUnitPath] using optimal_inverse_error_moment hB hq

end BrownianAffine
