import PLAStochastic.Index.KEP.ReferenceScale.ActualCertificateTransfer
import PLAStochastic.Index.KEP.ReferenceScale.BridgeKernelIdentification

/-!
# The exact Ward coefficients of the original certificate graph

The zero-order bridge term cancels in the first transferred scalar. In the
second bulk coefficient it survives only with cutoff derivatives. The original
second spatial kernel appears once, and all other differentiated terms are
explicit first pin fluxes. The physical numerator remains unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepCertificate_transferredScalar_ward {f f' κ κ' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') (hd : ∀ t, HasDerivAt f (f' t) t)
    {w d : ℝ} (hw : 0 ≤ w) (hd0 : d ≠ 0) (n : ℕ)
    (hddef : d = (n + 1 : ℕ) - w) (s : ℝ) :
    let p := kepLogStep f 1
    let p' := kepLogStepFirst f' 1
    let q := kepLogStepSlope f f' 1
    kepGraphTransferredScalar d (kepCertificateScalar p w d n κ)
      (kepCertificateScalarFirst p q w d n κ κ') s =
      Real.exp s * (κ' s * kepFixedBridge p w s n 0 w +
        κ s * d * kepFixedBridgeRight p p' w s n 0 w -
        κ s * kepBridgeTransportFlux p w 1 s n 0 w) := by
  dsimp only
  unfold kepGraphTransferredScalar kepCertificateScalar kepCertificateScalarFirst
  rw [kepFixedBridge_transport (continuous_kepLogStep hf 1)
    (continuous_kepLogStepFirst hf' 1) (hasDerivAt_kepLogStep_right hd 1)
    (kepLogStepSlope_eq (by norm_num : (1 : ℝ) ^ 2 = 1)) hw]
  simp only [mul_one, add_zero]
  rw [← hddef]
  field_simp [hd0]
  ring

theorem kepCertificate_bulkCoefficient_ward {f f' f'' κ κ' κ'' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f') (hd : ∀ t, HasDerivAt f (f' t) t)
    {w d : ℝ} (hw : 0 ≤ w) (hd0 : d ≠ 0) (n : ℕ)
    (hddef : d = (n + 1 : ℕ) - w) (s : ℝ) :
    let p := kepLogStep f 1
    let p' := kepLogStepFirst f' 1
    let p'' := kepLogStepSecond f'' 1
    let q := kepLogStepSlope f f' 1
    let R := kepCertificateScalar p w d n κ
    let R' := kepCertificateScalarFirst p q w d n κ κ'
    let R'' := kepCertificateScalarSecond p p' p'' q w d n κ κ' κ''
    Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / d ^ 2 =
      Real.exp (2 * s) / d *
        ((κ' s + κ'' s) * kepFixedBridge p w s n 0 w +
          2 * κ' s * d * kepFixedBridgeRight p p' w s n 0 w +
          κ s * d ^ 2 * kepFixedBridgeRight p p'' w s n 0 w -
          2 * (κ s + κ' s) * kepBridgeTransportFlux p w 1 s n 0 w -
          κ s * d * kepBridgeFluxRight p p' w 1 s n 0 w -
          κ s * kepBridgeFluxSlope p q w 1 s n 0 w) := by
  dsimp only
  unfold kepCertificateScalar kepCertificateScalarFirst kepCertificateScalarSecond
    kepFixedBridgeSlopeSecondWard
  rw [kepFixedBridge_transport (continuous_kepLogStep hf 1)
    (continuous_kepLogStepFirst hf' 1) (hasDerivAt_kepLogStep_right hd 1)
    (kepLogStepSlope_eq (by norm_num : (1 : ℝ) ^ 2 = 1)) hw]
  simp only [mul_one, add_zero]
  rw [← hddef]
  field_simp [hd0]
  ring

/-- The positive numerator condition also holds for the actual core cutoff
with a gap of order epsilon. Its reciprocal is bounded independently of the
layer and of every exterior length. -/
theorem kepCertificate_core_numerator_bounds {eps : ℝ} (heps : 1 ≤ eps)
    {L : ℕ} (hL : 4 * (2 * eps) ≤ (L : ℝ)) :
    eps ≤ (L : ℝ) - 2 * eps ∧ 1 ≤ (L : ℝ) - 2 * eps ∧
      ((L : ℝ) - 2 * eps)⁻¹ ≤ 1 := by
  have h : 1 ≤ (L : ℝ) - 2 * eps := by linarith
  exact ⟨by linarith, h, inv_le_one_of_one_le₀ h⟩

end

end PGM
