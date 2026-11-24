import PLAStochastic.Brownian.PathLaw.BridgeDecomposition
import PLAStochastic.Affine.Error.Measurable

/-!
# The fitting errors depend on the Brownian bridge alone

Removing the observed endpoint is a pathwise linear drift. The countable
observation formula then transfers independence from the entire bridge to each
actual fitting error. This supplies the endpoint independence used in the paper.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianAffine

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def bridgeUnitPath (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : Path 1 :=
  unitPath (processPath B ω) 1 + (-B 1 ω) • timePath 1

omit [MeasurableSpace Ω] in
theorem anchoredError_bridgeUnitPath (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    anchoredError (bridgeUnitPath B ω) = anchoredProcessError B 1 ω :=
  anchoredError_add_drift _ _

omit [MeasurableSpace Ω] in
theorem optimalError_bridgeUnitPath (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    optimalError (bridgeUnitPath B ω) = optimalProcessError B 1 ω := by
  simpa only [zero_smul, add_zero] using!
    optimalError_add_affine (unitPath (processPath B ω) 1) (-B 1 ω) 0

def errorSampleBridgeTime (s : ErrorSample) : BridgeTime :=
  ⟨errorSampleTime s, by constructor; positivity; exact s.1.property.2⟩

omit [MeasurableSpace Ω] in
theorem sampledBridge_eq_bridgeUnitPath {ω : Ω} (hω : Continuous (B · ω)) :
    (fun s => unitBrownianBridge B (errorSampleBridgeTime s) ω) =
      (fun s : ErrorSample => bridgeUnitPath B ω s.1) := by
  funext s
  change B (errorSampleTime s) ω - (s.1 : ℝ) * B 1 ω =
    unitPath (processPath B ω) 1 s.1 + (-B 1 ω) * (s.1 : ℝ)
  have hu : unitPath (processPath B ω) 1 s.1 = B (errorSampleTime s) ω := by
    change processPath B ω ((1 : ℝ) * (s.1 : ℝ)) = B (errorSampleTime s) ω
    rw [one_mul]
    exact processPath_apply_of_continuous hω (errorSampleTime s)
  rw [hu]
  ring

theorem measurable_bridgeSample :
    Measurable (fun g : BridgeTime → ℝ => fun s : ErrorSample => g (errorSampleBridgeTime s)) :=
  measurable_pi_lambda _ fun s => measurable_pi_apply (errorSampleBridgeTime s)

theorem sampledBridge_anchoredError_ae_eq (hB : IsBrownianReal B μ) :
    (fun ω => sampledAnchoredError (fun s => unitBrownianBridge B (errorSampleBridgeTime s) ω)) =ᵐ[μ]
      anchoredProcessError B 1 := by
  filter_upwards [hB.cont] with ω hω
  rw [sampledBridge_eq_bridgeUnitPath hω, sampledAnchoredError_eq,
    anchoredError_bridgeUnitPath]

theorem sampledBridge_optimalError_ae_eq (hB : IsBrownianReal B μ) :
    (fun ω => sampledOptimalError (fun s => unitBrownianBridge B (errorSampleBridgeTime s) ω)) =ᵐ[μ]
      optimalProcessError B 1 := by
  filter_upwards [hB.cont] with ω hω
  rw [sampledBridge_eq_bridgeUnitPath hω, sampledOptimalError_eq,
    optimalError_bridgeUnitPath]

theorem anchoredProcessError_indep_endpoint (hB : IsBrownianReal B μ) :
    IndepFun (anchoredProcessError B 1) (B 1) μ := by
  have h := (unitBrownianBridge_indep_endpoint hB.toIsPreBrownianReal).comp
    (measurable_sampledAnchoredError.comp measurable_bridgeSample) measurable_id
  exact h.congr (sampledBridge_anchoredError_ae_eq hB) Filter.EventuallyEq.rfl

theorem optimalProcessError_indep_endpoint (hB : IsBrownianReal B μ) :
    IndepFun (optimalProcessError B 1) (B 1) μ := by
  have h := (unitBrownianBridge_indep_endpoint hB.toIsPreBrownianReal).comp
    (measurable_sampledOptimalError.comp measurable_bridgeSample) measurable_id
  exact h.congr (sampledBridge_optimalError_ae_eq hB) Filter.EventuallyEq.rfl

end

end BrownianAffine
