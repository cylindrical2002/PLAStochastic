import PLAStochastic.Affine.Error.BridgeInvariance
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Actual Brownian and bridge random variables in the continuous path space

Countably many dense observations determine a continuous path. Their sampling
map is a measurable embedding of the Polish uniform-topology path space, which
proves measurability and full bridge-endpoint independence in that space.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianAffine

noncomputable section

instance pathMeasurableSpace (T : ℝ) : MeasurableSpace (Path T) := borel (Path T)
instance pathBorelSpace (T : ℝ) : BorelSpace (Path T) := ⟨rfl⟩

def pathObservations (f : Path 1) : ErrorSample → ℝ := fun s => f s.1

theorem continuous_pathObservations : Continuous pathObservations := by
  apply continuous_pi
  intro s
  exact continuous_eval_const s.1

theorem pathObservations_injective : Function.Injective pathObservations := by
  intro f g h
  apply DFunLike.ext'
  apply f.continuous.ext_on errorSampleSet_dense g.continuous
  intro t ht
  exact congrFun h ⟨t, ht⟩

theorem measurableEmbedding_pathObservations : MeasurableEmbedding pathObservations :=
  continuous_pathObservations.measurableEmbedding pathObservations_injective

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- Measurability in the uniform topology follows from the actual Brownian coordinates. -/
theorem aemeasurable_brownianUnitPath (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    AEMeasurable (fun ω => unitPath (processPath B ω) (T : ℝ)) μ := by
  apply measurableEmbedding_pathObservations.aemeasurable_comp_iff.mp
  apply (aemeasurable_sampledProcess hB.toIsPreBrownianReal T).congr
  filter_upwards [hB.cont] with ω hω
  funext s
  exact (unitPath_processPath_sample hω T s).symm

theorem aemeasurable_bridgeUnitPath (hB : IsBrownianReal B μ) :
    AEMeasurable (bridgeUnitPath B) μ :=
  (aemeasurable_brownianUnitPath hB 1).add
    ((hB.aemeasurable 1).neg.smul_const (timePath 1))

/-- Independence holds for the entire continuous bridge, with its uniform-topology Borel sets. -/
theorem bridgeUnitPath_indep_endpoint (hB : IsBrownianReal B μ) :
    IndepFun (bridgeUnitPath B) (B 1) μ := by
  have hs := (unitBrownianBridge_indep_endpoint hB.toIsPreBrownianReal).comp
    measurable_bridgeSample measurable_id
  have hsp : IndepFun (fun ω => pathObservations (bridgeUnitPath B ω)) (B 1) μ := by
    apply hs.congr _ Filter.EventuallyEq.rfl
    filter_upwards [hB.cont] with ω hω
    exact sampledBridge_eq_bridgeUnitPath hω
  obtain ⟨F, hF, hFeq⟩ := measurableEmbedding_pathObservations.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨(0 : Path 1)⟩)
  have h := hsp.comp hF measurable_id
  simpa only [Function.comp_def, id_eq, show ∀ f, F (pathObservations f) = f from
    fun f => congrFun hFeq f] using h

omit [MeasurableSpace Ω] in
/-- The pathwise Gaussian-endpoint decomposition in the same continuous path space. -/
theorem brownianUnitPath_eq_bridge_add_endpoint (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    unitPath (processPath B ω) 1 = bridgeUnitPath B ω + B 1 ω • timePath 1 := by
  unfold bridgeUnitPath
  simp only [neg_smul, neg_add_cancel_right]

end

end BrownianAffine
