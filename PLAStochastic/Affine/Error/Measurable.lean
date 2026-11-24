import PLAStochastic.Affine.Error.TimeProcess
import PLAStochastic.Brownian.Construction.CountableObservations
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.Topology.Order.IsLUB
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Instances.Rat

/-!
# Measurable representatives of the actual Brownian fitting errors

Uniform residuals of continuous paths are recovered on a fixed countable dense
subset of the unit interval. The fitting infimum is recovered on rational
coefficients. These countable formulas are measurable on the sampled function
space and agree with the pathwise errors almost surely for Brownian motion.
No measurability of a random variable valued in a continuous-path space is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace BrownianAffine

/-- One fixed countable dense set of observation times in the unit interval. -/
def errorSampleSet : Set (Set.Icc (0 : ℝ) 1) :=
  (TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) 1)).choose

theorem errorSampleSet_countable : errorSampleSet.Countable :=
  (TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) 1)).choose_spec.1

theorem errorSampleSet_dense : Dense errorSampleSet :=
  (TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) 1)).choose_spec.2

abbrev ErrorSample := errorSampleSet

instance : Countable ErrorSample := errorSampleSet_countable.to_subtype

def errorSampleTime (s : ErrorSample) : ℝ≥0 := ⟨s.1.1, s.1.property.1⟩

/-- A measurable anchored fitting functional on the full sampled function space. -/
def sampledAnchoredError (g : ErrorSample → ℝ) : ℝ :=
  ⨅ a : ℚ, ⨆ s : ErrorSample, |g s - (a : ℝ) * (s.1 : ℝ)|

/-- A measurable unrestricted fitting functional on the full sampled function space. -/
def sampledOptimalError (g : ErrorSample → ℝ) : ℝ :=
  ⨅ ab : ℚ × ℚ, ⨆ s : ErrorSample, |g s - (ab.1 : ℝ) * (s.1 : ℝ) - (ab.2 : ℝ)|

theorem measurable_sampledAnchoredError : Measurable sampledAnchoredError := by
  apply Measurable.iInf
  intro a
  apply Measurable.iSup
  intro s
  exact ((measurable_pi_apply s).sub measurable_const).abs

theorem measurable_sampledOptimalError : Measurable sampledOptimalError := by
  apply Measurable.iInf
  intro ab
  apply Measurable.iSup
  intro s
  exact (((measurable_pi_apply s).sub measurable_const).sub measurable_const).abs

/-- Continuity in the fitting coefficient reduces the anchored infimum to rationals. -/
theorem anchoredError_eq_rational_iInf (f : Path 1) :
    anchoredError f = ⨅ a : ℚ, dist f ((a : ℝ) • timePath 1) := by
  have hdense := (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).ciInf'
    (by fun_prop : Continuous (fun a : ℝ => dist f (a • timePath 1)))
  rw [iInf_range' (fun a : ℝ => dist f (a • timePath 1)) ((↑) : ℚ → ℝ)] at hdense
  rw [anchoredError_eq_sInf]
  change (⨅ a : ℝ, ⨆ t : Set.Icc (0 : ℝ) 1, |f t - a * (t : ℝ)|) = _
  simpa only [dist_anchored_fit] using hdense.symm

/-- The same reduction holds for rational slope-intercept pairs. -/
theorem optimalError_eq_rational_iInf (f : Path 1) :
    optimalError f = ⨅ ab : ℚ × ℚ,
      dist f ((ab.1 : ℝ) • timePath 1 + (ab.2 : ℝ) • (1 : Path 1)) := by
  have hd : DenseRange (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hdense := hd.ciInf' (by fun_prop : Continuous
    (fun ab : ℝ × ℝ => dist f (ab.1 • timePath 1 + ab.2 • (1 : Path 1))))
  rw [iInf_range' (fun ab : ℝ × ℝ => dist f (ab.1 • timePath 1 + ab.2 • (1 : Path 1)))
    (Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ))] at hdense
  rw [optimalError_eq_sInf]
  change (⨅ ab : ℝ × ℝ, ⨆ t : Set.Icc (0 : ℝ) 1,
    |f t - ab.1 * (t : ℝ) - ab.2|) = _
  simpa only [dist_affine_fit, Prod.map_apply] using! hdense.symm

/-- The measurable sampled functional is exactly the original anchored error
whenever the observed path is continuous. -/
theorem sampledAnchoredError_eq (f : Path 1) :
    sampledAnchoredError (fun s => f s.1) = anchoredError f := by
  rw [anchoredError_eq_rational_iInf]
  unfold sampledAnchoredError
  apply iInf_congr
  intro a
  rw [dist_anchored_fit]
  exact errorSampleSet_dense.ciSup'
    (f := fun t : Set.Icc (0 : ℝ) 1 => |f t - (a : ℝ) * (t : ℝ)|) (by fun_prop)

/-- The measurable sampled functional is exactly the original unrestricted error. -/
theorem sampledOptimalError_eq (f : Path 1) :
    sampledOptimalError (fun s => f s.1) = optimalError f := by
  rw [optimalError_eq_rational_iInf]
  unfold sampledOptimalError
  apply iInf_congr
  intro ab
  rw [dist_affine_fit]
  exact errorSampleSet_dense.ciSup'
    (f := fun t : Set.Icc (0 : ℝ) 1 => |f t - (ab.1 : ℝ) * (t : ℝ) - (ab.2 : ℝ)|)
    (by fun_prop)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {B C : ℝ≥0 → Ω → ℝ}

/-- A total continuous-path representative: extend a Brownian trajectory
constantly to negative times, and use zero on exceptional noncontinuous paths. -/
def processPath (B : ℝ≥0 → Ω → ℝ) (ω : Ω) : C(ℝ, ℝ) :=
  ContinuousMap.mkD (fun t : ℝ => B t.toNNReal ω) 0

omit [MeasurableSpace Ω] in
theorem processPath_apply_of_continuous {ω : Ω} (hω : Continuous (B · ω)) (t : ℝ≥0) :
    processPath B ω (t : ℝ) = B t ω := by
  unfold processPath
  have hc : Continuous (fun t : ℝ => B t.toNNReal ω) := hω.comp continuous_real_toNNReal
  rw [ContinuousMap.mkD_apply_of_continuous hc]
  simp

/-- The complete countable vector of observations in an interval of length T. -/
def sampledProcess (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) (s : ErrorSample) : ℝ :=
  B (T * errorSampleTime s) ω

omit [MeasurableSpace Ω] in
theorem unitPath_processPath_apply {ω : Ω} (hω : Continuous (B · ω))
    (T : ℝ≥0) (u : Set.Icc (0 : ℝ) 1) :
    unitPath (processPath B ω) (T : ℝ) u = B (T * ⟨u.1, u.property.1⟩) ω := by
  simpa only [unitPath, ContinuousMap.coe_mk, NNReal.coe_mul] using!
    processPath_apply_of_continuous hω (T * ⟨u.1, u.property.1⟩)

omit [MeasurableSpace Ω] in
theorem unitPath_processPath_sample {ω : Ω} (hω : Continuous (B · ω))
    (T : ℝ≥0) (s : ErrorSample) :
    unitPath (processPath B ω) (T : ℝ) s.1 = sampledProcess B T ω s := by
  simpa only [unitPath, ContinuousMap.coe_mk, NNReal.coe_mul, errorSampleTime,
    sampledProcess] using! processPath_apply_of_continuous hω (T * errorSampleTime s)

def anchoredProcessError (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  anchoredTimeError (processPath B ω) (T : ℝ)

def optimalProcessError (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  optimalTimeError (processPath B ω) (T : ℝ)

/-- The continuous representative retains Brownian motion's zero initial value a.e. -/
theorem processPath_zero_ae (hB : IsBrownianReal B μ) :
    (fun ω => processPath B ω 0) =ᵐ[μ] 0 := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hω h₀
  simpa using (processPath_apply_of_continuous hω 0).trans h₀

theorem aemeasurable_sampledProcess (hB : IsPreBrownianReal B μ) (T : ℝ≥0) :
    AEMeasurable (sampledProcess B T) μ :=
  aemeasurable_pi_lambda _ (fun s => hB.aemeasurable (T * errorSampleTime s))

/-- The sampled expression agrees a.e. with the actual anchored time error. -/
theorem sampledAnchoredError_ae_eq (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    (fun ω => sampledAnchoredError (sampledProcess B T ω)) =ᵐ[μ]
      anchoredProcessError B T := by
  filter_upwards [hB.cont] with ω hω
  have heq : sampledProcess B T ω = (fun s => unitPath (processPath B ω) (T : ℝ) s.1) := by
    funext s
    exact (unitPath_processPath_sample hω T s).symm
  rw [heq, sampledAnchoredError_eq]
  rfl

theorem sampledOptimalError_ae_eq (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    (fun ω => sampledOptimalError (sampledProcess B T ω)) =ᵐ[μ]
      optimalProcessError B T := by
  filter_upwards [hB.cont] with ω hω
  have heq : sampledProcess B T ω = (fun s => unitPath (processPath B ω) (T : ℝ) s.1) := by
    funext s
    exact (unitPath_processPath_sample hω T s).symm
  rw [heq, sampledOptimalError_eq]
  rfl

/-- The actual Brownian anchored fitting error is a.e. measurable at every fixed time. -/
theorem aemeasurable_anchoredProcessError (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    AEMeasurable (anchoredProcessError B T) μ :=
  (measurable_sampledAnchoredError.comp_aemeasurable
    (aemeasurable_sampledProcess hB.toIsPreBrownianReal T)).congr (sampledAnchoredError_ae_eq hB T)

theorem aemeasurable_optimalProcessError (hB : IsBrownianReal B μ) (T : ℝ≥0) :
    AEMeasurable (optimalProcessError B T) μ :=
  (measurable_sampledOptimalError.comp_aemeasurable
    (aemeasurable_sampledProcess hB.toIsPreBrownianReal T)).congr (sampledOptimalError_ae_eq hB T)

/-- The actual anchored errors of two Brownian motions on the same probability
space have the same law, obtained through the proved countable representation. -/
theorem identDistrib_anchoredProcessError (hB : IsBrownianReal B μ)
    (hC : IsBrownianReal C μ) (T : ℝ≥0) :
    IdentDistrib (anchoredProcessError B T) (anchoredProcessError C T) μ μ := by
  have hs := (identDistrib_countable_observations hB.toIsPreBrownianReal
    hC.toIsPreBrownianReal (fun s => T * errorSampleTime s)).comp measurable_sampledAnchoredError
  exact ((IdentDistrib.of_ae_eq hs.aemeasurable_fst (sampledAnchoredError_ae_eq hB T)).symm.trans hs).trans
    (IdentDistrib.of_ae_eq hs.aemeasurable_snd (sampledAnchoredError_ae_eq hC T))

theorem identDistrib_optimalProcessError (hB : IsBrownianReal B μ)
    (hC : IsBrownianReal C μ) (T : ℝ≥0) :
    IdentDistrib (optimalProcessError B T) (optimalProcessError C T) μ μ := by
  have hs := (identDistrib_countable_observations hB.toIsPreBrownianReal
    hC.toIsPreBrownianReal (fun s => T * errorSampleTime s)).comp measurable_sampledOptimalError
  exact ((IdentDistrib.of_ae_eq hs.aemeasurable_fst (sampledOptimalError_ae_eq hB T)).symm.trans hs).trans
    (IdentDistrib.of_ae_eq hs.aemeasurable_snd (sampledOptimalError_ae_eq hC T))

end BrownianAffine
