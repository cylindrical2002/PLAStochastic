import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws

/-!
# Countable observation vectors of pre-Brownian processes

Equal Brownian finite-dimensional laws identify the law of every countable vector of
observations. The theorem was moved verbatim from the measurable-error file so that
general Brownian results do not depend on the affine fitting errors.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {B C : ℝ≥0 → Ω → ℝ}

/-- Equal Brownian finite-dimensional laws identify every countable vector of
observations. Its measurability is derived from coordinate measurability. -/
theorem identDistrib_countable_observations {ι : Type*} [Countable ι]
    (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C μ) (t : ι → ℝ≥0) :
    IdentDistrib (fun ω i => B (t i) ω) (fun ω i => C (t i) ω) μ μ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hBm : AEMeasurable (fun ω i => B (t i) ω) μ :=
    aemeasurable_pi_lambda _ (fun i => hB.aemeasurable (t i))
  have hCm : AEMeasurable (fun ω i => C (t i) ω) μ :=
    aemeasurable_pi_lambda _ (fun i => hC.aemeasurable (t i))
  apply (identDistrib_iff_forall_finset_identDistrib hBm hCm).mpr
  intro I
  let J := I.image t
  let project : (J → ℝ) → I → ℝ := fun z i =>
    z ⟨t i.1, Finset.mem_image.mpr ⟨i.1, i.property, rfl⟩⟩
  have hp : Measurable project :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  exact ((hB.hasLaw J).identDistrib (hC.hasLaw J)).comp hp

end BrownianAffine
