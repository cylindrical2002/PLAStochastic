import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Composition

/-! # Scalar analytic curves in complex differentiable open domains -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem analyticAt_complex_curve_of_differentiableOn {F : E → ℂ} {U : Set E}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {a : ℂ → E}
    (ha : AnalyticAt ℂ a 0) (ha0 : a 0 ∈ U) :
    AnalyticAt ℂ (fun b => F (a b)) 0 := by
  have hmap : ∀ᶠ b : ℂ in 𝓝 0, a b ∈ U :=
    ha.continuousAt.eventually (hU.mem_nhds ha0)
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [hmap, analyticAt_iff_eventually_differentiableAt.mp ha] with b hb hab
  have hd := ((hF _ hb).differentiableAt (hU.mem_nhds hb)).comp b hab
  exact hd

end PGM
