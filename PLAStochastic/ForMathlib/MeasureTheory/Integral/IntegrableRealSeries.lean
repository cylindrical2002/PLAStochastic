import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # An integrable real series from summable actual L1 norms -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem integrable_real_tsum_of_summable_integral_norm
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → Ω → ℝ}
    (hm : ∀ n, Measurable (F n)) (hi : ∀ n, Integrable (F n) μ)
    (hs : Summable (fun n => ∫ x, ‖F n x‖ ∂μ)) :
    Integrable (fun x => ∑' n,F n x) μ := by
  refine ⟨(Measurable.tsum hm).aestronglyMeasurable,?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  calc
    (∫⁻ x,‖∑' n,F n x‖ₑ ∂μ) ≤ ∫⁻ x,∑' n,‖F n x‖ₑ ∂μ :=
      lintegral_mono (fun x => enorm_tsum_le_tsum_enorm)
    _ = ∑' n,∫⁻ x,‖F n x‖ₑ ∂μ := lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)
    _ = ∑' n,ENNReal.ofReal (∫ x,‖F n x‖ ∂μ) := by
      congr 1
      funext n
      exact (ofReal_integral_norm_eq_lintegral_enorm (hi n)).symm
    _ < ∞ := hs.tsum_ofReal_lt_top

end BrownianAffine
