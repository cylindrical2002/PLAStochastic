import PLAStochastic.Index.CEPS.Reward.PassageLadder
import PLAStochastic.Index.CEPS.Reward.Source

/-! # Identifying the probabilistic first-passage reward by renewal uniqueness

The renewal equation is proved from path splitting and the actual ladder
density. No probabilistic renewal equation is taken as a hypothesis.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ}
variable {s a : ℂ} {D θ : ℝ}

theorem halfBdd_passageTransform (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re) :
    HalfBdd (halfLine (passageTransform ρ s a)) :=
  halfBdd_halfLine (measurable_passageTransform ρ s a)
    (fun _ => ⟨1, zero_le_one, fun x _ _ => norm_passageTransform_le_one hs ha x⟩)

theorem passageTransform_renewal (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) s) D θ) (hθ : 0 ≤ θ)
    (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re) (haθ : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    passageTransform ρ s a x = rewardSource (ladderDensity ρ f (Ioi 0) s) a x +
      convC (ladderDensity ρ f (Ioi 0) s) (halfLine (passageTransform ρ s a)) x := by
  have hi : Integrable (fun h : ℝ =>
      if x < h then cexp (-a * (h - x : ℝ)) * ladderDensity ρ f (Ioi 0) s h else 0) := by
    have hIo := integrableOn_rewardSource_integrand hg (a₀ := ‖a‖) le_rfl haθ x
    exact hIo.integrable_indicator measurableSet_Ioi
  have hc := (hg.halfBdd hθ).integrable_convC_integrand
    (halfBdd_passageTransform (ρ := ρ) hs ha) x
  rw [passageTransform_eq_ladder_integral hf0 hfm hρ hs ha hx,
    rewardSource, convC, ← integral_add hi hc]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp only
  by_cases hh : x < h
  · rw [if_pos hh, if_pos hh, halfLine_of_neg _ (by linarith), mul_zero, add_zero]
    ring
  · rw [if_neg hh, if_neg hh, zero_add, halfLine_of_nonneg _ (by linarith)]

theorem passageTransform_eq_rewardSolution (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) s) D θ) (hθ : 0 ≤ θ)
    (hs : ‖s‖ ≤ 1) (ha : 0 ≤ a.re) (haθ : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    passageTransform ρ s a x =
      rewardSolution (ladderDensity ρ f (Ioi 0) s) (rewardSource (ladderDensity ρ f (Ioi 0) s) a) x := by
  have he := eq_rewardSolution_of_renewal hg hθ
    (halfBdd_rewardSource hg hθ (a₀ := ‖a‖) le_rfl haθ)
    (halfBdd_passageTransform (ρ := ρ) hs ha) (fun y hy => by
      rw [halfLine_of_nonneg _ hy]
      exact passageTransform_renewal hf0 hfm hρ hg hθ hs ha haθ hy)
  rw [← he, halfLine_of_nonneg _ hx]

end PGM.WienerHopf
