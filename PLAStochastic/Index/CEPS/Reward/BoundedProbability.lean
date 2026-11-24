import PLAStochastic.Index.CEPS.Reward.BoundedLadder
import PLAStochastic.Index.CEPS.Reward.TestSource

/-! # Identifying the probabilistic first-passage reward by renewal uniqueness

The renewal equation is proved from path splitting and the actual ladder
density. No probabilistic renewal equation is taken as a hypothesis.
-/

noncomputable section
open MeasureTheory Set Complex Filter
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ}
variable {s : ℂ} {φ : ℝ → ℂ} {D θ B : ℝ}

theorem halfBdd_passageTestTransform (hs : ‖s‖ ≤ 1) (hφ : Measurable φ)
    (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) :
    HalfBdd (halfLine (passageTestTransform ρ s φ)) :=
  halfBdd_halfLine (measurable_passageTestTransform ρ s hφ)
    (fun _ => ⟨B, hB, fun x _ _ => norm_passageTestTransform_le hs hφ hB hφB x⟩)

theorem passageTestTransform_renewal (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) s) D θ) (hθ : 0 < θ)
    (hs : ‖s‖ ≤ 1) (hφ : Measurable φ)
    (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) {x : ℝ} (hx : 0 ≤ x) :
    passageTestTransform ρ s φ x = rewardTestSource (ladderDensity ρ f (Ioi 0) s) φ x +
      convC (ladderDensity ρ f (Ioi 0) s) (halfLine (passageTestTransform ρ s φ)) x := by
  have hi : Integrable (fun h : ℝ =>
      if x < h then φ (h - x) * ladderDensity ρ f (Ioi 0) s h else 0) := by
    have hIo := integrableOn_rewardTestSource_integrand hg hφ (κ := 0)
      (fun y _ => by simpa using hφB y) hθ x
    exact hIo.integrable_indicator measurableSet_Ioi
  have hc := (hg.halfBdd hθ.le).integrable_convC_integrand
    (halfBdd_passageTestTransform (ρ := ρ) hs hφ hB hφB) x
  rw [passageTestTransform_eq_ladder_integral hf0 hfm hρ hs hφ hB hφB hx,
    rewardTestSource, convC, ← integral_add hi hc]
  refine integral_congr_ae (Eventually.of_forall fun h => ?_)
  dsimp only
  by_cases hh : x < h
  · rw [if_pos hh, if_pos hh, halfLine_of_neg _ (by linarith), mul_zero, add_zero]
    ring
  · rw [if_neg hh, if_neg hh, zero_add, halfLine_of_nonneg _ (by linarith)]

theorem passageTestTransform_eq_rewardSolution (hf0 : ∀ y, 0 ≤ f y) (hfm : Measurable f)
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) s) D θ) (hθ : 0 < θ)
    (hs : ‖s‖ ≤ 1) (hφ : Measurable φ)
    (hB : 0 ≤ B) (hφB : ∀ y, ‖φ y‖ ≤ B) {x : ℝ} (hx : 0 ≤ x) :
    passageTestTransform ρ s φ x =
      rewardSolution (ladderDensity ρ f (Ioi 0) s) (rewardTestSource (ladderDensity ρ f (Ioi 0) s) φ) x := by
  have he := eq_rewardSolution_of_renewal hg hθ.le
    (halfBdd_rewardTestSource hg hθ.le hφ (κ := 0)
      (fun y _ => by simpa using hφB y) hθ)
    (halfBdd_passageTestTransform (ρ := ρ) hs hφ hB hφB) (fun y hy => by
      rw [halfLine_of_nonneg _ hy]
      exact passageTestTransform_renewal hf0 hfm hρ hg hθ hs hφ hB hφB hy)
  rw [← he, halfLine_of_nonneg _ hx]

end PGM.WienerHopf
