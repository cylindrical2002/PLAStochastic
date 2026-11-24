import PLAStochastic.Index.CEPS.Reward.TruncatedSource

/-! # First-passage probability identification for both signs of the mark

Exponential integrability and two dominated-convergence arguments remove
all truncations. No sign condition on the real part of the mark remains.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace PGM.WienerHopf

variable {ρ : Measure ℝ} [IsProbabilityMeasure ρ] {f : ℝ → ℝ}
variable {s a : ℂ} {D θ : ℝ}

theorem passageTransform_eq_rewardSolution_of_expDensity (hf0 : ∀ y, 0 ≤ f y)
    (hfm : Measurable f) (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hg : IsExpDensity (ladderDensity ρ f (Ioi 0) s) D θ)
    (hg1 : IsExpDensity (ladderDensity ρ f (Ioi 0) 1) D θ) (hθ : 0 < θ)
    (hs : ‖s‖ ≤ 1) (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    passageTransform ρ s a x = rewardSolution (ladderDensity ρ f (Ioi 0) s)
      (rewardSource (ladderDensity ρ f (Ioi 0) s) a) x := by
  have he : (fun n => passageTestTransform ρ s (truncatedMark a n) x) =
      (fun n => rewardSolution (ladderDensity ρ f (Ioi 0) s)
        (rewardTestSource (ladderDensity ρ f (Ioi 0) s) (truncatedMark a n)) x) := by
    funext n
    exact passageTestTransform_eq_rewardSolution hf0 hfm hρ hg hθ hs
      (measurable_truncatedMark a n) (Real.exp_pos _).le (norm_truncatedMark_le a n) hx
  have hP := passageTestTransform_truncatedMark_tendsto hf0 hfm hρ hg1 hθ hs ha hx
  have hR := rewardTestSolution_truncatedMark_tendsto hg hθ.le ha hx
  rw [he] at hP
  exact tendsto_nhds_unique hP hR

end PGM.WienerHopf
