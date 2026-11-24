import PLAStochastic.ForMathlib.Analysis.Complex.Osgood

/-! # Measurability of derivatives with a fixed parameter cutoff -/

noncomputable section
open Set Filter Topology MeasureTheory
namespace PGM

theorem aestronglyMeasurable_cutoff_deriv_param {S : Set ℝ} (hS : MeasurableSet S)
    {G : ℝ → ℂ → ℂ} {z : ℂ} {h : ℕ → ℂ}
    (hne : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hc : ∀ n, ContinuousOn (fun a => G a (z + h n)) S)
    (hc0 : ContinuousOn (fun a => G a z) S)
    (hd : ∀ a ∈ S, DifferentiableAt ℂ (G a) z) :
    AEStronglyMeasurable (S.indicator (fun a => deriv (G a) z)) := by
  classical
  let F : ℝ → ℂ → ℂ := fun a ζ => if a ∈ S then G a ζ else 0
  have hm : ∀ n, AEStronglyMeasurable (fun a => F a (z + h n)) := fun n =>
    ((hc n).measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hm0 : AEStronglyMeasurable (fun a => F a z) :=
    (hc0.measurable_piecewise continuous_const.continuousOn hS).aestronglyMeasurable
  have hdF : ∀ a, DifferentiableAt ℂ (F a) z := by
    intro a
    by_cases ha : a ∈ S
    · simpa only [F, if_pos ha] using hd a ha
    · simp only [F, if_neg ha]
      exact differentiableAt_const 0
  have hmF := aestronglyMeasurable_deriv_param (G := F) (q₀ := z) hne hlim hm hm0 hdF
  refine hmF.congr (ae_of_all _ fun a => ?_)
  by_cases ha : a ∈ S <;> simp [F, ha]

end PGM
