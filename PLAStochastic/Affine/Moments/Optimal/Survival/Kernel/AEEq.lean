import PLAStochastic.Affine.Moments.Optimal.Width.SurvivalWidth
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine

/-- A monotone function agrees at every continuity point of an almost-everywhere
representative. The proof uses positive measure of every real open interval. -/
theorem monotone_eq_continuousAt_of_ae_eq {β : Type*} [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {f g : ℝ → β} (hf : Monotone f) (he : f =ᵐ[volume] g)
    {r : ℝ} (hg : ContinuousAt g r) : f r = g r := by
  have hd := volume.dense_of_ae he
  apply le_antisymm
  · by_contra h
    have hh : g r < f r := lt_of_not_ge h
    have hn : ∀ᶠ s in 𝓝 r, g s < f r := hg (Iio_mem_nhds hh)
    obtain ⟨δ,hδ,hs⟩ := Metric.eventually_nhds_iff.mp hn
    obtain ⟨s,heq,hrs,hsδ⟩ := hd.exists_between (show r < r+δ by linarith)
    have hdist : dist s r < δ := by rw [Real.dist_eq,abs_of_pos (by linarith : 0 < s-r)]; linarith
    have hsf : f s < f r := by rw [heq]; exact hs hdist
    exact (not_lt_of_ge (hf hrs.le)) hsf
  · by_contra h
    have hh : f r < g r := lt_of_not_ge h
    have hn : ∀ᶠ s in 𝓝 r, f r < g s := hg (Ioi_mem_nhds hh)
    obtain ⟨δ,hδ,hs⟩ := Metric.eventually_nhds_iff.mp hn
    obtain ⟨s,heq,hδs,hsr⟩ := hd.exists_between (show r-δ < r by linarith)
    have hdist : dist s r < δ := by rw [Real.dist_eq,abs_of_neg (by linarith : s-r < 0)]; linarith
    have hsf : f r < f s := by rw [heq]; exact hs hdist
    exact (not_lt_of_ge (hf hsr.le)) hsf

end BrownianAffine
