import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences

/-! Compactness upgrades joint sequential convergence to uniform convergence. -/
open Set Filter
open scoped Topology Classical
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Compactness upgrades convergence along every moving point to uniform convergence. -/
theorem tendstoUniformlyOn_of_joint_sequence
    {α β : Type*} [MetricSpace α] [PseudoMetricSpace β] {K : Set α} (hK : IsCompact K)
    {F : ℕ → α → β} {f : α → β} (hf : ContinuousOn f K)
    (hj : ∀ k : ℕ → ℕ, Tendsto k atTop atTop → ∀ u : ℕ → α, (∀ n, u n ∈ K) →
      ∀ w ∈ K, Tendsto u atTop (𝓝 w) → Tendsto (fun n => F (k n) (u n)) atTop (𝓝 (f w))) :
    TendstoUniformlyOn F f atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra h
  rw [eventually_atTop] at h
  push Not at h
  choose k hk u hu hb using h
  have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  obtain ⟨w, hw, φ, hφ, hφt⟩ := hK.tendsto_subseq hu
  have ht := hj (k ∘ φ) (hkt.comp hφ.tendsto_atTop) (u ∘ φ) (fun n => hu (φ n)) w hw hφt
  have hwf : Tendsto (fun n => f (u (φ n))) atTop (𝓝 (f w)) :=
    (hf w hw).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hφt, Eventually.of_forall (fun n => hu (φ n))⟩)
  have hd : Tendsto (fun n => dist (f (u (φ n))) (F (k (φ n)) (u (φ n)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, dist_self] using! hwf.dist ht
  obtain ⟨n, hn⟩ := (hd.eventually (Iio_mem_nhds hε)).exists
  exact not_lt_of_ge (hb (φ n)) hn

end BrownianAffine
