import PLAStochastic.ForMathlib.Analysis.Complex.ParametricBanachInverseGerm
import PLAStochastic.ForMathlib.Analysis.Complex.CompactSpatialDeriv

/-! # Analytic compact-function inverse germs agree with the actual scalar inverse -/

noncomputable section
open Complex Filter Topology Metric
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [TopologicalSpace K] [CompactSpace K]

/-- A pointwise analytic family has a genuine compact-function inverse germ. Local scalar
left-inverse identities identify every value of that germ on one actual neighborhood. -/
theorem exists_analytic_parametric_inverse_lift_germ
    {f g : E × ℂ → ℂ} {H : E × C(K, ℂ) → C(K, ℂ)} {p₀ : E} {V : ℂ}
    (hH : AnalyticAt ℂ H (p₀, 0))
    (hHD : HasFDerivAt H (V • ContinuousLinearMap.snd ℂ E C(K, ℂ)) (p₀, 0))
    (hV : V ≠ 0) (hH₀ : H (p₀, 0) = 0)
    (happly : ∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, H u k = f (u.1, u.2 k))
    (hleft : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), g (u.1, f u) = u.2) :
    ∃ G : E × C(K, ℂ) → C(K, ℂ), AnalyticAt ℂ G (p₀, 0) ∧ G (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), H (u.1, G u) = u.2) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, G u k = g (u.1, u.2 k)) := by
  obtain ⟨G, hG, hG₀, hright, _⟩ := exists_analytic_parametric_banach_inverse_germ hH hHD hV hH₀
  refine ⟨G, hG, hG₀, hright, ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hleft
  have hc : ContinuousAt (fun u : E × C(K, ℂ) => (u.1, G u)) (p₀, 0) :=
    continuousAt_fst.prodMk hG.continuousAt
  have ht : Tendsto (fun u : E × C(K, ℂ) => (u.1, G u)) (𝓝 (p₀, 0)) (𝓝 (p₀, 0)) := by
    simpa only [hG₀] using hc.tendsto
  have hnear : ∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), (u.1, G u) ∈ ball (p₀, 0) r :=
    ht (ball_mem_nhds _ hr)
  filter_upwards [hright, ht happly, hnear] with u hu he hn
  intro k
  have hnorm : max ‖u.1 - p₀‖ ‖G u‖ < r := by
    rw [mem_ball, dist_eq_norm] at hn
    simpa [Prod.norm_def] using hn
  have hk : (u.1, G u k) ∈ ball (p₀, (0 : ℂ)) r := by
    rw [mem_ball, dist_eq_norm]
    simpa [Prod.norm_def] using
      max_lt (max_lt_iff.mp hnorm).1 ((G u).norm_coe_le_norm k |>.trans_lt (max_lt_iff.mp hnorm).2)
  have hs : g (u.1, f (u.1, G u k)) = G u k := hball hk
  have hf := congrArg (fun S : C(K, ℂ) => S k) hu
  change H (u.1, G u) k = u.2 k at hf
  rw [he k] at hf
  rw [hf] at hs
  exact hs.symm

end PGM
