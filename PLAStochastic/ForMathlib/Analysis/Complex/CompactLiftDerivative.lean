import PLAStochastic.ForMathlib.Analysis.Complex.CompactSpatialDeriv

/-! # Actual pointwise scalar derivatives pay compact-function block derivatives -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace K] [CompactSpace K]

/-- The derivative of a genuine analytic compact-function lift is determined by its
actual scalar evaluations. Agreement is required on an actual neighborhood. -/
theorem hasFDerivAt_compact_lift_of_scalar_block
    {f : E × ℂ → ℂ} {H : E × C(K, ℂ) → C(K, ℂ)} {p₀ : E} {V : ℂ}
    (hH : AnalyticAt ℂ H (p₀, 0))
    (hdf : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0))
    (happly : ∀ᶠ u in 𝓝 (p₀, (0 : C(K, ℂ))), ∀ k, H u k = f (u.1, u.2 k)) :
    HasFDerivAt H (V • ContinuousLinearMap.snd ℂ E C(K, ℂ)) (p₀, 0) := by
  have he : fderiv ℂ H (p₀, 0) = V • ContinuousLinearMap.snd ℂ E C(K, ℂ) := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousMap.ext
    intro k
    let L : E × C(K, ℂ) →L[ℂ] E × ℂ := (ContinuousLinearMap.fst ℂ E C(K, ℂ)).prod
      ((ContinuousMap.evalCLM ℂ k).comp (ContinuousLinearMap.snd ℂ E C(K, ℂ)))
    have hdf' : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (L (p₀, 0)) := by
      simpa [L] using hdf
    have hdS := hdf'.comp (p₀, (0 : C(K, ℂ))) L.hasFDerivAt
    have hdH := (ContinuousMap.evalCLM ℂ k).hasFDerivAt.comp (p₀, (0 : C(K, ℂ)))
      hH.differentiableAt.hasFDerivAt
    have heq : (fun v : E × C(K, ℂ) => f (L v)) =ᶠ[𝓝 (p₀, 0)] (fun v => H v k) := by
      filter_upwards [happly] with v hv
      exact (hv k).symm
    have hunique := (hdH.congr_of_eventuallyEq heq).unique hdS
    have hv := congrArg (fun T : E × C(K, ℂ) →L[ℂ] ℂ => T u) hunique
    simpa [L] using hv
  rw [← he]
  exact hH.differentiableAt.hasFDerivAt

end PGM
