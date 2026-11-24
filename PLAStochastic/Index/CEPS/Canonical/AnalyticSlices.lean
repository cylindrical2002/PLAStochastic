import PLAStochastic.Index.CEPS.Canonical.JointDifferential

/-! # Analytic discount curves of the actual canonical factor -/

noncomputable section
open Complex MeasureTheory Set Metric Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem analyticAt_canonL_comp_spatial {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} {Z : ℂ → ℂ}
    (hZ : AnalyticAt ℂ Z q) (hq : ‖q‖ < dom.q₀) (hζ : (Z q).re < dom.c₀) :
    AnalyticAt ℂ (fun r => dom.canonL ρW μ r (Z r)) q := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  have hqN : ∀ᶠ r : ℂ in 𝓝 q, ‖r‖ < dom.q₀ :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hq
  have hZN : ∀ᶠ r : ℂ in 𝓝 q, (Z r).re < dom.c₀ :=
    hZ.continuousAt.preimage_mem_nhds
      ((isOpen_lt continuous_re continuous_const).mem_nhds hζ)
  filter_upwards [hZ.eventually_analyticAt, hqN, hZN] with r hr hqr hZr
  simpa only [Function.comp_def, id_eq] using!
    (dom.differentiableAt_canonL_qz hW hθ hD hμ hqr hZr).comp r
      (differentiableAt_id.prodMk hr.differentiableAt)

include hW hθ hD in
theorem analyticAt_canonL_comp_qz {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {t : ℂ} {Q Z : ℂ → ℂ}
    (hQ : AnalyticAt ℂ Q t) (hZ : AnalyticAt ℂ Z t)
    (hq : ‖Q t‖ < dom.q₀) (hζ : (Z t).re < dom.c₀) :
    AnalyticAt ℂ (fun r => dom.canonL ρW μ (Q r) (Z r)) t := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  have hqN : ∀ᶠ r : ℂ in 𝓝 t, ‖Q r‖ < dom.q₀ :=
    hQ.continuousAt.preimage_mem_nhds ((isOpen_lt continuous_norm continuous_const).mem_nhds hq)
  have hZN : ∀ᶠ r : ℂ in 𝓝 t, (Z r).re < dom.c₀ :=
    hZ.continuousAt.preimage_mem_nhds ((isOpen_lt continuous_re continuous_const).mem_nhds hζ)
  filter_upwards [hQ.eventually_analyticAt, hZ.eventually_analyticAt, hqN, hZN]
    with r hrQ hrZ hqr hZr
  simpa only [Function.comp_def] using!
    (dom.differentiableAt_canonL_qz hW hθ hD hμ hqr hZr).comp r
      (hrQ.differentiableAt.prodMk hrZ.differentiableAt)

end PGM.CepsCanonDomain
