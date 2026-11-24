import PLAStochastic.Index.CEPS.Scaled.EndpointZeroMark

/-! # The regular endpoint has the proved physical zero-mark derivative -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_hasDerivAt_mark_zero {b : ℝ} (hb : 0 < b)
    (hμ : |b| ≤ dom.μ₀) : HasDerivAt (fun z => cepsScaledTrueRegularEndpoint dom ρW z b)
      (-cepsScaledZeroEndpoint dom ρW b) 0 := by
  have hQ : Tendsto (fun z : ℂ => cepsComplexScaledDiscount 1 z b) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => cepsComplexScaledDiscount 1 z b) := by
      unfold cepsComplexScaledDiscount
      fun_prop
    simpa only [cepsComplexScaledDiscount, mul_zero, zero_mul] using hc.tendsto 0
  have hT : Tendsto (fun z : ℂ => (b : ℂ) ^ 2 * z) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun z : ℂ => (b : ℂ) ^ 2 * z) := by fun_prop
    simpa only [mul_zero] using hc.tendsto (0 : ℂ)
  have he : (fun z => cepsScaledTrueRegularEndpoint dom ρW z b) =ᶠ[𝓝 0]
      cepsScaledMarkedEndpoint dom ρW b := by
    filter_upwards [hQ.eventually (ball_mem_nhds 0 dom.q₀_pos),
      hT.eventually (ball_mem_nhds 0 (cepsMarkedUnitRadius_pos hD hθ))] with z hzQ hzT
    exact cepsScaledTrueRegularEndpoint_eq_filled_all_marks dom hW hθ hD hb hμ
      (mem_ball_zero_iff.mp hzQ).le hzT
  exact (cepsScaledMarkedEndpoint_hasDerivAt_zero dom hW hθ hD hb hμ).congr_of_eventuallyEq he

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_deriv_mark_zero {b : ℝ} (hb : 0 < b)
    (hμ : |b| ≤ dom.μ₀) :
    -deriv (fun z => cepsScaledTrueRegularEndpoint dom ρW z b) 0 = cepsScaledZeroEndpoint dom ρW b := by
  rw [(cepsScaledTrueRegularEndpoint_hasDerivAt_mark_zero dom hW hθ hD hb hμ).deriv, neg_neg]

end PGM
