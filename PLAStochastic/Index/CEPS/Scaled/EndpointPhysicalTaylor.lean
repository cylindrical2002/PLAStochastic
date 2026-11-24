import PLAStochastic.Index.CEPS.Scaled.EndpointActualRadius
import PLAStochastic.Index.CEPS.Scaled.EndpointZeroDerivative
import PLAStochastic.Index.CEPS.Scaled.EndpointBrownian

/-! # Physical marked endpoint decay, Taylor remainders and Brownian scale limit -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : 0 < b) (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z)) :
    ‖cepsScaledMarkedEndpoint dom ρW b z‖ ≤ dom.trueEndpointConstant M *
      (2 + Real.sqrt ‖z‖) * Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) := by
  rw [← cepsScaledTrueEndpoint_eq_physical_on_disc dom hW hθ hD M hz hb hbs]
  exact cepsScaledTrueRegularEndpoint_budget dom hW hθ hD hf hη hM hm hz
    (ball_subset_ball (trueEndpointScaleRadius_le dom M z) hbs)

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_taylor_le {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ} (hb : 0 < b)
    (hbs : (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z))
    (hbN : (b : ℂ) ∈ ball (0 : ℂ) ((dom.pairPolynomialScaleBase N M / (2 + Real.sqrt ‖z‖)) / 2)) :
    ‖cepsScaledMarkedEndpoint dom ρW b z -
      complexTaylorSum (cepsScaledSurrogateMarkedEndpoint dom ρW N z) (N + 1) 0 b‖ ≤
        (dom.trueEndpointErrorConstant N M * (2 + Real.sqrt ‖z‖) *
          Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖) +
            dom.endpointSurrogateTaylorBound N M (N + 1) z) * |b| ^ (N + 1) := by
  rw [← cepsScaledTrueEndpoint_eq_physical_on_disc dom hW hθ hD M hz hb hbs]
  exact cepsScaledTrueRegularEndpoint_taylor_le dom hW hθ hD hf hη hM N hN hz
    (ball_subset_ball (trueEndpointScaleRadius_le dom M z) hbs) hbN

include hW hθ hD in
theorem cepsScaledMarkedEndpoint_tendsto_scale_zero {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {z : ℂ} (hz : 0 ≤ z.re) :
    Tendsto (fun b : ℝ => cepsScaledMarkedEndpoint dom ρW b z) (𝓝[>] 0)
      (𝓝 (cepsBrownianMarkedEndpoint (cepsStepVar ρW) z)) := by
  have hR := trueEndpointScaleRadius_pos dom hW hθ hD ((cepsSobolev_nonneg m η fW).trans hM) z
  have hs := (cepsScaledTrueRegularEndpoint_continuousAt_scale_zero dom hW hθ hD hf hη hM hm hz).tendsto
    |>.mono_left (y := 𝓝[>] (0 : ℝ)) nhdsWithin_le_nhds
  rw [cepsScaledTrueRegularEndpoint_eq_brownian dom hW hθ hD hz] at hs
  apply hs.congr'
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0,
      (b : ℂ) ∈ ball (0 : ℂ) (dom.trueEndpointScaleRadius M z) :=
    Eventually.filter_mono nhdsWithin_le_nhds
      ((Complex.continuous_ofReal.tendsto 0).eventually (ball_mem_nhds 0 hR))
  filter_upwards [self_mem_nhdsWithin, hsmall] with b hb hbs
  exact cepsScaledTrueEndpoint_eq_physical_on_disc dom hW hθ hD M hz hb hbs

end PGM
