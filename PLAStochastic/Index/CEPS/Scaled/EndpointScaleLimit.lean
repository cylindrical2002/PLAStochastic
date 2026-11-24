import PLAStochastic.Index.CEPS.Scaled.EndpointTrueError
import PLAStochastic.Index.CEPS.Scaled.RootZero

/-! # The actual marked endpoint has a continuous zero-scale extension -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_continuousAt_scale_zero {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (hm : 2 ≤ m) {z : ℂ} (hz : 0 ≤ z.re) :
    ContinuousAt (cepsScaledTrueRegularEndpoint dom ρW z) 0 := by
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hR := trueDenominatorScaleRadius_pos dom hW hθ hD hM0 1 z
  have hS : 0 < dom.pairPolynomialScaleBase 0 M / (2 + Real.sqrt ‖z‖) :=
    div_pos (pairPolynomialScaleBase_pos dom hW hθ hD 0 M) (by positivity)
  have hbD : ∀ᶠ b : ℝ in 𝓝 0,
      (b : ℂ) ∈ ball (0 : ℂ) (dom.trueDenominatorScaleRadius M 1 z) :=
    (Complex.continuous_ofReal.tendsto 0).eventually (ball_mem_nhds 0 hR)
  have hbS : ∀ᶠ b : ℝ in 𝓝 0,
      (b : ℂ) ∈ ball (0 : ℂ) (dom.pairPolynomialScaleBase 0 M / (2 + Real.sqrt ‖z‖)) :=
    (Complex.continuous_ofReal.tendsto 0).eventually (ball_mem_nhds 0 hS)
  let K := dom.trueEndpointErrorConstant 0 M * (2 + Real.sqrt ‖z‖) *
    Real.exp (-dom.entranceBridgeDecayRate * Real.sqrt ‖z‖)
  have he : Tendsto (fun b : ℝ => cepsScaledTrueRegularEndpoint dom ρW z b -
      cepsScaledSurrogateMarkedEndpoint dom ρW 0 z b) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun b : ℝ => K * |b|) ?_ ?_
    · filter_upwards [hbD, hbS] with b hbD hbS
      simpa only [zero_add, pow_one] using
        cepsScaledTrueRegularEndpoint_error_budget dom hW hθ hD hf hη hM 0 hm hz hbD hbS
    · simpa using (tendsto_const_nhds (x := K)).mul (continuous_abs.tendsto (0 : ℝ))
  have hs := (cepsScaledSurrogateMarkedEndpoint_differentiableOn dom hW hθ hD hf hη hM
    0 (by omega) hz 0 (mem_ball_self hS)).differentiableAt (ball_mem_nhds 0 hS)
  have ht := hs.continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto 0)
  have hadd := he.add ht
  simp only [Function.comp_apply, sub_add_cancel, zero_add] at hadd
  simpa only [ContinuousAt, cepsScaledTrueRegularEndpoint_zero dom ρW 0 z] using hadd

include hW hθ hD in
theorem cepsScaledTrueRegularEndpoint_scale_zero {z : ℂ} (hz : 0 ≤ z.re) :
    cepsScaledTrueRegularEndpoint dom ρW z 0 =
      exp (-cepsScaledSignedRoot D θ ρW 1 z 1 0) *
        (cepsScaledSignedRoot D θ ρW 1 z 1 0 - cepsScaledSignedRoot D θ ρW 1 z (-1) 0) /
          (-cepsScaledSignedRoot D θ ρW 1 z (-1) 0) := by
  let p := cepsScaledSignedRoot D θ ρW 1 z 1 0
  let a := cepsScaledSignedRoot D θ ρW 1 z (-1) 0
  let L := dom.canonL ρW 0 0 0
  have hQ := CepsC6.cepsQ_ne_zero dom hW hθ hD (μ := (0 : ℝ)) (q := (0 : ℂ)) (z := (0 : ℂ))
    (by simpa using dom.μ₀_pos.le) (by simpa using dom.q₀_pos.le)
    (by simp only [zero_re, abs_zero]; linarith [dom.c₀_pos])
  simp only [ofReal_zero] at hQ
  have hR := pairPolynomialScaleBase_pos dom hW hθ hD 0 0
  have hgap := cepsScaledPositiveMarkerGap_norm_lower dom hW hθ hD 0 0 1 le_rfl hz
    (mem_ball_self (div_pos hR (by positivity)))
  simp only [zero_mul, zero_sub, norm_neg] at hgap
  have ha : a ≠ 0 := norm_pos_iff.mp ((positiveMarkerGapLower_pos dom hW hθ hD).trans_le hgap)
  have hexp : exp (2 * L) * exp (-(2 * L)) = 1 := by
    rw [← exp_add]
    simp
  rw [cepsScaledTrueRegularEndpoint_eq_factors]
  unfold cepsScaledTrueDoubleMarkPrefactor cepsScaledTrueG cepsCanonTrueWeight cepsScaledEndpointCarrier
  simp only [ofReal_zero, zero_mul, mul_zero, add_zero, pow_two, mul_one, exp_zero,
    one_mul, cepsComplexScaledDiscount, zero_sub]
  change exp (2 * L) / cepsQ D θ ρW 0 0 0 *
    (exp (-p) * (cepsQ D θ ρW 0 0 0 * exp (-2 * L))) * ((p - a) / -a) =
      exp (-p) * (p - a) / -a
  simp only [neg_mul]
  field_simp [hQ, ha]
  linear_combination -(p - a) * hexp

end PGM
