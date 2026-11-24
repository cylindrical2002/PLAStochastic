import PLAStochastic.Index.CEPS.Normal.ZeroHalfPair
import PLAStochastic.Index.CEPS.Canonical.SpatialTransport

/-! # Drift transport of the regular zero-discount endpoint -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {D θ v : ℝ}

/-- The finite endpoint obtained after removing the common discount pole. -/
def halfZeroEndpoint (dom : CepsCanonDomain D θ v) (ρW : Measure ℝ) (μ : ℝ) (w : ℂ) : ℂ :=
  1 / 2 + (cepsStepVar ρW : ℂ) / 2 / (μ : ℂ) ^ 2 -
    2 * deriv (dom.canonL ρW μ 0) 0 / (μ : ℂ) - w * (1 + (μ : ℂ)) / (μ : ℂ)

variable {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem hasDerivAt_halfZeroEndpoint {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) (hne : μ ≠ 0) (w : ℂ) :
    HasDerivAt (fun t : ℝ => dom.halfZeroEndpoint ρW t w)
      (-(cepsStepVar ρW : ℂ) / (μ : ℂ) ^ 3 + w / (μ : ℂ) ^ 2 +
        2 * deriv (dom.canonL ρW μ 0) 0 / (μ : ℂ) ^ 2 +
        2 * deriv (fun q => dom.canonL ρW μ q 0) 0 / (μ : ℂ)) μ := by
  have hmne : (μ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hne
  have hmu : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 μ := (hasDerivAt_id μ).ofReal_comp
  have hr := dom.hasDerivAt_canonSpatialSlope_mu hW hθ hD hf hm hη hμ
    (q := 0) (by simpa using div_pos dom.q₀_pos (by norm_num : (0 : ℝ) < 4))
  have hV := (hasDerivAt_const μ ((cepsStepVar ρW : ℂ) / 2)).div (hmu.pow 2) (pow_ne_zero 2 hmne)
  have hR := (hr.const_mul 2).div hmu hmne
  have hw := ((hmu.const_add 1).const_mul w).div hmu hmne
  have hd := (((hasDerivAt_const μ (1 / 2 : ℂ)).add hV).sub hR).sub hw
  refine hd.congr_deriv ?_
  dsimp only [Pi.pow_apply]
  norm_num
  field_simp [hmne]
  ring

include hW hθ hD in
/-- Zero-discount P12 transport, using the genuinely cancelled entrance. -/
theorem actual_halfPair_zeroDiscount {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} (hμ : |μ| < dom.μ₀ / 4) (hp : 0 < μ) (w : ℂ) :
    HasDerivAt (fun t : ℝ => dom.halfZeroEndpoint ρW t w)
      (cepsNormalRegularHalfPairAt (cepsNormalData D θ ρW) (dom.canonL ρW) μ 0 0 w) μ := by
  rw [cepsNormal_regularHalfPair_zeroDiscount dom hW hθ hD
    (show |μ| ≤ dom.μ₀ by linarith [dom.μ₀_pos]) hp]
  exact dom.hasDerivAt_halfZeroEndpoint hW hθ hD hf hm hη hμ hp.ne' w

end PGM.CepsCanonDomain
