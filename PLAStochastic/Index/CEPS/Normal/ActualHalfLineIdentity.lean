import PLAStochastic.Index.CEPS.Normal.ActualHalfLineTransport

/-! # Identification of the actual transport components with the original pair -/

noncomputable section
open Complex MeasureTheory Filter Topology Set Metric
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalData_psiPlus_eq {μ q : ℂ} (hx : (μ, q) ∈ cepsSPRegion D θ ρW) :
    (cepsNormalData D θ ρW μ q).ψp = deriv (cepsCgf ρW) (cepsRootPlus D θ ρW μ q) + μ := by
  have hr : ‖cepsRootR D θ ρW μ q‖ < cepsChartRho D θ :=
    norm_sqrt_lt (cepsChartRho_pos hD hθ) hx.2
  have hb := rootPlus_mem_ball hW hθ hD hx.1 hr
  have hp := ((differentiableOn_cepsCgf hW hθ hD) _ hb).differentiableAt
    (isOpen_ball.mem_nhds hb)
  have hd := hp.hasDerivAt.add ((hasDerivAt_id (cepsRootPlus D θ ρW μ q)).const_mul μ)
  change deriv (fun z => cepsCgf ρW z + μ * z) (cepsRootPlus D θ ρW μ q) = _
  simpa only [id_eq, mul_one] using! hd.deriv

include hW hθ hD in
theorem cepsNormalHalfPairAt_actual_eq {μ : ℝ} {q t w : ℂ}
    (hx : ((μ : ℂ), q) ∈ cepsSPRegion D θ ρW)
    (L : ℂ → ℂ → ℂ → ℂ) :
    cepsNormalHalfPairAt (cepsNormalData D θ ρW) L μ q t w =
      cepsNormalHalfPairComponents (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) L μ q t w := by
  have hpath : ContinuousAt (fun q' : ℂ => ((μ : ℂ), q')) q := by fun_prop
  have hmem := hpath.preimage_mem_nhds ((isOpen_cepsSPRegion hW hθ hD).mem_nhds hx)
  have he : (fun q' => (cepsNormalData D θ ρW μ q').halfBridge L μ q'
      (w * (1 + (μ : ℂ)))) =ᶠ[𝓝 q]
      (fun q' => cepsNormalRootSlope (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q) μ q' *
          exp (-cepsRootPlus D θ ρW μ q' * (w * (1 + (μ : ℂ))) -
            2 * L μ q' (cepsRootPlus D θ ρW μ q'))) := by
    filter_upwards [hmem] with q' hq'
    rw [CepsNormalData.halfBridge, cepsNormalData_psiPlus_eq hW hθ hD hq']
    rfl
  unfold cepsNormalHalfPairAt cepsNormalHalfPairComponents
  dsimp only
  rw [he.deriv_eq, he.eq_of_nhds]
  rfl

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

include hW hθ hD in
theorem actual_halfPrimitive_eq_amplitude {μ : ℝ} {q t w : ℂ}
    (hx : ((μ : ℂ), q) ∈ cepsSPRegion D θ ρW) :
    cepsNormalHalfPrimitive (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW) μ q t w =
      (cepsNormalData D θ ρW μ q).amplitude (dom.canonL ρW) μ q t *
        exp (-(cepsRootPlus D θ ρW μ q - t) * (w * (1 + (μ : ℂ)))) /
          cepsD ρW μ q t := by
  rw [CepsNormalData.amplitude, cepsNormalData_psiPlus_eq hW hθ hD hx]
  unfold cepsNormalHalfPrimitive
  dsimp only [cepsNormalData, cepsNormalRootSlope]
  rw [sub_eq_add_neg (2 * dom.canonL ρW μ q t -
    2 * dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)), exp_add]
  simp only [div_eq_mul_inv, neg_mul]
  ring

include hW hθ hD in
/-- The actual P12 derivative is the original canonical half-line occupation pair. -/
theorem actual_halfPair_marked_original {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) (hm : 2 ≤ m) (hη : 2 * dom.c₀ ≤ η)
    {μ : ℝ} {t w : ℂ} (hμ : |μ| < dom.μ₀ / 4)
    (hq : ‖t * (1 + (μ : ℂ))‖ < dom.q₀ / 4)
    (hre : 0 ≤ (t * (1 + (μ : ℂ))).re) (ht : t.re < dom.c₀)
    (hne : t * (1 + (μ : ℂ)) - cepsMorseMin D θ ρW μ ≠ 0)
    (hd0 : cepsD ρW μ (t * (1 + (μ : ℂ))) t ≠ 0) :
    HasDerivAt
      (fun x : ℝ => cepsNormalHalfPrimitive (cepsCgf ρW)
        (fun (y : ℝ) q => cepsRootPlus D θ ρW y q)
        (fun (y : ℝ) q z => cepsD ρW y q z) (dom.canonL ρW)
        x (t * (1 + (x : ℂ))) t w)
      (cepsNormalHalfPair (cepsNormalData D θ ρW) (dom.canonL ρW) μ t w) μ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by
    rw [norm_real, Real.norm_eq_abs]
    linarith [dom.μ₀_pos]
  have hx := dom.mem_SPRegion hW hθ hD hμ'
    (show ‖t * (1 + (μ : ℂ))‖ ≤ dom.q₀ by linarith [dom.q₀_pos])
  have he := cepsNormalHalfPairAt_actual_eq hW hθ hD (t := t) (w := w) hx (dom.canonL ρW)
  exact (dom.actual_halfPair_marked hW hθ hD hf hm hη hμ hq hre ht hne hd0).congr_deriv
    he.symm

end CepsCanonDomain
end PGM
