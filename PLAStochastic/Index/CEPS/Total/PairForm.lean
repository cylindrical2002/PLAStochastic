import PLAStochastic.Index.CEPS.Total.Identify
import PLAStochastic.Index.CEPS.Normal.ActualEquality

/-!
# WP10: the physical normal pair in the `cepsNormalData` form

`cepsPhysicalPair dom ρW b z μ` (the physical pair of `Scaled/`, built from `cepsWHNormalData`)
is the complete regular pair `e^{tl} Ĥ² (-∂_q Û - w Û)` built from the original root-zone data
`cepsNormalData` (`regularEntrance`, `regularBridge`), at `t = b² z`, `w = 1/b`, `q = t(1+μ)`,
`l = w(1+μ)` (`cepsPhysicalPair_eq_normalData`). This is the form in which the S-6 pair error is
stated on the WP9 side.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The physical normal pair with the root-zone data `cepsNormalData`. -/
theorem cepsPhysicalPair_eq_normalData {b : ℝ} (hb : 0 < b) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {z : ℂ} (hq : ‖(b : ℂ) ^ 2 * z * (1 + (μ : ℂ))‖ < dom.q₀)
    (ht : (b : ℂ) ^ 2 * z ∈ ball (0 : ℂ) dom.ρA) :
    cepsPhysicalPair dom ρW b z μ =
      exp ((b : ℂ) ^ 2 * z * ((b : ℂ)⁻¹ * (1 + (μ : ℂ)))) *
        ((cepsNormalData D θ ρW μ ((b : ℂ) ^ 2 * z * (1 + (μ : ℂ)))).regularEntrance
          (dom.canonL ρW) μ ((b : ℂ) ^ 2 * z * (1 + (μ : ℂ))) ((b : ℂ)⁻¹ * (1 + (μ : ℂ)))
          ((b : ℂ) ^ 2 * z)) ^ 2 *
        (-deriv (fun q' => (cepsNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q'
            ((b : ℂ)⁻¹ * (1 + (μ : ℂ)))) ((b : ℂ) ^ 2 * z * (1 + (μ : ℂ))) -
          (b : ℂ)⁻¹ * (cepsNormalData D θ ρW μ ((b : ℂ) ^ 2 * z * (1 + (μ : ℂ)))).regularBridge
            (dom.canonL ρW) μ ((b : ℂ) ^ 2 * z * (1 + (μ : ℂ))) ((b : ℂ)⁻¹ * (1 + (μ : ℂ)))) := by
  set t := (b : ℂ) ^ 2 * z
  set q := t * (1 + (μ : ℂ))
  set l := (b : ℂ)⁻¹ * (1 + (μ : ℂ))
  have hb0 : b ≠ 0 := hb.ne'
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hl : (1 + (μ : ℂ)) / (b : ℂ) = l := by
    simp only [l]; rw [div_eq_inv_mul]
  have hev : (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l) =ᶠ[nhds q]
      (fun q' => (cepsNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hq)] with q' hq'
    exact (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' (mem_ball_zero_iff.mp hq').le
      (dom.canonL ρW) l ht).2
  obtain ⟨hE, hB⟩ := cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' hq.le (dom.canonL ρW) l ht
  unfold cepsPhysicalPair cepsScaledTruePhysicalPair
  simp only
  rw [ofReal_mul_div_cancel hb0, scaledDiscount_div hb0, hl]
  change exp (t * l) * ((cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t) ^ 2 *
      (-deriv (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge (dom.canonL ρW) μ q' l) q -
        (b : ℂ)⁻¹ * (cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l) = _
  rw [hE, hB, hev.deriv_eq]

end PGM
