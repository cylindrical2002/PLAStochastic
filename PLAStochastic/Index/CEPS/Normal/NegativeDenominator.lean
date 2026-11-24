import PLAStochastic.Index.CEPS.Normal.NegativeDelta

/-! # The genuine normal divided denominator on a common negative-real extension -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- The genuine divided-slope denominator is nonzero at every point of the half-disc. -/
theorem cepsNormal_actual_dslope_ne_zero_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    dslope ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
      (cepsRootMinus D θ ρW μ q) (cepsRootPlus D θ ρW μ q) ≠ 0 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  let a := cepsWHNormalData D θ ρW μ q
  have hm := dom.norm_rootMinus_le hW hθ hD hμ' hq
  change ‖a.βm‖ ≤ dom.c₀ / 4 at hm
  have hmA : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hmA
  obtain ⟨hl0, hM, -⟩ := cepsNormal_width_properties dom hW hθ hD
    ((le_max_left dom.normalWidthThreshold (6 * dom.normalPiBound)).trans hl)
  by_cases hroots : a.βp = a.βm
  · exact a.normalG_merged_dslope_ne (dom.canonL ρW) μ q hroots
      ((CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq hmA).hasDerivAt)
      ((CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq
        (show a.βm.re < dom.c₀ by linarith [re_le_norm a.βm, dom.c₀_pos])).hasDerivAt)
      hQm (cepsNormal_actual_derivativeBudget dom hW hθ hD hμ hq hm) hM
  · have hr : cepsRootR D θ ρW μ q ≠ 0 := by
      intro hz
      apply hroots
      change cepsMorseRoot D θ ρW μ _ = cepsMorseRoot D θ ρW μ _
      rw [hz, neg_zero]
    have hΔ := cepsNormal_actual_delta_lower_bound_negative dom hW hθ hD hμ hq hl hre
    have hΔ0 : a.delta (dom.canonL ρW) μ q l ≠ 0 := norm_pos_iff.mp
      ((mul_pos (div_pos (cepsNormal_sectorConst_pos dom hW hθ hD) (by norm_num))
        (lt_min (by norm_num) (mul_pos (norm_pos_iff.mpr hr) hl0))).trans_le hΔ)
    intro hS
    change dslope (a.normalG (dom.canonL ρW) μ q l) a.βm a.βp = 0 at hS
    have hid := a.delta_mul_normalG (dom.canonL ρW) μ q (l : ℂ) hQm
    rw [hS, mul_zero] at hid
    exact (mul_ne_zero hΔ0 (a.normalG_ne (dom.canonL ρW) μ q l hQm)) hid


end PGM
