import PLAStochastic.Index.CEPS.Normal.NegativeDenominator
import PLAStochastic.Index.CEPS.Normal.SlopeInverseBound

/-! # The relative divided-slope inverse on the common negative-real extension -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_actual_relative_slope_inverse_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l
        (cepsRootMinus D θ ρW μ q)‖ ≤
      dom.normalSlopeInverseBound *
        ‖dslope ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
          (cepsRootMinus D θ ρW μ q) (cepsRootPlus D θ ρW μ q)‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlnegative : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hlw
  have hwidth : 2 * dom.normalDerivativeBudget ≤ l := (le_max_right _ _).trans hlcoarse
  have hM := cepsNormal_budget_nonneg dom hθ hD
  have hl1 : 1 ≤ l := by
    have hbase := (le_max_left (dom.normalDerivativeBudget + 1)
      (2 * dom.normalPiRootBound / dom.normalSectorConst)).trans hlw
    linarith
  have hc := cepsNormal_sectorConst_pos dom hW hθ hD
  have hK := cepsChartK_pos hD
  have hrmax := dom.rmax_pos
  have hcoef : 0 ≤ 8 * cepsChartK D / dom.normalSectorConst := by positivity
  let a := cepsWHNormalData D θ ρW μ q
  have hm : ‖a.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have hmA : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hmA
  by_cases hr : cepsRootR D θ ρW μ q = 0
  · have hroots : a.βp = a.βm := by
      change cepsMorseRoot D θ ρW μ _ = cepsMorseRoot D θ ρW μ _
      rw [hr, neg_zero]
    have hd := a.normalG_deriv_lower (dom.canonL ρW) μ q
      ((CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq hmA).hasDerivAt)
      ((CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq
        (show a.βm.re < dom.c₀ by linarith [re_le_norm a.βm, dom.c₀_pos])).hasDerivAt)
      hQm (cepsNormal_actual_derivativeBudget dom hW hθ hD hμ hq hm)
      (cepsNormal_width_properties dom hW hθ hD hlw).2.1
    change ‖a.normalG (dom.canonL ρW) μ q l a.βm‖ ≤
      dom.normalSlopeInverseBound * ‖dslope (a.normalG (dom.canonL ρW) μ q l) a.βm a.βp‖
    rw [hroots, dslope_same]
    have hb : ‖a.normalG (dom.canonL ρW) μ q l a.βm‖ ≤
        2 * ‖deriv (a.normalG (dom.canonL ρW) μ q l) a.βm‖ := by
      have hn := norm_nonneg (a.normalG (dom.canonL ρW) μ q l a.βm)
      nlinarith
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    unfold CepsCanonDomain.normalSlopeInverseBound
    nlinarith
  · have hb := a.norm_normalG_le_dslope_of_delta (dom.canonL ρW) μ q hl0
      (norm_pos_iff.mpr hr) (div_pos hc (by norm_num)) (by positivity) hQm
      (cepsNormal_actual_delta_lower_bound_negative dom hW hθ hD hμ hq hlnegative hre)
      (cepsRoots_difference_norm_le hW hθ hD dom hμ' hq)
    change ‖a.normalG (dom.canonL ρW) μ q l a.βm‖ ≤ _
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have hrbound := dom.norm_cepsRootR_le hW hθ hD hμ' hq
    have hinv : 1 / l ≤ 1 := by rw [div_le_one hl0]; exact hl1
    have hscale : ‖cepsRootR D θ ρW μ q‖ + 1 / l ≤ dom.rmax + 1 := add_le_add hrbound hinv
    have hcoefe : (2 * cepsChartK D) / (dom.normalSectorConst / 4) =
        8 * cepsChartK D / dom.normalSectorConst := by ring
    rw [hcoefe]
    calc
      _ ≤ (8 * cepsChartK D / dom.normalSectorConst) * (dom.rmax + 1) :=
        mul_le_mul_of_nonneg_left hscale hcoef
      _ ≤ _ := by unfold CepsCanonDomain.normalSlopeInverseBound; nlinarith


end PGM
