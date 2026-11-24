import PLAStochastic.Index.CEPS.Normal.ActualBridgeBound

/-! # A uniform inverse bound for the relative normal divided slope -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsNormalData

theorem norm_normalG_le_dslope_of_delta (a : CepsNormalData)
    (L : ℂ → ℂ → ℂ → ℂ) (μ q : ℂ) {l r c K : ℝ}
    (hl : 0 < l) (hr : 0 < r) (hc : 0 < c) (hK : 0 ≤ K)
    (hQm : a.Q a.βm ≠ 0)
    (hdelta : c * min 1 (r * l) ≤ ‖a.delta L μ q l‖)
    (heta : ‖a.eta‖ ≤ K * r) :
    ‖a.normalG L μ q l a.βm‖ ≤
      K / c * (r + 1 / l) * ‖dslope (a.normalG L μ q l) a.βm a.βp‖ := by
  have hm : 0 < min 1 (r * l) := lt_min (by norm_num) (mul_pos hr hl)
  have he := congrArg norm (a.delta_mul_normalG L μ q l hQm)
  simp only [norm_mul, norm_neg] at he
  have hgain := cepsNormal_rootGain_le hr.le hl
  have hmul : (c * ‖a.normalG L μ q l a.βm‖) * min 1 (r * l) ≤
      (K * (r + 1 / l) * ‖dslope (a.normalG L μ q l) a.βm a.βp‖) * min 1 (r * l) := by
    calc
      _ = (c * min 1 (r * l)) * ‖a.normalG L μ q l a.βm‖ := by ring
      _ ≤ ‖a.delta L μ q l‖ * ‖a.normalG L μ q l a.βm‖ :=
        mul_le_mul_of_nonneg_right hdelta (norm_nonneg _)
      _ = _ := he
      _ ≤ (K * r) * ‖dslope (a.normalG L μ q l) a.βm a.βp‖ :=
        mul_le_mul_of_nonneg_right heta (norm_nonneg _)
      _ ≤ (K * (min 1 (r * l) * (r + 1 / l))) *
          ‖dslope (a.normalG L μ q l) a.βm a.βp‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgain hK) (norm_nonneg _)
      _ = _ := by ring
  have hcancel := le_of_mul_le_mul_right hmul hm
  have hb := (le_div_iff₀ hc).mpr (by simpa only [mul_comm c] using hcancel)
  calc
    _ ≤ (K * (r + 1 / l) * ‖dslope (a.normalG L μ q l) a.βm a.βp‖) / c := hb
    _ = _ := by ring

end CepsNormalData

namespace CepsCanonDomain

def normalSlopeInverseBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  (8 * cepsChartK D / dom.normalSectorConst + 2) * (dom.rmax + 1)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_actual_relative_slope_inverse {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re)
    {l : ℝ} (hl : dom.normalCoarseWidth ≤ l) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l
        (cepsRootMinus D θ ρW μ q)‖ ≤
      dom.normalSlopeInverseBound *
        ‖dslope ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
          (cepsRootMinus D θ ρW μ q) (cepsRootPlus D θ ρW μ q)‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hl
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hlw
  have hwidth : 2 * dom.normalDerivativeBudget ≤ l := (le_max_right _ _).trans hl
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
      (cepsNormal_actual_delta_lower_bound dom hW hθ hD hμ hq hre hlw)
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
