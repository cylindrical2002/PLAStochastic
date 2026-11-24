import PLAStochastic.Index.CEPS.Normal.NegativeRootSigns
import PLAStochastic.Index.CEPS.Normal.NegativeDenominator
import PLAStochastic.Index.CEPS.Normal.RelativeWeight
import PLAStochastic.Index.CEPS.Normal.ActualBridgeBound

/-! # A canonical bridge bound on the common negative-real extension -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalNegativeBridgeBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp dom.normalRootSlack * dom.normalBridgeBound

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_weight_le_of_re_slack {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4)
    {l C : ℝ} (hre : -C ≤ ζ.re * l) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l ζ‖ ≤
      Real.exp C * (v * Real.exp (2 * dom.normalLogBound)) := by
  rw [CepsNormalData.norm_normalG_real_width]
  exact mul_le_mul (Real.exp_le_exp.mpr (by linarith))
    (cepsNormal_weight_bounds dom hW hθ hD hμ hq hζ).2
    (norm_nonneg _) (Real.exp_pos _).le

include hW hθ hD in
/-- No off-root or off-merger assumption remains in this bridge estimate. -/
theorem cepsNormal_actual_regularBridge_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l‖ ≤
      dom.normalNegativeBridgeBound * (‖cepsRootR D θ ρW μ q‖ + 1 / l) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlnegative : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hlw
  have hwidth : 2 * dom.normalDerivativeBudget ≤ l := (le_max_right _ _).trans hlcoarse
  have hc := cepsNormal_sectorConst_pos dom hW hθ hD
  have hK := cepsChartK_pos hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  let a := cepsWHNormalData D θ ρW μ q
  let G := Real.exp dom.normalRootSlack * (v * Real.exp (2 * dom.normalLogBound))
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hp : ‖a.βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμ' hq
  have hm : ‖a.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have hmA : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hmA
  have hsign := (cepsRoots_re_signs_negative dom hW hθ hD hμ hq hl0 hre).1
  have hweight := cepsNormal_weight_le_of_re_slack dom hW hθ hD hμ hq hp hsign
  change ‖a.normalG (dom.canonL ρW) μ q l a.βp‖ ≤ G at hweight
  have hconst : dom.normalNegativeBridgeBound = (8 * cepsChartK D / dom.normalSectorConst + 2) * G := by
    unfold CepsCanonDomain.normalNegativeBridgeBound CepsCanonDomain.normalBridgeBound G
    ring
  by_cases hr : cepsRootR D θ ρW μ q = 0
  · have hroots : a.βp = a.βm := by
      change cepsMorseRoot D θ ρW μ _ = cepsMorseRoot D θ ρW μ _
      rw [hr, neg_zero]
    rw [hroots] at hweight
    have hb := a.norm_regularBridge_merged_le (dom.canonL ρW) μ q hl0 hwidth hroots
      ((CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq hmA).hasDerivAt)
      ((CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq
        (show a.βm.re < dom.c₀ by linarith [re_le_norm a.βm, dom.c₀_pos])).hasDerivAt)
      hQm (cepsNormal_actual_derivativeBudget dom hW hθ hD hμ hq hm) hweight
    change ‖a.regularBridge (dom.canonL ρW) μ q l‖ ≤ _
    refine hb.trans ?_
    rw [hr, norm_zero, zero_add, hconst]
    have hKG : 0 ≤ 8 * cepsChartK D / dom.normalSectorConst * G := by positivity
    calc
      2 * G / l = 2 * G * (1 / l) := by ring
      _ ≤ ((8 * cepsChartK D / dom.normalSectorConst) * G + 2 * G) * (1 / l) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hKG) (by positivity)
      _ = _ := by ring
  · have hS := cepsNormal_actual_dslope_ne_zero_negative dom hW hθ hD hμ hq hlnegative hre
    have hb := a.norm_regularBridge_le_of_delta (dom.canonL ρW) μ q hl0
      (norm_pos_iff.mpr hr) (div_pos hc (by norm_num)) (by positivity) hG hQm hS
      (cepsNormal_actual_delta_lower_bound_negative dom hW hθ hD hμ hq hlnegative hre)
      (cepsRoots_difference_norm_le hW hθ hD dom hμ' hq) hweight
    change ‖a.regularBridge (dom.canonL ρW) μ q l‖ ≤ _
    refine hb.trans ?_
    have hcoef : (2 * cepsChartK D) * G / (dom.normalSectorConst / 4) =
        8 * cepsChartK D / dom.normalSectorConst * G := by ring
    rw [hcoef, hconst]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    nlinarith

include hW hθ hD in
/-- The same estimate for the original root-zone normal data. -/
theorem cepsNormalData_canonical_regularBridge_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l‖ ≤
      dom.normalNegativeBridgeBound * (‖cepsRootR D θ ρW μ q‖ + 1 / l) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have he := (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' hq
    (dom.canonL ρW) l (t := 0) (mem_ball_zero_iff.mpr (by simpa using dom.ρA_pos))).2
  rw [← he]
  exact cepsNormal_actual_regularBridge_bound_negative dom hW hθ hD hμ hq hl hre


end PGM
