import PLAStochastic.Index.CEPS.Normal.ActualDenominator
import PLAStochastic.Index.CEPS.Normal.ActualEquality
import PLAStochastic.Index.CEPS.Normal.BridgeBound
import PLAStochastic.Index.CEPS.Scaled.LadderSigns

/-! # A uniform bound for the genuine actual regular bridge

The bound is valid on the entire closed discount half-disc and retains
the inverse-width gain at merging. The constants depend only on the class.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalCoarseWidth {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  max dom.normalWidthThreshold (2 * dom.normalDerivativeBudget)

def normalBridgeBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  (8 * cepsChartK D / dom.normalSectorConst + 2) *
    v * Real.exp (2 * dom.normalLogBound)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_weight_le_of_re_nonneg {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q ζ : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hζ : ‖ζ‖ ≤ dom.c₀ / 4)
    (hre : 0 ≤ ζ.re) {l : ℝ} (hl : 0 ≤ l) :
    ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l ζ‖ ≤
      v * Real.exp (2 * dom.normalLogBound) := by
  have hw := (cepsNormal_weight_bounds dom hW hθ hD hμ hq hζ).2
  have he : ‖cexp (-ζ * (l : ℂ))‖ ≤ 1 := by
    rw [norm_exp, Real.exp_le_one_iff]
    simp only [mul_re, neg_re, ofReal_re, neg_im, ofReal_im, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hre) hl
  have hid : (cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l ζ =
      cexp (-ζ * l) *
        (cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q 0 ζ := by
    simp only [CepsNormalData.normalG, mul_zero, exp_zero, one_mul, mul_assoc]
  rw [hid, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) he).trans hw

include hW hθ hD in
/-- No off-root or off-merger assumption remains in this bridge estimate. -/
theorem cepsNormal_actual_regularBridge_bound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re)
    {l : ℝ} (hl : dom.normalCoarseWidth ≤ l) :
    ‖(cepsWHNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l‖ ≤
      dom.normalBridgeBound * (‖cepsRootR D θ ρW μ q‖ + 1 / l) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hl
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hlw
  have hwidth : 2 * dom.normalDerivativeBudget ≤ l := (le_max_right _ _).trans hl
  have hc := cepsNormal_sectorConst_pos dom hW hθ hD
  have hK := cepsChartK_pos hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  let a := cepsWHNormalData D θ ρW μ q
  let G := v * Real.exp (2 * dom.normalLogBound)
  have hG : 0 ≤ G := mul_nonneg hv.le (Real.exp_pos _).le
  have hp : ‖a.βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμ' hq
  have hm : ‖a.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have hmA : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hmA
  have hsign := (cepsRoots_re_signs dom hW hθ hD hμ hre hq).1
  have hweight := cepsNormal_weight_le_of_re_nonneg dom hW hθ hD hμ hq hp hsign hl0.le
  change ‖a.normalG (dom.canonL ρW) μ q l a.βp‖ ≤ G at hweight
  have hconst : dom.normalBridgeBound = (8 * cepsChartK D / dom.normalSectorConst + 2) * G := by
    unfold CepsCanonDomain.normalBridgeBound G
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
  · have hS := cepsNormal_actual_dslope_ne_zero dom hW hθ hD hμ hq hre hlw
    have hb := a.norm_regularBridge_le_of_delta (dom.canonL ρW) μ q hl0
      (norm_pos_iff.mpr hr) (div_pos hc (by norm_num)) (by positivity) hG hQm hS
      (cepsNormal_actual_delta_lower_bound dom hW hθ hD hμ hq hre hlw)
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
theorem cepsNormalData_canonical_regularBridge_bound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re)
    {l : ℝ} (hl : dom.normalCoarseWidth ≤ l) :
    ‖(cepsNormalData D θ ρW μ q).regularBridge (dom.canonL ρW) μ q l‖ ≤
      dom.normalBridgeBound * (‖cepsRootR D θ ρW μ q‖ + 1 / l) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have he := (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' hq
    (dom.canonL ρW) l (t := 0) (mem_ball_zero_iff.mpr (by simpa using dom.ρA_pos))).2
  rw [← he]
  exact cepsNormal_actual_regularBridge_bound dom hW hθ hD hμ hq hre hl

end PGM
