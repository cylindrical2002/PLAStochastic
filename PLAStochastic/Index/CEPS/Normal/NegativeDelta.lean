import PLAStochastic.Index.CEPS.Normal.ExtendedRootSector
import PLAStochastic.Index.CEPS.Normal.SmallComplexDelta
import PLAStochastic.Index.CEPS.Normal.ActualDenominator

/-! # A common width-scaled negative-real extension of the actual denominator -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalSmallRootScale {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  min 1 (1 / (8 * cepsChartK D))

def normalNegativeRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  dom.normalSmallRootScale ^ 2 / 2

def normalNegativeWidth {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  max dom.normalWidthThreshold (6 * dom.normalPiBound)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem cepsNormal_negativeRadius_pos : 0 < dom.normalNegativeRadius := by
  have hK := cepsChartK_pos hD
  have hs : 0 < dom.normalSmallRootScale := lt_min (by norm_num) (by positivity)
  exact div_pos (sq_pos_of_pos hs) (by norm_num)

include hW hθ hD in
theorem cepsNormal_actual_delta_lower_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    dom.normalSectorConst / 4 * min 1 (‖cepsRootR D θ ρW μ q‖ * l) ≤
      ‖(cepsWHNormalData D θ ρW μ q).delta (dom.canonL ρW) μ q l‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlbase := (le_max_left dom.normalWidthThreshold (6 * dom.normalPiBound)).trans hl
  obtain ⟨hl0, -, hwidth⟩ := cepsNormal_width_properties dom hW hθ hD hlbase
  let R := ‖cepsRootR D θ ρW μ q‖
  let a := cepsWHNormalData D θ ρW μ q
  let ε := dom.normalSmallRootScale
  have hK := cepsChartK_pos hD
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hPi := cepsNormal_actual_pi_sub_one_le dom hW hθ hD hμ hq
  by_cases hsmall : R * l ≤ ε
  · have hηsmall : ‖a.eta‖ * l ≤ 1 / 4 := by
      have hb := mul_le_mul_of_nonneg_right
        (cepsRoots_difference_norm_le hW hθ hD dom hμ' hq) hl0.le
      change ‖a.eta‖ * l ≤ 2 * cepsChartK D * R * l at hb
      have hc : 2 * cepsChartK D * ε ≤ 1 / 4 := by
        have hs : ε ≤ 1 / (8 * cepsChartK D) := min_le_right _ _
        rw [le_div_iff₀ (by positivity)] at hs
        linarith
      change ‖a.eta‖ * l ≤ 1 / 4
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * cepsChartK D)
        (sub_nonneg.mpr hsmall)]
    have hw : 6 * dom.normalPiBound ≤ l :=
      (le_max_right dom.normalWidthThreshold (6 * dom.normalPiBound)).trans hl
    have hd := cepsNormal_delta_lower_bound_small hl0.le hηsmall hPi hw
    have hnorm := cepsRoots_difference_norm_ge hW hθ hD dom hμ' hq
    have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
    have hc : dom.normalSectorConst * R ≤ ‖a.eta‖ := by
      calc
        _ ≤ (1 / (2 * Real.sqrt v)) * R :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ ≤ R / Real.sqrt v := by
          rw [div_mul_eq_mul_div, one_mul]
          exact div_le_div_of_nonneg_left (norm_nonneg _) hv (by linarith)
        _ ≤ _ := hnorm
    have hcpos := (cepsNormal_sectorConst_pos dom hW hθ hD).le
    have hm : dom.normalSectorConst * min 1 (R * l) ≤ ‖a.eta‖ * l := by
      calc
        _ ≤ dom.normalSectorConst * (R * l) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hcpos
        _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) hl0.le]
    change dom.normalSectorConst / 4 * min 1 (R * l) ≤ ‖a.delta (dom.canonL ρW) μ q l‖
    change ‖a.eta‖ * l / 2 ≤ ‖a.delta (dom.canonL ρW) μ q l‖ at hd
    nlinarith [mul_nonneg (norm_nonneg a.eta) hl0.le]
  · have hbig : ε ≤ R * l := (lt_of_not_ge hsmall).le
    have hrl0 : 0 ≤ R * l := mul_nonneg (norm_nonneg _) hl0.le
    have hsquare : ε ^ 2 ≤ R ^ 2 * l ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hbig) (by linarith : 0 ≤ R * l + ε)]
    have hrad : dom.normalNegativeRadius / l ^ 2 ≤ R ^ 2 / 2 := by
      rw [div_le_iff₀ (sq_pos_of_pos hl0)]
      change ε ^ 2 / 2 ≤ R ^ 2 / 2 * l ^ 2
      nlinarith
    have hn : R ^ 2 = ‖q - cepsMorseMin D θ ρW μ‖ := by
      change ‖Complex.sqrt (q - cepsMorseMin D θ ρW μ)‖ ^ 2 = _
      rw [← norm_pow, sqrt_sq_eq]
    have hz : -‖q - cepsMorseMin D θ ρW μ‖ / 2 ≤
        (q - cepsMorseMin D θ ρW μ).re := by
      rw [← hn, sub_re]
      linarith [re_cepsMorseMin_nonpos hW hθ hD (dom.μ_lt_chart hμ')]
    have hrsector := sqrt_re_ge_half_norm_of_re_ge hz
    have hsector := cepsRoots_difference_re_ge_of_rootR_sector hW hθ hD dom hμ' hq hrsector
    have hsector' : dom.normalSectorConst * R ≤ a.eta.re := by
      calc
        _ ≤ (1 / (2 * Real.sqrt v)) * R :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ = R / (2 * Real.sqrt v) := by ring
        _ ≤ _ := hsector
    have hPib := cepsNormal_piRootBound_nonneg dom hW hθ hD
    have hfactor : ‖a.pi (dom.canonL ρW) μ q - 1‖ ≤ dom.normalPiRootBound * R := by
      have hC : 0 ≤ dom.normalPiBound := by
        have := cepsNormal_budget_nonneg dom hθ hD
        have := cepsVarLo_pos hD
        have := CepsCanonDomain.v_pos hW hθ hD
        unfold CepsCanonDomain.normalPiBound
        positivity
      calc
        _ ≤ _ := hPi
        _ ≤ dom.normalPiBound * (2 * cepsChartK D * R) :=
          mul_le_mul_of_nonneg_left (cepsRoots_difference_norm_le hW hθ hD dom hμ' hq) hC
        _ = _ := by unfold CepsCanonDomain.normalPiRootBound; ring
    exact cepsNormal_delta_lower_bound hl0.le (norm_nonneg _)
      (cepsNormal_sectorConst_pos dom hW hθ hD) (min_le_left _ _) hPib
      hsector' hfactor hwidth

end PGM
