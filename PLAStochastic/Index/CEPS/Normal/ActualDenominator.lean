import PLAStochastic.Index.CEPS.Normal.ActualPiBounds
import PLAStochastic.Index.CEPS.Normal.ActualRootSector
import PLAStochastic.Index.CEPS.Normal.DenominatorBound

/-! # The actual canonical normal denominator on the closed discount half-disc

Both the root sector and the factor budget are discharged. The quantitative
Delta estimate retains the root-merging factor; at merging the divided
slope is shown nonzero using the actual logarithmic derivative budget.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalSectorConst {D θ v : ℝ} (_dom : CepsCanonDomain D θ v) : ℝ :=
  min 1 (1 / (2 * Real.sqrt v))

def normalPiRootBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  2 * cepsChartK D * dom.normalPiBound

def normalWidthThreshold {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  max (dom.normalDerivativeBudget + 1) (2 * dom.normalPiRootBound / dom.normalSectorConst)

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_sectorConst_pos : 0 < dom.normalSectorConst := by
  have hv : 0 < Real.sqrt v := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
  exact lt_min (by norm_num) (by positivity)

include hW hθ hD in
theorem cepsNormal_piRootBound_nonneg : 0 ≤ dom.normalPiRootBound := by
  have hM := cepsNormal_budget_nonneg dom hθ hD
  have hvl := cepsVarLo_pos hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hK := cepsChartK_pos hD
  unfold CepsCanonDomain.normalPiRootBound CepsCanonDomain.normalPiBound
  positivity

include hW hθ hD in
theorem cepsNormal_width_properties {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    0 < l ∧ dom.normalDerivativeBudget < l ∧
      2 * dom.normalPiRootBound ≤ dom.normalSectorConst * l := by
  have h1 := (le_max_left (dom.normalDerivativeBudget + 1)
    (2 * dom.normalPiRootBound / dom.normalSectorConst)).trans hl
  have h2 := (le_max_right (dom.normalDerivativeBudget + 1)
    (2 * dom.normalPiRootBound / dom.normalSectorConst)).trans hl
  have hM := cepsNormal_budget_nonneg dom hθ hD
  rw [div_le_iff₀ (cepsNormal_sectorConst_pos dom hW hθ hD)] at h2
  exact ⟨by linarith, by linarith, by nlinarith⟩

include hW hθ hD in
/-- The full closed-half-disc quantitative estimate, including the merger. -/
theorem cepsNormal_actual_delta_lower_bound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re)
    {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    dom.normalSectorConst / 4 * min 1 (‖cepsRootR D θ ρW μ q‖ * l) ≤
      ‖(cepsWHNormalData D θ ρW μ q).delta (dom.canonL ρW) μ q l‖ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨hl0, -, hwidth⟩ := cepsNormal_width_properties dom hW hθ hD hl
  have hsector := cepsRoots_difference_re_ge hW hθ hD dom hμ hq hre
  have hsector' : dom.normalSectorConst * ‖cepsRootR D θ ρW μ q‖ ≤
      (cepsWHNormalData D θ ρW μ q).eta.re := by
    calc
      _ ≤ (1 / (2 * Real.sqrt v)) * ‖cepsRootR D θ ρW μ q‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ = ‖cepsRootR D θ ρW μ q‖ / (2 * Real.sqrt v) := by ring
      _ ≤ _ := hsector
  have hfactor := cepsNormal_actual_pi_sub_one_le dom hW hθ hD hμ hq
  have hPi : 0 ≤ dom.normalPiBound := by
    have := cepsNormal_budget_nonneg dom hθ hD
    have := cepsVarLo_pos hD
    have := CepsCanonDomain.v_pos hW hθ hD
    unfold CepsCanonDomain.normalPiBound
    positivity
  have hfactor' : ‖(cepsWHNormalData D θ ρW μ q).pi (dom.canonL ρW) μ q - 1‖ ≤
      dom.normalPiRootBound * ‖cepsRootR D θ ρW μ q‖ := by
    calc
      _ ≤ _ := hfactor
      _ ≤ dom.normalPiBound * (2 * cepsChartK D * ‖cepsRootR D θ ρW μ q‖) :=
        mul_le_mul_of_nonneg_left (cepsRoots_difference_norm_le hW hθ hD dom hμ' hq) hPi
      _ = _ := by unfold CepsCanonDomain.normalPiRootBound; ring
  exact cepsNormal_delta_lower_bound hl0.le (norm_nonneg _)
    (cepsNormal_sectorConst_pos dom hW hθ hD) (min_le_left _ _)
    (cepsNormal_piRootBound_nonneg dom hW hθ hD) hsector' hfactor' hwidth

include hW hθ hD in
/-- The genuine divided-slope denominator is nonzero at every point of the half-disc. -/
theorem cepsNormal_actual_dslope_ne_zero {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (hre : 0 ≤ q.re)
    {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    dslope ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
      (cepsRootMinus D θ ρW μ q) (cepsRootPlus D θ ρW μ q) ≠ 0 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  let a := cepsWHNormalData D θ ρW μ q
  have hm := dom.norm_rootMinus_le hW hθ hD hμ' hq
  change ‖a.βm‖ ≤ dom.c₀ / 4 at hm
  have hmA : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hmA
  obtain ⟨hl0, hM, -⟩ := cepsNormal_width_properties dom hW hθ hD hl
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
    have hΔ := cepsNormal_actual_delta_lower_bound dom hW hθ hD hμ hq hre hl
    have hΔ0 : a.delta (dom.canonL ρW) μ q l ≠ 0 := norm_pos_iff.mp
      ((mul_pos (div_pos (cepsNormal_sectorConst_pos dom hW hθ hD) (by norm_num))
        (lt_min (by norm_num) (mul_pos (norm_pos_iff.mpr hr) hl0))).trans_le hΔ)
    intro hS
    change dslope (a.normalG (dom.canonL ρW) μ q l) a.βm a.βp = 0 at hS
    have hid := a.delta_mul_normalG (dom.canonL ρW) μ q (l : ℂ) hQm
    rw [hS, mul_zero] at hid
    exact (mul_ne_zero hΔ0 (a.normalG_ne (dom.canonL ρW) μ q l hQm)) hid

end PGM
