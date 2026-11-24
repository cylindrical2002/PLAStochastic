import PLAStochastic.Index.CEPS.Normal.RelativeSlack
import PLAStochastic.Index.CEPS.Normal.NegativeRootSigns
import PLAStochastic.Index.CEPS.Normal.NegativeSlopeInverse
import PLAStochastic.Index.CEPS.Normal.ActualEntranceBound

/-! # A quadratic canonical entrance bound on the common negative extension -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalNegativeEntranceBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp (2 * dom.normalRootSlack) * dom.normalEntranceBound

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_actual_regularEntrance_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {t : ℂ} (ht : ‖t‖ ≤ dom.c₀ / 4) (htre : 0 ≤ t.re)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsWHNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t‖ ≤
      dom.normalNegativeEntranceBound * (1 + l) ^ 2 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlnegative : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  have hl0 := (cepsNormal_width_properties dom hW hθ hD hlw).1
  have hc := dom.c₀_pos
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  let a := cepsWHNormalData D θ ρW μ q
  let G := a.normalG (dom.canonL ρW) μ q l
  let C2 := Real.exp (2 * dom.normalRootSlack) * dom.normalSpatialSecondBound
  let S : Set ℂ := closedBall 0 (dom.c₀ / 4) ∩ {z | a.βm.re - 2 * dom.normalRootSlack / l ≤ z.re}
  have hSc : Convex ℝ S :=
    (convex_closedBall (0 : ℂ) (dom.c₀ / 4)).inter (convex_halfSpace_ge reLm.isLinear (a.βm.re - 2 * dom.normalRootSlack / l))
  have hsub : S ⊆ ball 0 (dom.c₀ / 2) := by
    intro z hz
    apply mem_ball_zero_iff.mpr
    have hn := mem_closedBall_zero_iff.mp hz.1
    linarith
  obtain ⟨hpSign, hmSign⟩ := cepsRoots_re_signs_negative dom hW hθ hD hμ hq hl0 hre
  change -dom.normalRootSlack ≤ a.βp.re * l at hpSign
  change a.βm.re * l ≤ dom.normalRootSlack at hmSign
  have hSlack : 0 ≤ dom.normalRootSlack := by
    unfold CepsCanonDomain.normalRootSlack
    exact mul_nonneg (cepsChartK_pos hD).le (Real.sqrt_nonneg _)
  have hslackid : 2 * dom.normalRootSlack / l * l = 2 * dom.normalRootSlack :=
    div_mul_cancel₀ _ hl0.ne'
  have hp : a.βp ∈ S := ⟨mem_closedBall_zero_iff.mpr (dom.norm_rootPlus_le hW hθ hD hμ' hq),
    by change a.βm.re - 2 * dom.normalRootSlack / l ≤ a.βp.re; nlinarith⟩
  have hm : a.βm ∈ S := ⟨mem_closedBall_zero_iff.mpr (dom.norm_rootMinus_le hW hθ hD hμ' hq),
    by change a.βm.re - 2 * dom.normalRootSlack / l ≤ a.βm.re
       exact sub_le_self _ (div_nonneg (by positivity) hl0.le)⟩
  have htS : t ∈ S := ⟨mem_closedBall_zero_iff.mpr ht, by
    change a.βm.re - 2 * dom.normalRootSlack / l ≤ t.re
    nlinarith [mul_nonneg htre hl0.le]⟩
  have hC2 : 0 ≤ C2 := by
    unfold C2 CepsCanonDomain.normalSpatialSecondBound CepsCanonDomain.normalWeightRatio
    positivity
  have hrel : ‖dslope (dslope G a.βm) a.βp t‖ ≤
      C2 * (1 + l) ^ 2 * ‖G a.βm‖ :=
    cepsNormal_norm_second_dslope_le
      (cepsNormalG_differentiableOn_spatial dom hW hθ hD hμ hq l) hSc hsub
      (mul_nonneg (mul_nonneg hC2 (sq_nonneg _)) (norm_nonneg _))
      (fun z hz => by
        have hsl : a.βm.re * l ≤ z.re * l + 2 * dom.normalRootSlack := by
          have hmem := hz.2
          change a.βm.re - 2 * dom.normalRootSlack / l ≤ z.re at hmem
          nlinarith [mul_nonneg (sub_nonneg.mpr hmem) hl0.le]
        simpa only [C2, mul_assoc] using! cepsNormal_relative_secondDerivative_le_slack
          dom hW hθ hD hμ hq hl0.le (mem_closedBall_zero_iff.mp hz.1) hsl) hm hp htS
  have hden := cepsNormal_actual_relative_slope_inverse_negative dom hW hθ hD hμ hq hl hre
  change ‖G a.βm‖ ≤ dom.normalSlopeInverseBound * ‖dslope G a.βm a.βp‖ at hden
  have hnum : ‖dslope (dslope G a.βm) a.βp t‖ ≤
      C2 * (1 + l) ^ 2 *
        (dom.normalSlopeInverseBound * ‖dslope G a.βm a.βp‖) :=
    hrel.trans (mul_le_mul_of_nonneg_left hden (mul_nonneg hC2 (sq_nonneg _)))
  have hS0 : dslope G a.βm a.βp ≠ 0 :=
    cepsNormal_actual_dslope_ne_zero_negative dom hW hθ hD hμ hq hlnegative hre
  have hSn : 0 < ‖dslope G a.βm a.βp‖ := norm_pos_iff.mpr hS0
  have htA : ‖t‖ < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQlo := cepsQ_norm_ge_on_rootZone dom hW hθ hD hμ' hq htA
  change cepsVarLo D / 4 ≤ ‖a.Q t‖ at hQlo
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith) hμ' (ofReal_im μ) hq
    (show ‖t‖ ≤ dom.c₀ / 2 by linarith)
  change ‖dom.canonL ρW μ q t‖ ≤ dom.normalLogBound at hL
  have hExp : ‖cexp (dom.canonL ρW μ q t)‖ ≤ Real.exp dom.normalLogBound := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr ((re_le_norm _).trans hL)
  have hCoeff : 0 ≤ dom.normalSlopeInverseBound := by
    have := cepsNormal_sectorConst_pos dom hW hθ hD
    have := cepsChartK_pos hD
    have := dom.rmax_pos
    unfold CepsCanonDomain.normalSlopeInverseBound
    positivity
  change ‖-cexp (dom.canonL ρW μ q t) * dslope (dslope G a.βm) a.βp t /
    (a.Q t * dslope G a.βm a.βp)‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_neg]
  calc
    _ ≤ (Real.exp dom.normalLogBound *
          (C2 * (1 + l) ^ 2 *
            (dom.normalSlopeInverseBound * ‖dslope G a.βm a.βp‖))) /
        ((cepsVarLo D / 4) * ‖dslope G a.βm a.βp‖) :=
      div_le_div₀ (by positivity) (mul_le_mul hExp hnum (norm_nonneg _) (Real.exp_pos _).le)
        (mul_pos (by positivity) hSn) (mul_le_mul_of_nonneg_right hQlo (norm_nonneg _))
    _ = _ := by
      unfold CepsCanonDomain.normalNegativeEntranceBound CepsCanonDomain.normalEntranceBound C2
      field_simp

include hW hθ hD in
theorem cepsNormalData_canonical_regularEntrance_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {t : ℂ} (ht : ‖t‖ ≤ dom.c₀ / 4) (htre : 0 ≤ t.re)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsNormalData D θ ρW μ q).regularEntrance (dom.canonL ρW) μ q l t‖ ≤
      dom.normalNegativeEntranceBound * (1 + l) ^ 2 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have htA : t ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  rw [← (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμ' hq (dom.canonL ρW) l htA).1]
  exact cepsNormal_actual_regularEntrance_bound_negative dom hW hθ hD hμ hq ht htre hl hre


end PGM
