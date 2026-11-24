import PLAStochastic.Index.CEPS.Normal.InverseRelativeDerivative
import PLAStochastic.Index.CEPS.Normal.NegativeRootSigns
import PLAStochastic.Index.CEPS.Normal.ActualEquality

/-! # A quadratic lower-end occupation entrance bound on the common negative extension -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain

def normalBottomEntranceBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  Real.exp (dom.normalLogBound + 2 * dom.normalRootSlack) *
    dom.normalSpatialSecondBound * dom.normalSlopeInverseBound

end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormal_actual_regularBottomEntrance_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsWHNormalData D θ ρW μ q).regularBottomEntrance (dom.canonL ρW) μ q l‖ ≤
      dom.normalBottomEntranceBound * (1 + l) ^ 2 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlnegative : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  have hl0 := (cepsNormal_width_properties dom hW hθ hD hlw).1
  have hc := dom.c₀_pos
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  let a := cepsWHNormalData D θ ρW μ q
  let G := a.normalK (dom.canonL ρW) μ q l
  let C2 := Real.exp (2 * dom.normalRootSlack) * dom.normalSpatialSecondBound
  let S : Set ℂ := closedBall 0 (dom.c₀ / 4) ∩ {z | z.re ≤ a.βp.re + 2 * dom.normalRootSlack / l}
  have hSc : Convex ℝ S :=
    (convex_closedBall (0 : ℂ) (dom.c₀ / 4)).inter (convex_halfSpace_le reLm.isLinear (a.βp.re + 2 * dom.normalRootSlack / l))
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
    by change a.βp.re ≤ a.βp.re + 2 * dom.normalRootSlack / l
       exact le_add_of_nonneg_right (div_nonneg (by positivity) hl0.le)⟩
  have hm : a.βm ∈ S := ⟨mem_closedBall_zero_iff.mpr (dom.norm_rootMinus_le hW hθ hD hμ' hq),
    by change a.βm.re ≤ a.βp.re + 2 * dom.normalRootSlack / l; nlinarith⟩
  have htS : (0 : ℂ) ∈ S := ⟨mem_closedBall_zero_iff.mpr (by simp; positivity), by
    change (0 : ℝ) ≤ a.βp.re + 2 * dom.normalRootSlack / l
    nlinarith⟩
  have hC2 : 0 ≤ C2 := by
    unfold C2 CepsCanonDomain.normalSpatialSecondBound CepsCanonDomain.normalWeightRatio
    positivity
  have hrel : ‖dslope (dslope G a.βm) a.βp 0‖ ≤
      C2 * (1 + l) ^ 2 * ‖G a.βp‖ :=
    cepsNormal_norm_second_dslope_le
      (cepsNormalK_differentiableOn_spatial dom hW hθ hD hμ hq l) hSc hsub
      (mul_nonneg (mul_nonneg hC2 (sq_nonneg _)) (norm_nonneg _))
      (fun z hz => by
        have hsl : z.re * l ≤ a.βp.re * l + 2 * dom.normalRootSlack := by
          have hmem := hz.2
          change z.re ≤ a.βp.re + 2 * dom.normalRootSlack / l at hmem
          nlinarith [mul_nonneg (sub_nonneg.mpr hmem) hl0.le]
        simpa only [C2, mul_assoc] using! cepsNormal_inverse_relative_secondDerivative_le_slack
          dom hW hθ hD hμ hq hl0.le (mem_closedBall_zero_iff.mp hz.1) hsl) hm hp htS
  have hden := cepsNormal_inverse_relative_slope_inverse_negative dom hW hθ hD hμ hq hl hre
  change ‖G a.βp‖ ≤ dom.normalSlopeInverseBound * ‖dslope G a.βm a.βp‖ at hden
  have hnum : ‖dslope (dslope G a.βm) a.βp 0‖ ≤
      C2 * (1 + l) ^ 2 *
        (dom.normalSlopeInverseBound * ‖dslope G a.βm a.βp‖) :=
    hrel.trans (mul_le_mul_of_nonneg_left hden (mul_nonneg hC2 (sq_nonneg _)))
  have hSm : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have hn : ‖a.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hSp : a.βp ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have hn : ‖a.βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμ' hq
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hSm
  have hQp := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hSp
  have hs := a.normalK_dslope (dom.canonL ρW) μ q l
    ((cepsNormalG_differentiableOn_spatial dom hW hθ hD hμ hq l).differentiableAt
      (isOpen_ball.mem_nhds (hsub hm))) hQm hQp
  have hS0 : dslope G a.βm a.βp ≠ 0 := by
    rw [hs]
    exact div_ne_zero (neg_ne_zero.mpr
      (cepsNormal_actual_dslope_ne_zero_negative dom hW hθ hD hμ hq hlnegative hre))
      (mul_ne_zero (a.normalG_ne (dom.canonL ρW) μ q l hQm)
        (a.normalG_ne (dom.canonL ρW) μ q l hQp))
  have hSn : 0 < ‖dslope G a.βm a.βp‖ := norm_pos_iff.mpr hS0
  have hL := dom.norm_cepsCanonL_le hW hθ hD (γ := 1) (by norm_num) le_rfl
    (c := dom.c₀) le_rfl (by linarith) hμ' (ofReal_im μ) hq
    (show ‖(0 : ℂ)‖ ≤ dom.c₀ / 2 by simp; positivity)
  change ‖dom.canonL ρW μ q 0‖ ≤ dom.normalLogBound at hL
  have hExp : ‖cexp (-dom.canonL ρW μ q 0)‖ ≤ Real.exp dom.normalLogBound := by
    rw [norm_exp, neg_re]
    exact Real.exp_le_exp.mpr
      ((neg_le_abs _).trans ((abs_re_le_norm _).trans hL))
  have hCoeff : 0 ≤ dom.normalSlopeInverseBound := by
    have := cepsNormal_sectorConst_pos dom hW hθ hD
    have := cepsChartK_pos hD
    have := dom.rmax_pos
    unfold CepsCanonDomain.normalSlopeInverseBound
    positivity
  change ‖cexp (-dom.canonL ρW μ q 0) * dslope (dslope G a.βm) a.βp 0 /
    dslope G a.βm a.βp‖ ≤ _
  rw [norm_div, norm_mul]
  calc
    _ ≤ (Real.exp dom.normalLogBound *
          (C2 * (1 + l) ^ 2 *
            (dom.normalSlopeInverseBound * ‖dslope G a.βm a.βp‖))) /
        ‖dslope G a.βm a.βp‖ :=
      div_le_div_of_nonneg_right
        (mul_le_mul hExp hnum (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
    _ = _ := by
      unfold CepsCanonDomain.normalBottomEntranceBound C2
      rw [Real.exp_add]
      field_simp

include hW hθ hD in
theorem cepsNormal_actual_regularBottomEntrance_eq {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) (L : ℂ → ℂ → ℂ → ℂ) (l : ℂ) :
    (cepsWHNormalData D θ ρW μ q).regularBottomEntrance L μ q l =
      (cepsNormalData D θ ρW μ q).regularBottomEntrance L μ q l := by
  let bp := cepsRootPlus D θ ρW μ q
  let bm := cepsRootMinus D θ ρW μ q
  let G := (cepsWHNormalData D θ ρW μ q).normalK L μ q l
  let H := (cepsNormalData D θ ρW μ q).normalK L μ q l
  have hp : bp ∈ ball (0 : ℂ) dom.ρA := CepsC6.ball_c₀_subset dom
    (CepsC6.rootPlus_mem_ball dom hW hθ hD hμ hq)
  have hm : bm ∈ ball (0 : ℂ) dom.ρA := CepsC6.ball_c₀_subset dom
    (CepsC6.rootMinus_mem_ball dom hW hθ hD hμ hq)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) dom.ρA := by simpa using dom.ρA_pos
  have hGH : EqOn G H (ball 0 dom.ρA) := by
    intro z hz
    change (cexp (-z * l) * cepsQ D θ ρW μ q z * cexp (-2 * L μ q z))⁻¹ =
      (cexp (-z * l) * cepsQuotA D θ ρW μ q z * cexp (-2 * L μ q z))⁻¹
    rw [CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμ hq hz]
  have hS := cepsNormal_dslope_eqOn_of_eqOn isOpen_ball hGH hm
  have hN := cepsNormal_dslope_eqOn_of_eqOn isOpen_ball hS hp
  change cexp (-L μ q 0) * dslope (dslope G bm) bp 0 / dslope G bm bp =
    cexp (-L μ q 0) * dslope (dslope H bm) bp 0 / dslope H bm bp
  rw [hN h0, hS hp]

include hW hθ hD in
theorem cepsNormalData_canonical_regularBottomEntrance_bound_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsNormalData D θ ρW μ q).regularBottomEntrance (dom.canonL ρW) μ q l‖ ≤
      dom.normalBottomEntranceBound * (1 + l) ^ 2 := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  rw [← cepsNormal_actual_regularBottomEntrance_eq dom hW hθ hD hμ' hq (dom.canonL ρW) l]
  exact cepsNormal_actual_regularBottomEntrance_bound_negative dom hW hθ hD hμ hq hl hre

end PGM
