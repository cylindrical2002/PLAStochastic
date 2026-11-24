import PLAStochastic.Index.CEPS.Normal.InverseRelativeWeight
import PLAStochastic.Index.CEPS.Normal.NegativeSlopeInverse

/-! # Paid reciprocal weight derivatives and the relative denominator inverse -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalK_differentiableOn_spatial {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (l : ℂ) :
    DifferentiableOn ℂ ((cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l)
      (ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  refine (cepsNormalG_differentiableOn_spatial dom hW hθ hD hμ hq l).inv ?_
  intro z hz
  have hzA : z ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := mem_ball_zero_iff.mp hz; have := dom.c₀_le; have := dom.ρA_pos; linarith)
  exact (cepsWHNormalData D θ ρW μ q).normalG_ne (dom.canonL ρW) μ q l
    (CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hzA)

include hW hθ hD in
theorem cepsNormal_inverse_relative_secondDerivative_le_slack {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 ≤ l)
    {w : ℂ} (hw : ‖w‖ ≤ dom.c₀ / 4)
    {C : ℝ} (hre : w.re * l ≤ (cepsRootPlus D θ ρW μ q).re * l + C) :
    ‖deriv (deriv ((cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l)) w‖ ≤
      Real.exp C * dom.normalSpatialSecondBound * (1 + l) ^ 2 *
        ‖(cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l
          (cepsRootPlus D θ ρW μ q)‖ := by
  let δ := dom.c₀ / (8 * (1 + l))
  have hc := dom.c₀_pos
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδle : δ ≤ dom.c₀ / 8 := by
    dsimp [δ]
    apply div_le_div_of_nonneg_left hc.le (by norm_num)
    linarith
  have hsub : ball w δ ⊆ ball (0 : ℂ) (dom.c₀ / 2) := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    apply mem_ball_zero_iff.mpr
    have hn := norm_add_le (z - w) w
    rw [sub_add_cancel] at hn
    linarith
  have hd := norm_iteratedDeriv_le_of_ball 2 hδ
    ((cepsNormalK_differentiableOn_spatial dom hW hθ hD hμ hq l).mono hsub)
    (fun z hz => cepsNormal_inverse_relative_weight_on_ball_slack dom hW hθ hD hμ hq hl hw hre hz)
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hd
  refine hd.trans_eq ?_
  simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one]
  unfold CepsCanonDomain.normalSpatialSecondBound δ
  field_simp
  ring

include hW hθ hD in
theorem cepsNormal_inverse_relative_slope_inverse_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    {l : ℝ} (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    ‖(cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l
        (cepsRootPlus D θ ρW μ q)‖ ≤
      dom.normalSlopeInverseBound *
        ‖dslope ((cepsWHNormalData D θ ρW μ q).normalK (dom.canonL ρW) μ q l)
          (cepsRootMinus D θ ρW μ q) (cepsRootPlus D θ ρW μ q)‖ := by
  let a := cepsWHNormalData D θ ρW μ q
  let G := a.normalG (dom.canonL ρW) μ q l
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hm : a.βm ∈ ball (0 : ℂ) (dom.c₀ / 2) := mem_ball_zero_iff.mpr (by
    have hn : ‖a.βm‖ ≤ dom.c₀ / 4 := dom.norm_rootMinus_le hW hθ hD hμ' hq
    linarith [dom.c₀_pos])
  have hmA : a.βm ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have := mem_ball_zero_iff.mp hm; have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hpA : a.βp ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
    have hn : ‖a.βp‖ ≤ dom.c₀ / 4 := dom.norm_rootPlus_le hW hθ hD hμ' hq
    have := dom.c₀_le; have := dom.ρA_pos; linarith)
  have hQm : a.Q a.βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hmA
  have hQp : a.Q a.βp ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμ' hq hpA
  have hgm : 0 < ‖G a.βm‖ := norm_pos_iff.mpr (a.normalG_ne (dom.canonL ρW) μ q l hQm)
  have hgp : 0 < ‖G a.βp‖ := norm_pos_iff.mpr (a.normalG_ne (dom.canonL ρW) μ q l hQp)
  have hden := cepsNormal_actual_relative_slope_inverse_negative dom hW hθ hD hμ hq hl hre
  have hs := a.normalK_dslope (dom.canonL ρW) μ q l
    ((cepsNormalG_differentiableOn_spatial dom hW hθ hD hμ hq l).differentiableAt
      (isOpen_ball.mem_nhds hm)) hQm hQp
  change ‖a.normalK (dom.canonL ρW) μ q l a.βp‖ ≤
    dom.normalSlopeInverseBound * ‖dslope (a.normalK (dom.canonL ρW) μ q l) a.βm a.βp‖
  rw [hs, CepsNormalData.normalK, norm_inv, norm_div, norm_neg, norm_mul, ← mul_div_assoc]
  apply (le_div_iff₀ (mul_pos hgm hgp)).mpr
  have he : ‖G a.βp‖⁻¹ * (‖G a.βm‖ * ‖G a.βp‖) = ‖G a.βm‖ := by
    field_simp
  change ‖G a.βp‖⁻¹ * (‖G a.βm‖ * ‖G a.βp‖) ≤ _
  rw [he]
  exact hden

end PGM
