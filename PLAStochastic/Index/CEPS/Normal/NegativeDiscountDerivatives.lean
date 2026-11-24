import PLAStochastic.Index.CEPS.Normal.NegativeHolomorphy
import PLAStochastic.Index.CEPS.Normal.NegativeEntranceBound
import PLAStochastic.Index.CEPS.Normal.NegativeBridgeBound

/-! # All discount derivatives on a common width-scaled negative extension -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain
def normalDiscountRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min (dom.q₀ / 4) (dom.normalNegativeRadius / 4)
end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hD in
theorem cepsNormal_discountRadius_pos : 0 < dom.normalDiscountRadius :=
  lt_min (by linarith [dom.q₀_pos]) (by linarith [cepsNormal_negativeRadius_pos dom hD])

include hW hθ hD in
theorem cepsNormal_discount_disc_subset {l : ℝ}
    (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2)
    (hre : -(dom.normalNegativeRadius / (2 * l ^ 2)) ≤ q.re)
    {z : ℂ} (hz : z ∈ ball q (dom.normalDiscountRadius / l ^ 2)) :
    ‖z‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) ≤ z.re := by
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  have hl0 := (cepsNormal_width_properties dom hW hθ hD hlw).1
  have hl1 : 1 ≤ l := by
    have hb := (le_max_left (dom.normalDerivativeBudget + 1)
      (2 * dom.normalPiRootBound / dom.normalSectorConst)).trans hlw
    linarith [cepsNormal_budget_nonneg dom hθ hD]
  have hr := cepsNormal_discountRadius_pos dom hD
  let δ := dom.normalDiscountRadius / l ^ 2
  have hδ : δ ≤ dom.normalDiscountRadius := by
    exact div_le_self hr.le (by nlinarith)
  have hδq : δ ≤ dom.q₀ / 4 := hδ.trans (min_le_left _ _)
  have hδnegative : δ ≤ dom.normalNegativeRadius / (2 * l ^ 2) := by
    have hα : dom.normalDiscountRadius ≤ dom.normalNegativeRadius / 2 :=
      (min_le_right _ _).trans (by linarith [cepsNormal_negativeRadius_pos dom hD])
    have hh := div_le_div_of_nonneg_right hα (sq_nonneg l)
    simpa only [δ, div_div] using hh
  have hδsum : dom.normalNegativeRadius / (2 * l ^ 2) + δ ≤
      dom.normalNegativeRadius / l ^ 2 := by
    have he : dom.normalNegativeRadius / (2 * l ^ 2) =
      (dom.normalNegativeRadius / l ^ 2) / 2 := by ring
    rw [he] at hδnegative ⊢
    linarith
  have hdist : ‖z - q‖ < δ := by simpa only [mem_ball, dist_eq_norm, δ] using hz
  have hn := norm_add_le (z - q) q
  rw [sub_add_cancel] at hn
  have hrz := (neg_le_abs (z - q).re).trans (abs_re_le_norm _)
  rw [sub_re] at hrz
  exact ⟨by linarith [dom.q₀_pos], by linarith⟩

private theorem cauchy_scaled_disc {F : ℂ → ℂ} {q : ℂ} {a l M : ℝ}
    (ha : 0 < a) (hl : 0 < l) (n : ℕ)
    (hd : DifferentiableOn ℂ F (ball q (a / l ^ 2)))
    (hb : ∀ z ∈ ball q (a / l ^ 2), ‖F z‖ ≤ M) :
    ‖iteratedDeriv n F q‖ ≤ n.factorial * M * (2 / a) ^ n * l ^ (2 * n) := by
  have he := norm_iteratedDeriv_le_of_ball n (div_pos ha (sq_pos_of_pos hl)) hd hb
  refine he.trans_eq ?_
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, inv_pow, pow_mul]
  ring

include hW hθ hD in
theorem cepsNormal_actual_discount_derivative_bounds {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {t : ℂ}
    (ht : ‖t‖ ≤ dom.c₀ / 4) (htre : 0 ≤ t.re) {l : ℝ}
    (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / (2 * l ^ 2)) ≤ q.re) (n : ℕ) :
    ‖iteratedDeriv n (fun q' => (cepsWHNormalData D θ ρW μ q').regularEntrance
      (dom.canonL ρW) μ q' l t) q‖ ≤
        n.factorial * (dom.normalNegativeEntranceBound * (1 + l) ^ 2) *
          (2 / dom.normalDiscountRadius) ^ n * l ^ (2 * n) ∧
    ‖iteratedDeriv n (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge
      (dom.canonL ρW) μ q' l) q‖ ≤
        n.factorial * (dom.normalNegativeBridgeBound * (dom.rmax + 1)) *
          (2 / dom.normalDiscountRadius) ^ n * l ^ (2 * n) := by
  have hlnegative : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans hl
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  have hl0 := (cepsNormal_width_properties dom hW hθ hD hlw).1
  have hl1 : 1 ≤ l := by
    have hb := (le_max_left (dom.normalDerivativeBudget + 1)
      (2 * dom.normalPiRootBound / dom.normalSectorConst)).trans hlw
    linarith [cepsNormal_budget_nonneg dom hθ hD]
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  let S := ball q (dom.normalDiscountRadius / l ^ 2)
  have hdomain : ∀ z ∈ S, ‖z‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) ≤ z.re :=
    fun _ hz => cepsNormal_discount_disc_subset dom hW hθ hD hl hq hre hz
  have hhol : ∀ z ∈ S,
      DifferentiableAt ℂ (fun q' => (cepsWHNormalData D θ ρW μ q').regularEntrance
        (dom.canonL ρW) μ q' l t) z ∧
      DifferentiableAt ℂ (fun q' => (cepsWHNormalData D θ ρW μ q').regularBridge
        (dom.canonL ρW) μ q' l) z := fun z hz =>
    cepsNormal_actual_holomorphicAt_negative dom hW hθ hD hμ (hdomain z hz).1
      (by linarith [dom.c₀_pos]) hlnegative (hdomain z hz).2
  constructor
  · exact cauchy_scaled_disc (cepsNormal_discountRadius_pos dom hD) hl0 n
      (fun z hz => (hhol z hz).1.differentiableWithinAt)
      (fun z hz => cepsNormal_actual_regularEntrance_bound_negative dom hW hθ hD hμ
        (hdomain z hz).1.le ht htre hl (hdomain z hz).2)
  · refine cauchy_scaled_disc (cepsNormal_discountRadius_pos dom hD) hl0 n
      (fun z hz => (hhol z hz).2.differentiableWithinAt) ?_
    intro z hz
    have hb := cepsNormal_actual_regularBridge_bound_negative dom hW hθ hD hμ
      (hdomain z hz).1.le hl (hdomain z hz).2
    have hcoef : 0 ≤ dom.normalNegativeBridgeBound := by
      have := cepsChartK_pos hD
      have := cepsNormal_sectorConst_pos dom hW hθ hD
      have := CepsCanonDomain.v_pos hW hθ hD
      unfold CepsCanonDomain.normalNegativeBridgeBound CepsCanonDomain.normalBridgeBound
      positivity
    exact hb.trans (mul_le_mul_of_nonneg_left
      (add_le_add (dom.norm_cepsRootR_le hW hθ hD hμ' (hdomain z hz).1.le)
        (by rw [div_le_one hl0]; exact hl1)) hcoef)

end PGM
