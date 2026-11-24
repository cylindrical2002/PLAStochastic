import PLAStochastic.Index.CEPS.Normal.BottomNegativeHolomorphy
import PLAStochastic.Index.CEPS.Normal.ActualBottomBound
import PLAStochastic.Index.CEPS.Normal.NegativeDiscountDerivatives

/-! # Original lower-end normal entrance: common negative extension and all discount derivatives -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalData_canonical_bottom_differentiableAt_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ < dom.q₀) {l : ℝ} (hl : dom.normalNegativeWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    DifferentiableAt ℂ (fun q' => (cepsNormalData D θ ρW μ q').regularBottomEntrance
      (dom.canonL ρW) μ q' l) q := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hqn : ∀ᶠ q' : ℂ in 𝓝 q, ‖q'‖ < dom.q₀ :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hq
  have he : (fun q' => (cepsNormalData D θ ρW μ q').regularBottomEntrance
      (dom.canonL ρW) μ q' l) =ᶠ[𝓝 q]
      (fun q' => (cepsWHNormalData D θ ρW μ q').regularBottomEntrance
        (dom.canonL ρW) μ q' l) := by
    filter_upwards [hqn] with q' hq'
    exact (cepsNormal_actual_regularBottomEntrance_eq dom hW hθ hD hμ' hq'.le
      (dom.canonL ρW) l).symm
  exact (cepsNormal_actual_bottom_holomorphicAt_negative dom hW hθ hD hμ hq hl hre).congr_of_eventuallyEq he

include hW hθ hD in
theorem cepsNormalData_canonical_bottom_analyticOnNhd_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {l : ℝ} (hl : dom.normalNegativeWidth ≤ l) :
    AnalyticOnNhd ℂ (fun q' => (cepsNormalData D θ ρW μ q').regularBottomEntrance
      (dom.canonL ρW) μ q' l)
        {q : ℂ | ‖q‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) < q.re} := by
  have hU : IsOpen {q : ℂ | ‖q‖ < dom.q₀ ∧
      -(dom.normalNegativeRadius / l ^ 2) < q.re} :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const continuous_re)
  exact (show DifferentiableOn ℂ (fun q' =>
      (cepsNormalData D θ ρW μ q').regularBottomEntrance (dom.canonL ρW) μ q' l)
      {q : ℂ | ‖q‖ < dom.q₀ ∧ -(dom.normalNegativeRadius / l ^ 2) < q.re} from
    fun q hq => (cepsNormalData_canonical_bottom_differentiableAt_negative dom hW hθ hD hμ
      hq.1 hl hq.2.le).differentiableWithinAt).analyticOnNhd hU

include hW hθ hD in
theorem cepsNormalData_canonical_bottom_discount_derivative_bound {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀ / 2) {l : ℝ}
    (hl : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l)
    (hre : -(dom.normalNegativeRadius / (2 * l ^ 2)) ≤ q.re) (n : ℕ) :
    ‖iteratedDeriv n (fun q' => (cepsNormalData D θ ρW μ q').regularBottomEntrance
      (dom.canonL ρW) μ q' l) q‖ ≤
        n.factorial * (dom.normalBottomEntranceBound * (1 + l) ^ 2) *
          (2 / dom.normalDiscountRadius) ^ n * l ^ (2 * n) := by
  have hlnegative : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans hl
  have hlcoarse : dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hlw : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans hlcoarse
  have hl0 := (cepsNormal_width_properties dom hW hθ hD hlw).1
  have hδ : 0 < dom.normalDiscountRadius / l ^ 2 :=
    div_pos (cepsNormal_discountRadius_pos dom hD) (sq_pos_of_pos hl0)
  have he := norm_iteratedDeriv_le_of_ball n hδ
    (fun z hz => (cepsNormalData_canonical_bottom_differentiableAt_negative dom hW hθ hD hμ
      (cepsNormal_discount_disc_subset dom hW hθ hD hl hq hre hz).1 hlnegative
      (cepsNormal_discount_disc_subset dom hW hθ hD hl hq hre hz).2).differentiableWithinAt)
    (fun z hz => cepsNormalData_canonical_regularBottomEntrance_bound_negative dom hW hθ hD hμ
      (cepsNormal_discount_disc_subset dom hW hθ hD hl hq hre hz).1.le hl
      (cepsNormal_discount_disc_subset dom hW hθ hD hl hq hre hz).2)
  refine he.trans_eq ?_
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow, inv_pow, pow_mul]
  ring

end PGM
