import PLAStochastic.Index.CEPS.Normal.RelativeWeight
import PLAStochastic.Index.CEPS.Normal.SecondSlopeBound

/-! # Polynomial spatial derivative bounds after normal-weight cancellation -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsNormalG_differentiableOn_spatial {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) (l : ℂ) :
    DifferentiableOn ℂ ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)
      (ball 0 (dom.c₀ / 2)) := by
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hQ : DifferentiableOn ℂ (cepsQ D θ ρW μ q) (ball 0 (dom.c₀ / 2)) := by
    intro z hz
    have hzA : z ∈ ball (0 : ℂ) dom.ρA := mem_ball_zero_iff.mpr (by
      have := mem_ball_zero_iff.mp hz; have := dom.c₀_le; have := dom.ρA_pos; linarith)
    exact (CepsC6.differentiableAt_cepsQ dom hW hθ hD hμ' hq hzA).differentiableWithinAt
  have hL : DifferentiableOn ℂ (dom.canonL ρW μ q) (ball 0 (dom.c₀ / 2)) := by
    intro z hz
    have hzr : z.re < dom.c₀ := by
      have := mem_ball_zero_iff.mp hz; linarith [re_le_norm z, dom.c₀_pos]
    exact (CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq hzr).differentiableWithinAt
  exact (((differentiableOn_id.neg.mul_const l).cexp).mul hQ).mul ((hL.const_mul (-2)).cexp)

include hW hθ hD in
theorem cepsNormal_relative_secondDerivative_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 ≤ l)
    {w : ℂ} (hw : ‖w‖ ≤ dom.c₀ / 4)
    (hre : (cepsRootMinus D θ ρW μ q).re ≤ w.re) :
    ‖deriv (deriv ((cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l)) w‖ ≤
      dom.normalSpatialSecondBound * (1 + l) ^ 2 *
        ‖(cepsWHNormalData D θ ρW μ q).normalG (dom.canonL ρW) μ q l
          (cepsRootMinus D θ ρW μ q)‖ := by
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
    ((cepsNormalG_differentiableOn_spatial dom hW hθ hD hμ hq l).mono hsub)
    (fun z hz => cepsNormal_relative_weight_on_ball dom hW hθ hD hμ hq hl hw hre hz)
  rw [iteratedDeriv_succ, iteratedDeriv_one] at hd
  refine hd.trans_eq ?_
  simp only [Nat.factorial_succ, Nat.factorial_zero, Nat.cast_mul, Nat.cast_one]
  unfold CepsCanonDomain.normalSpatialSecondBound δ
  field_simp
  ring

end PGM
