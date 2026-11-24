import PLAStochastic.Index.CEPS.Reward.Actual
import PLAStochastic.Index.CEPS.Reward.NegativeProbability

/-! # Canonical first-passage reward estimates for the actual drifted walk

Both signs of the mark are included; the discount is in the closed right
half-disk, including zero. Infinite first-passage times contribute zero.
-/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
/-- Identification with the original walk, from its step density and path law. -/
theorem actual_passage_eq_reward_all_marks {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) {a : ℂ} (ha : ‖a‖ < θ) {x : ℝ} (hx : 0 ≤ x) :
    passageTransform (driftStep ρW μ) (cexp (-q)) a x = cepsRenewalReward ρW fW μ q a x := by
  have := hW.isProbabilityMeasure
  have hs : ‖cexp (-q)‖ ≤ 1 := by
    rw [norm_exp, neg_re]
    exact Real.exp_le_one_iff.mpr (by linarith)
  exact passageTransform_eq_rewardSolution_of_expDensity (fun y => hW.nonneg _)
    (hW.measurable.comp (show Measurable (fun y : ℝ => y - μ) by fun_prop))
    (driftStep_eq_withDensity hW μ) (cepsAscDensity_isExpDensity dom hW hθ hD hμ hs)
    (cepsAscDensity_isExpDensity dom hW hθ hD hμ (s := 1) (by simp)) hθ hs ha hx

include hW hθ hD in
/-- The canonical main term and vanishing remainder for the actual first-passage expectation. -/
theorem actual_passage_normal_bound_all_marks {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖passageTransform (driftStep ρW μ) (cexp (-q)) a x -
      cexp (dom.canonL ρW μ q (-a) - dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) *
        cexp (-cepsRootPlus D θ ρW μ q * x)‖ ≤
      dom.rewardBound * ‖a + cepsRootPlus D θ ρW μ q‖ *
        Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  rw [dom.actual_passage_eq_reward_all_marks hW hθ hD (hμ.trans (min_le_left _ _)) hq0
    (by have := dom.two_c₀_lt; linarith [dom.c₀_pos]) hx]
  exact dom.actual_reward_normal_bound hW hθ hD hμ hq0 hq ha hx

end PGM.CepsCanonDomain
