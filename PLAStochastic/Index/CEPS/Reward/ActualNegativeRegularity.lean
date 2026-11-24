import PLAStochastic.Index.CEPS.Reward.ActualNegativeProbability
import PLAStochastic.Index.CEPS.Reward.ActualRegularity
import PLAStochastic.Index.CEPS.Family.Defs

/-! # Actual reward spatial regularity and the derivative remainder

Continuity of the step density is the explicit regularity input; the
ladder and renewal densities' continuity is proved here, including unit
discount. Class constants are independent of this density representative.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem passageRemainder_eq_rewardRemainder_all_marks {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 ≤ x) :
    dom.passageRemainder ρW μ q a x =
      rewardRemainder (cepsAscDensity ρW fW μ (cexp (-q))) (cepsRootPlus D θ ρW μ q) a x := by
  have hr := dom.actual_expRenewalData hW hθ hD hμ hq0 hq
  have he := hr.renewalRes_eq_exp ((CepsC6.differentiableAt_canonL dom hW hθ hD
    (hμ.trans (min_le_left _ _)) (hq.trans (min_le_left _ _))
    (by have := re_le_norm (cepsRootPlus D θ ρW μ q)
        have := dom.renewal_root_le hW hθ hD hμ hq; linarith [dom.c₀_pos])).continuousAt)
  rw [passageRemainder, rewardRemainder, he,
    dom.actual_reward_moment hW hθ hD hμ hq0 hq ha,
    dom.actual_passage_eq_reward_all_marks hW hθ hD (hμ.trans (min_le_left _ _)) hq0
      (by have := dom.two_c₀_lt; linarith [dom.c₀_pos]) hx]
  rw [exp_sub]
  simp only [exp_neg, cepsRenewalReward]
  ring

include hW hθ hD in
/-- The actual first-passage remainder has a classical derivative with the same vanishing factor. -/
theorem actual_passage_remainder_derivative_bound_all_marks (hf : Continuous fW) {μ : ℝ}
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ} (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (dom.passageRemainder ρW μ q a) x ∧
      ‖deriv (dom.passageRemainder ρW μ q a) x‖ ≤
        dom.rewardSpatialBound * ‖a + cepsRootPlus D θ ρW μ q‖ *
          Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  have hr := dom.actual_expRenewalData hW hθ hD hμ hq0 hq
  have hs : ‖cexp (-q)‖ ≤ 1 := by rw [norm_exp, neg_re]; exact Real.exp_le_one_iff.mpr (by linarith)
  have hu := dom.actual_renewalDensity_continuousAt hW hθ hD hf
    (hμ.trans (min_le_left _ _)) hs hx
  have he : dom.passageRemainder ρW μ q a =ᶠ[𝓝 x]
      rewardRemainder (cepsAscDensity ρW fW μ (cexp (-q))) (cepsRootPlus D θ ρW μ q) a := by
    filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hx] with y hy
    exact dom.passageRemainder_eq_rewardRemainder_all_marks hW hθ hD hμ hq0 hq ha hy.le
  exact ⟨((hasDerivAt_rewardRemainder hr ha hx hu).congr_of_eventuallyEq he).differentiableAt,
    by rw [he.deriv_eq]; exact norm_deriv_rewardRemainder_le hr ha hx hu⟩

include hW hθ hD in
/-- The final Sobolev input pays the classical spatial regularity condition. -/
theorem actual_passage_remainder_derivative_bound_of_sobolev {m : ℕ} {η : ℝ}
    (hf : CepsSobolevClass m η fW) {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (dom.passageRemainder ρW μ q a) x ∧
      ‖deriv (dom.passageRemainder ρW μ q a) x‖ ≤
        dom.rewardSpatialBound * ‖a + cepsRootPlus D θ ρW μ q‖ *
          Real.exp (-((dom.c₀ / 2) / 2) * x) :=
  dom.actual_passage_remainder_derivative_bound_all_marks hW hθ hD hf.continuous
    hμ hq0 hq ha hx

end PGM.CepsCanonDomain
