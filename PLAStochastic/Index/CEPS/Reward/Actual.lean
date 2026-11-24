import PLAStochastic.Index.CEPS.Reward.Vanishing
import PLAStochastic.Index.CEPS.Reward.RenewalData
import PLAStochastic.Index.CEPS.Reward.MomentFormula

/-! # Canonical-residue reward estimates for the actual ladder density

The reward is the explicit renewal solution, with its main moment evaluated
as a divided slope. Random-walk first-passage identification is a separate
probabilistic step.
-/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsRenewalReward (ρW : Measure ℝ) (fW : ℝ → ℝ) (μ : ℝ) (q a : ℂ) : ℝ → ℂ :=
  let g := cepsAscDensity ρW fW μ (cexp (-q))
  rewardSolution g (rewardSource g a)

namespace CepsCanonDomain

def rewardBound {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  4 * rewardLinearBound dom.ladderEnvelope θ (dom.c₀ / 2) dom.renewalLogBound *
    dom.ladderEnvelope / (θ - (dom.c₀ / 2) / 2) ^ 2

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem actual_reward_moment {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) :
    rewardMoment (cepsRootPlus D θ ρW μ q)
        (rewardSource (cepsAscDensity ρW fW μ (cexp (-q))) a) =
      cexp (dom.canonL ρW μ q (-a)) := by
  have hr := dom.actual_expRenewalData hW hθ hD hμ hq0 hq
  rw [rewardMoment_eq_dslope hr ha]
  by_cases he : -a = cepsRootPlus D θ ρW μ q
  · rw [he]
    have hres := hr.renewalRes_eq_exp ((CepsC6.differentiableAt_canonL dom hW hθ hD
      (hμ.trans (min_le_left _ _)) (hq.trans (min_le_left _ _))
      (by have := re_le_norm (cepsRootPlus D θ ρW μ q)
          have := dom.renewal_root_le hW hθ hD hμ hq; linarith [dom.c₀_pos])).continuousAt)
    have hi := congrArg (fun z : ℂ => z⁻¹) hres
    simpa only [renewalRes, inv_inv, ← exp_neg, neg_neg] using hi
  · exact hr.dslope_eq_exp ((abs_re_le_norm _).trans
      (by rw [norm_neg]; linarith [dom.c₀_pos])) he

include hW hθ hD in
/-- Actual analytic renewal reward, including the zero-remainder root parameter. -/
theorem actual_reward_vanishing_bound {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖cepsRenewalReward ρW fW μ q a x -
      cexp (-dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) *
        cexp (-cepsRootPlus D θ ρW μ q * x) *
          rewardMoment (cepsRootPlus D θ ρW μ q)
            (rewardSource (cepsAscDensity ρW fW μ (cexp (-q))) a)‖ ≤
      dom.rewardBound * ‖a + cepsRootPlus D θ ρW μ q‖ *
        Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  have hr := dom.actual_expRenewalData hW hθ hD hμ hq0 hq
  have he := hr.renewalRes_eq_exp ((CepsC6.differentiableAt_canonL dom hW hθ hD
    (hμ.trans (min_le_left _ _)) (hq.trans (min_le_left _ _))
    (by have := re_le_norm (cepsRootPlus D θ ρW μ q)
        have := dom.renewal_root_le hW hθ hD hμ hq; linarith [dom.c₀_pos])).continuousAt)
  simpa only [cepsRenewalReward, rewardBound, he] using
    norm_rewardSolution_sub_pole_vanishing hr ha hx

include hW hθ hD in
/-- The normal-form leading reward, with the main moment fully evaluated. -/
theorem actual_reward_normal_bound {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖cepsRenewalReward ρW fW μ q a x -
      cexp (dom.canonL ρW μ q (-a) - dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) *
        cexp (-cepsRootPlus D θ ρW μ q * x)‖ ≤
      dom.rewardBound * ‖a + cepsRootPlus D θ ρW μ q‖ *
        Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  have hb := dom.actual_reward_vanishing_bound hW hθ hD hμ hq0 hq ha hx
  rw [dom.actual_reward_moment hW hθ hD hμ hq0 hq ha] at hb
  have he : cexp (-dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) *
      cexp (-cepsRootPlus D θ ρW μ q * x) * cexp (dom.canonL ρW μ q (-a)) =
      cexp (dom.canonL ρW μ q (-a) - dom.canonL ρW μ q (cepsRootPlus D θ ρW μ q)) *
        cexp (-cepsRootPlus D θ ρW μ q * x) := by
    rw [exp_sub, exp_neg]
    ring
  rwa [he] at hb

end CepsCanonDomain
end PGM
