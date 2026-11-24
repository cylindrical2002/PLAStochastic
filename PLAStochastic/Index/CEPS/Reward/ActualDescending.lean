import PLAStochastic.Index.CEPS.Reward.CanonicalReflection
import PLAStochastic.Index.CEPS.Reward.PassageReflection
import PLAStochastic.Index.CEPS.Reward.ActualNegativeRegularity

/-! # Actual strict downcrossing: canonical main term and spatial remainder

Reflection preserves all step-class constants. The weak descending ladder
and strict downcrossing are identified from the density of each finite
entrance height, including at zero discount and at coincident roots.
-/

noncomputable section
open MeasureTheory Complex
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

def descendingPassageRemainder {D θ v : ℝ} (dom : CepsCanonDomain D θ v)
    (ρW : Measure ℝ) (μ : ℝ) (q a : ℂ) (x : ℝ) : ℂ :=
  descendingPassageTransform (driftStep ρW μ) (cexp (-q)) a x -
    cexp (dom.canonLMinus ρW μ q a - dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) *
      cexp (cepsRootMinus D θ ρW μ q * x)

include hW hθ hD in
theorem reflected_passage_main_eq {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) (x : ℝ) :
    cexp (dom.canonL (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q (-a) -
      dom.canonL (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q
        (cepsRootPlus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q)) *
      cexp (-cepsRootPlus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q * x) =
    cexp (dom.canonLMinus ρW μ q a - dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) *
      cexp (cepsRootMinus D θ ρW μ q * x) := by
  rw [exp_sub, exp_sub,
    dom.exp_canonL_reflected hW hθ hD hμ hq0 hq
      (z := -a) (by rw [neg_re, abs_neg]; linarith [abs_re_le_norm a, dom.c₀_pos]),
    neg_neg, dom.exp_canonL_reflected_at_root hW hθ hD hμ hq0 hq,
    dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD hμ hq0 hq, neg_neg]

include hW hθ hD in
theorem descendingPassageRemainder_eq_reflected {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) :
    dom.descendingPassageRemainder ρW μ q a = dom.passageRemainder (ρW.map Neg.neg) (-μ) q a := by
  have := hW.isProbabilityMeasure
  funext x
  unfold descendingPassageRemainder passageRemainder
  rw [descendingPassageTransform_eq_reflected, driftStep_map_neg,
    dom.reflected_passage_main_eq hW hθ hD hμ hq0 hq ha]

include hW hθ hD in
theorem actual_descending_passage_normal_bound {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ}
    (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2) {x : ℝ} (hx : 0 ≤ x) :
    ‖dom.descendingPassageRemainder ρW μ q a x‖ ≤
      dom.rewardBound * ‖a - cepsRootMinus D θ ρW μ q‖ *
        Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  have ht := dom.actual_passage_normal_bound_all_marks hW.neg hθ hD
    (μ := -μ) (by simpa only [abs_neg] using hμ) hq0 hq ha hx
  rw [dom.descendingPassageRemainder_eq_reflected hW hθ hD
    (hμ.trans (min_le_left _ _)) hq0 (hq.trans (min_le_left _ _)) ha]
  change ‖dom.passageRemainder (ρW.map Neg.neg) (-μ) q a x‖ ≤ _
  unfold passageRemainder
  simpa only [dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD
    (hμ.trans (min_le_left _ _)) hq0 (hq.trans (min_le_left _ _)), ← sub_eq_add_neg] using ht

include hW hθ hD in
theorem actual_descending_passage_remainder_derivative_bound (hf : Continuous fW)
    {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ} (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2)
    {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (dom.descendingPassageRemainder ρW μ q a) x ∧
      ‖deriv (dom.descendingPassageRemainder ρW μ q a) x‖ ≤
        dom.rewardSpatialBound * ‖a - cepsRootMinus D θ ρW μ q‖ *
          Real.exp (-((dom.c₀ / 2) / 2) * x) := by
  rw [dom.descendingPassageRemainder_eq_reflected hW hθ hD
    (hμ.trans (min_le_left _ _)) hq0 (hq.trans (min_le_left _ _)) ha]
  have ht := dom.actual_passage_remainder_derivative_bound_all_marks hW.neg hθ hD
    (hf.comp continuous_neg) (μ := -μ) (by simpa only [abs_neg] using hμ) hq0 hq ha hx
  simpa only [dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD
    (hμ.trans (min_le_left _ _)) hq0 (hq.trans (min_le_left _ _)), ← sub_eq_add_neg] using ht

include hW hθ hD in
theorem actual_descending_passage_remainder_derivative_bound_of_sobolev
    {m : ℕ} {η : ℝ} (hf : CepsSobolevClass m η fW)
    {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.renewalDiscount) {a : ℂ} (ha : ‖a‖ ≤ (dom.c₀ / 2) / 2)
    {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (dom.descendingPassageRemainder ρW μ q a) x ∧
      ‖deriv (dom.descendingPassageRemainder ρW μ q a) x‖ ≤
        dom.rewardSpatialBound * ‖a - cepsRootMinus D θ ρW μ q‖ *
          Real.exp (-((dom.c₀ / 2) / 2) * x) :=
  dom.actual_descending_passage_remainder_derivative_bound hW hθ hD hf.continuous hμ hq0 hq ha hx

end PGM.CepsCanonDomain
