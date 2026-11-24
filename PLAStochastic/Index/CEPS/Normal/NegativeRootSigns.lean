import PLAStochastic.Index.CEPS.Normal.NegativeDelta
import PLAStochastic.Index.CEPS.Scaled.LadderSigns
import PLAStochastic.ForMathlib.Analysis.Complex.SqrtHorizontal

/-! # Width-scaled root real-part bounds on the common negative extension -/

noncomputable section
open Complex MeasureTheory
open PGM.WienerHopf
namespace PGM

namespace CepsCanonDomain
def normalRootSlack {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  cepsChartK D * Real.sqrt dom.normalNegativeRadius
end CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsRoots_horizontal_distance_le {μ q q' : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hq : ‖q‖ ≤ dom.q₀) (hq' : ‖q'‖ ≤ dom.q₀) (him : q.im = q'.im) :
    ‖cepsRootPlus D θ ρW μ q - cepsRootPlus D θ ρW μ q'‖ ≤
      cepsChartK D * Real.sqrt ‖q - q'‖ ∧
    ‖cepsRootMinus D θ ρW μ q - cepsRootMinus D θ ρW μ q'‖ ≤
      cepsChartK D * Real.sqrt ‖q - q'‖ := by
  have hr := dom.norm_cepsRootR_lt hW hθ hD hμ hq
  have hr' := dom.norm_cepsRootR_lt hW hθ hD hμ hq'
  have hh : (q - cepsMorseMin D θ ρW μ).im = (q' - cepsMorseMin D θ ρW μ).im := by
    simp only [sub_im, him]
  have hs := norm_sqrt_sub_sqrt_le_of_im_eq hh
  have hid : q - cepsMorseMin D θ ρW μ - (q' - cepsMorseMin D θ ρW μ) = q - q' := by ring
  rw [hid] at hs
  have hc := two_div_norm_cepsChartSlope_le hW hθ hD
  have hK := cepsChartK_pos hD
  constructor
  · exact (norm_cepsMorseRoot_sub_le hW hθ hD (dom.μ_lt_chart hμ) hr hr').trans
      (mul_le_mul hc hs (norm_nonneg _) hK.le)
  · have hn := norm_cepsMorseRoot_sub_le hW hθ hD (dom.μ_lt_chart hμ)
      (r₁ := -cepsRootR D θ ρW μ q) (by simpa using hr)
      (r₂ := -cepsRootR D θ ρW μ q') (by simpa using hr')
    simp only [neg_sub_neg, norm_sub_rev] at hn
    exact hn.trans (mul_le_mul hc hs (norm_nonneg _) hK.le)

include hW hθ hD in
theorem cepsRoots_re_signs_negative {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : 0 < l)
    (hre : -(dom.normalNegativeRadius / l ^ 2) ≤ q.re) :
    -dom.normalRootSlack ≤ (cepsRootPlus D θ ρW μ q).re * l ∧
      (cepsRootMinus D θ ρW μ q).re * l ≤ dom.normalRootSlack := by
  have hC : 0 ≤ dom.normalRootSlack := by
    unfold CepsCanonDomain.normalRootSlack
    exact mul_nonneg (cepsChartK_pos hD).le (Real.sqrt_nonneg _)
  by_cases hpos : 0 ≤ q.re
  · obtain ⟨hp, hm⟩ := cepsRoots_re_signs dom hW hθ hD hμ hpos hq
    exact ⟨(neg_nonpos.mpr hC).trans (mul_nonneg hp hl.le),
      (mul_nonpos_of_nonpos_of_nonneg hm hl.le).trans hC⟩
  have hqneg : q.re < 0 := lt_of_not_ge hpos
  let q' : ℂ := q.im * I
  have hqp : q'.re = 0 := by simp [q']
  have hqi : q.im = q'.im := by simp [q']
  have hqn : ‖q'‖ ≤ dom.q₀ := by
    have hn : ‖q'‖ = |q.im| := by simp [q']
    rw [hn]
    exact (abs_im_le_norm q).trans hq
  have hμ' : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  obtain ⟨hp, hm⟩ := cepsRoots_re_signs dom hW hθ hD hμ (by rw [hqp]) hqn
  obtain ⟨hpd, hmd⟩ := cepsRoots_horizontal_distance_le dom hW hθ hD hμ' hq hqn hqi
  have hdiff : q - q' = (q.re : ℂ) := by apply Complex.ext <;> simp [q']
  have hnorm : ‖q - q'‖ = -q.re := by
    rw [hdiff, norm_real, Real.norm_eq_abs, abs_of_neg hqneg]
  rw [hnorm] at hpd hmd
  have hs : Real.sqrt (-q.re) * l ≤ Real.sqrt dom.normalNegativeRadius := by
    have ha : 0 ≤ dom.normalNegativeRadius := (cepsNormal_negativeRadius_pos dom hD).le
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ -q.re)
    have hsqA := Real.sq_sqrt ha
    have hrl : -q.re * l ^ 2 ≤ dom.normalNegativeRadius := by
      have hh : -q.re ≤ dom.normalNegativeRadius / l ^ 2 := by linarith
      exact (le_div_iff₀ (sq_pos_of_pos hl)).mp hh
    nlinarith [Real.sqrt_nonneg (-q.re), Real.sqrt_nonneg dom.normalNegativeRadius,
      mul_nonneg (Real.sqrt_nonneg (-q.re)) hl.le]
  have hK := cepsChartK_pos hD
  have hpwidth := mul_le_mul_of_nonneg_right hpd hl.le
  have hmwidth := mul_le_mul_of_nonneg_right hmd hl.le
  have hbudget := mul_le_mul_of_nonneg_left hs hK.le
  have hpr := (neg_le_abs (cepsRootPlus D θ ρW μ q - cepsRootPlus D θ ρW μ q').re).trans
    (abs_re_le_norm _)
  have hmr := (le_abs_self (cepsRootMinus D θ ρW μ q - cepsRootMinus D θ ρW μ q').re).trans
    (abs_re_le_norm _)
  simp only [sub_re] at hpr hmr
  have hprwidth := mul_le_mul_of_nonneg_right hpr hl.le
  have hmrwidth := mul_le_mul_of_nonneg_right hmr hl.le
  unfold CepsCanonDomain.normalRootSlack
  constructor <;> nlinarith [mul_nonneg hp hl.le, mul_nonpos_of_nonpos_of_nonneg hm hl.le]

end PGM
