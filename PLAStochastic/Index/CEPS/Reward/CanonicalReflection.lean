import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.EntranceReflection
import PLAStochastic.Index.CEPS.Ident.Main

/-! # Actual root and canonical exponential factors under reflection -/

noncomputable section
open MeasureTheory Complex Filter Topology
open PGM.WienerHopf
namespace PGM.CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW in
theorem ascTransform_reflected_drift (μ : ℝ) (s z : ℂ) :
    ascTransform (driftStep (ρW.map Neg.neg) (-μ)) s z =
      descTransform (driftStep ρW μ) s (-z) := by
  have := hW.isProbabilityMeasure
  rw [← driftStep_map_neg]
  exact ascTransform_map_neg_eq_desc
    (hW.measurable.comp (show Measurable (fun y : ℝ => y - μ) by fun_prop))
    (driftStep_eq_withDensity hW μ) s z

include hW hθ hD in
theorem rootPlus_reflected_eq_neg_rootMinus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) :
    cepsRootPlus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q = -cepsRootMinus D θ ρW μ q := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by simpa only [norm_real, Real.norm_eq_abs] using hμ
  have hb := dom.norm_rootMinus_le hW hθ hD hμc hq
  have hz : (-cepsRootMinus D θ ρW μ q).re < dom.c₀ := by
    have := re_le_norm (-cepsRootMinus D θ ρW μ q)
    rw [norm_neg] at this
    linarith [dom.c₀_pos]
  have he := (dom.cepsWHIdent hW.neg hθ hD (-μ) hμ' q hq0 hq).1
    (-cepsRootMinus D θ ρW μ q) hz
  rw [ascTransform_reflected_drift hW, neg_neg,
    dom.descTransform_rootMinus hW hθ hD (dom.cepsWHIdent hW hθ hD) hμ hq0 hq,
    sub_self] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right (Complex.exp_ne_zero _))

include hW hθ hD in
theorem exp_canonL_reflected_at_root {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) :
    cexp (dom.canonL (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q
      (cepsRootPlus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q)) =
    cexp (dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)) := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have hr := dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD hμ hq0 hq
  have hp := dom.hasDerivAt_ascTransform_rootPlus hW.neg hθ hD
    (dom.cepsWHIdent hW.neg hθ hD) hμ' hq0 hq
  have hm := dom.hasDerivAt_descTransform_rootMinus hW hθ hD
    (dom.cepsWHIdent hW hθ hD) hμ hq0 hq
  have hn := hm.comp_of_eq (-cepsRootMinus D θ ρW μ q)
    (hasDerivAt_id' (-cepsRootMinus D θ ρW μ q)).neg (by simp)
  have hf : (fun z => ascTransform (driftStep (ρW.map Neg.neg) (-μ)) (cexp (-q)) z) =
      (fun z => descTransform (driftStep ρW μ) (cexp (-q)) (-z)) :=
    funext (ascTransform_reflected_drift hW μ (cexp (-q)))
  rw [hf, hr] at hp
  have hn' : HasDerivAt (fun z => descTransform (driftStep ρW μ) (cexp (-q)) (-z))
      (cexp (dom.canonLMinus ρW μ q (cepsRootMinus D θ ρW μ q)))
      (-cepsRootMinus D θ ρW μ q) := by
    simpa using! hn
  simpa only [hr] using hp.unique hn'

include hW hθ hD in
theorem exp_canonL_reflected {μ : ℝ} (hμ : |μ| ≤ dom.μ₀)
    {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀) {z : ℂ}
    (hz : |z.re| < dom.c₀) :
    cexp (dom.canonL (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q z) = cexp (dom.canonLMinus ρW μ q (-z)) := by
  have hμ' : |(-μ)| ≤ dom.μ₀ := by simpa only [abs_neg] using hμ
  have hr := dom.rootPlus_reflected_eq_neg_rootMinus hW hθ hD hμ hq0 hq
  by_cases he : z = cepsRootPlus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q
  · rw [he, hr, neg_neg]
    simpa only [hr] using dom.exp_canonL_reflected_at_root hW hθ hD hμ hq0 hq
  · have hp := (dom.cepsWHIdent hW.neg hθ hD (-μ) hμ' q hq0 hq).1 z
      (lt_of_le_of_lt (le_abs_self z.re) hz)
    have hm := (dom.cepsWHIdent hW hθ hD μ hμ q hq0 hq).2 (-z)
      (by simpa only [neg_re, abs_neg] using hz)
    rw [ascTransform_reflected_drift hW] at hp
    have hc : cepsRootPlus D θ (ρW.map Neg.neg) ((-μ : ℝ) : ℂ) q - z =
        -z - cepsRootMinus D θ ρW μ q := by rw [hr]; ring
    rw [← hc] at hm
    exact mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm he)) (hp.symm.trans hm)

end PGM.CepsCanonDomain
