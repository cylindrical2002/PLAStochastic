import PLAStochastic.Index.CEPS.Glue.T5
import PLAStochastic.Index.CEPS.Glue.T1Low
import PLAStochastic.Index.CEPS.Glue.T1Mid
import PLAStochastic.Index.CEPS.Glue.Coeff

/-!
# WP11a: glue from the normal transform to T1 and T5 (assembly)

`cepsT1T5_of_normal`: the normal-side premises of `Glue.Defs` (S-9, the Taylor bound at `0`, the
`b`-expansions of C-10, coefficient regularity, C-11) give `CepsT1Mid`, `CepsT1Low J` and
`CepsT5 J` for jet data whose scalar coefficients are `c_k = 4 · 2^{-k} C_k` and whose transform
coefficients are the composed coefficients `cepsLowCoeff Gk J.scal`. The stretched-exponential
bound of these coefficients is `norm_cepsLowCoeff_le_stretched`.
-/

namespace PGM

open MeasureTheory

/-- **T1 and T5 from the normal-side premises.** -/
theorem cepsT1T5_of_normal {J : CepsJetData} {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    {Dn : ℝ → ProbabilityMeasure ℝ → ℂ} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hclose : CepsNormalClose Gn)
    (htaylor : CepsNormalTaylor Gn Dn) (hmean : CepsNormalMeanExpansion J Dn Cs)
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * Cs k p)
    (hexp : CepsNormalLowExpansion J Gn Gk) (hreg : CepsNormalCoeffReg J Gk)
    (hphi : ∀ k u p, J.phi k u p = cepsLowCoeff Gk J.scal k u p) (hmid : CepsNormalMid Gn) :
    CepsT1Mid ∧ CepsT1Low J ∧ CepsT5 J := by
  have hT5 := cepsT5_of_normal hclose htaylor hmean hscal
  exact ⟨cepsT1Mid_of_normal hclose hmid, cepsT1Low_of_normal hT5 hclose hexp hreg hphi, hT5⟩

end PGM
