import PLAStochastic.Index.CEPS.ZeroOrder.PhiZero
import PLAStochastic.Index.CEPS.Total.Discharge
import PLAStochastic.Index.CEPS.Total.Mid
import PLAStochastic.Index.CEPS.Total.Taylor

/-!
# C-16: unconditional instances for the fixed normal transform

With the proved `cepsNormalClose`, `cepsNormalMid`, `cepsNormalTaylor` for `cepsNormalGn`
and `cepsNormalDn`:

* `cepsT1Mid` and `cepsLambdaChar_stretched_bound` (`CepsT3.lambdaChar_bound`) hold
  unconditionally;
* for any mean expansion `CepsNormalMeanExpansion J cepsNormalDn Cs` and any low expansion
  `CepsNormalLowExpansion J cepsNormalGn Gk`, the WP11a replacement
  `Gk ↦ cepsGkLambda Gk J.scal` keeps both the low expansion and the coefficient regularity
  (`cepsNormalLowExpansion_gkLambda'`, `cepsNormalCoeffReg_gkLambda'`), and
  `Φ₀(u; p) = φ_Λ(u)` for every `p` once `c₀(p) ≠ 0`
  (`cepsT3_phi_zero_of_gkLambda`, `cepsCsAdjust`).
-/

namespace PGM

noncomputable section

/-- **T1-mid holds.** -/
theorem cepsT1Mid : CepsT1Mid := cepsT1Mid_of_normal cepsNormalClose cepsNormalMid

/-- **C-16 (`CepsT3.lambdaChar_bound`), unconditional.** -/
theorem cepsLambdaChar_stretched_bound :
    ∃ K c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ u, ‖cepsLambdaChar u‖ ≤ K * cepsStretchedWeight c d u :=
  cepsLambdaChar_bound_of_T1Mid cepsT1Mid

/-- T5 for the fixed normal transform, from a mean expansion. -/
theorem cepsT5_of_meanExpansion {J : CepsJetData} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    (hmean : CepsNormalMeanExpansion J cepsNormalDn Cs)
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * Cs k p) : CepsT5 J :=
  cepsT5_of_normal cepsNormalClose cepsNormalTaylor hmean hscal

theorem cepsNormalLowExpansion_gkLambda' {J : CepsJetData} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hmean : CepsNormalMeanExpansion J cepsNormalDn Cs)
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * Cs k p)
    (hexp : CepsNormalLowExpansion J cepsNormalGn Gk) :
    CepsNormalLowExpansion J cepsNormalGn (cepsGkLambda Gk J.scal) :=
  cepsNormalLowExpansion_gkLambda (cepsT5_of_meanExpansion hmean hscal) cepsNormalClose hexp

theorem cepsNormalCoeffReg_gkLambda' {J : CepsJetData} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hmean : CepsNormalMeanExpansion J cepsNormalDn Cs)
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * Cs k p)
    (hexp : CepsNormalLowExpansion J cepsNormalGn Gk) (hreg : CepsNormalCoeffReg J Gk) :
    CepsNormalCoeffReg J (cepsGkLambda Gk J.scal) :=
  cepsNormalCoeffReg_gkLambda (cepsT5_of_meanExpansion hmean hscal) cepsNormalClose hexp hreg

/-- The adjusted mean expansion for the fixed normal transform. -/
theorem cepsNormalMeanExpansion_adjust' {J : CepsJetData} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    (hmean : CepsNormalMeanExpansion J cepsNormalDn Cs) :
    CepsNormalMeanExpansion J cepsNormalDn (cepsCsAdjust Cs) :=
  cepsNormalMeanExpansion_adjust cepsNormalClose cepsNormalTaylor hmean

/-- **C-16 assembled.** Given the normal-side data with the WP11a choices
`scal k p = 4 (1/2)ᵏ C'_k(p)` for the adjusted `C' = cepsCsAdjust Cs`, `Gk' = cepsGkLambda Gk scal`
and `phi = cepsLowCoeff Gk' scal`: T1-mid, T1-low and T5 hold, `Φ₀ = φ_Λ` for every jet
vector, and `φ_Λ` decays stretched-exponentially. -/
theorem cepsZeroOrder_of_normal {J : CepsJetData} {Cs : ℕ → (ℕ → ℝ) → ℝ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hmean : CepsNormalMeanExpansion J cepsNormalDn Cs)
    (hscal : ∀ k p, J.scal k p = 4 * (2⁻¹) ^ k * cepsCsAdjust Cs k p)
    (hexp : CepsNormalLowExpansion J cepsNormalGn Gk) (hreg : CepsNormalCoeffReg J Gk)
    (hphi : ∀ k u p, J.phi k u p = cepsLowCoeff (cepsGkLambda Gk J.scal) J.scal k u p) :
    (CepsT1Mid ∧ CepsT1Low J ∧ CepsT5 J) ∧ (∀ u p, J.phi 0 u p = cepsLambdaChar u) ∧
      ∃ K c : ℝ, 0 < c ∧ ∃ d : ℕ, ∀ u, ‖cepsLambdaChar u‖ ≤ K * cepsStretchedWeight c d u := by
  have hmean' := cepsNormalMeanExpansion_adjust' hmean
  refine ⟨cepsT1T5_of_normal cepsNormalClose cepsNormalTaylor hmean' hscal
    (cepsNormalLowExpansion_gkLambda' hmean' hscal hexp)
    (cepsNormalCoeffReg_gkLambda' hmean' hscal hexp hreg) hphi cepsNormalMid,
    cepsT3_phi_zero_of_gkLambda hphi fun p => ?_, cepsLambdaChar_stretched_bound⟩
  rw [hscal]
  exact cepsCsAdjust_scal_zero_ne_zero Cs p

end

end PGM
