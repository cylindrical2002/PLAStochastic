import PLAStochastic.Index.CEPS.Final.Defs
import PLAStochastic.Index.CEPS.Final.Phi
import PLAStochastic.Index.CEPS.Assembly.OneLayer

import PLAStochastic.Index.CEPS.Final.KernelMean
import PLAStochastic.Index.CEPS.Final.KernelLow

import PLAStochastic.Index.CEPS.Final.AnalyticBox

/-!
# P-CEPS from the single remaining kernel-jet premise

`gepC_asymptoticExpansion_of_kernelJets`: the all-order expansion of `gepC ε / ε²` with
`a 0 = optimalMeanConstant / optimalDispersionConstant`, from `CepsKernelJetRepresentation`
alone. The assembly:

* jet data `J` with `jet := cepsJetLaw`, `jetCoeff := cepsJetCoeff` (X8, `cepsJF_of_eq`),
  `scal k p := 4 (1/2)ᵏ (cepsCsAdjust Cs) k p` and `phi := cepsLowCoeff (cepsGkLambda Gk scal) scal`
  (the WP11a/C-16 constraints);
* T1-mid, T1-low, T5, `Φ₀ = φ_Λ` and the decay of `φ_Λ` from `cepsZeroOrder_of_normal`
  (S-9 `cepsNormalClose`, `cepsNormalMid`, `cepsNormalTaylor` built in);
* the remaining `CepsT3` fields from the Taylor composition `cepsJet_phi_rep`, with the
  coordinate count `dim k = ∑_{i ≤ k} (d(Cs i) + d(Gk i))`;
* `gepC_asymptoticExpansion_of_interfaces`.

At the reference law the representation gives `Cs 0 (J Λ) > 0` (T5 at order `0`) and
`Gk 0 (J Λ) y = φ_Λ(-c₀ y / 4)` (C-16), hence `φ_Λ = T₀(-4 · / c₀)` with the smooth zero-order
Taylor coefficient `T₀` of `Gk 0`.
-/

namespace PGM

noncomputable section

open Finset

/-- At the reference law: `Cs 0 (J Λ) > 0` and the zero-order normal coefficient is the
rescaled characteristic function of `Λ`. -/
theorem cepsKernelJet_reference_facts {Cs : ℕ → (ℕ → ℝ) → ℝ} {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ}
    (hmean : CepsNormalMeanExpansion cepsKernelJetBase cepsNormalDn Cs)
    (hexp : CepsNormalLowExpansion cepsKernelJetBase cepsNormalGn Gk) :
    0 < Cs 0 (cepsJetLaw cepsLambda) ∧ ∀ y : ℝ,
      Gk 0 (cepsJetLaw cepsLambda) y =
        cepsLambdaChar (-(4 * Cs 0 (cepsJetLaw cepsLambda)) * y / 4) := by
  let J₁ : CepsJetData :=
    { cepsKernelJetBase with scal := fun k p => 4 * (2⁻¹ : ℝ) ^ k * Cs k p }
  have hT5 : CepsT5 J₁ := cepsT5_of_meanExpansion (J := J₁) hmean fun _ _ => rfl
  obtain ⟨D, θ, hD, hθ, hreg⟩ := exists_regLaw_cepsLambda
  have hv := BrownianAffine.optimalDispersionConstant_pos
  refine ⟨?_, ?_⟩
  · obtain ⟨m, H⟩ := cepsT5_scal_bounds hT5 0
    obtain ⟨η, hη, hcls⟩ := exists_cepsSobolevClass_cepsLambdaDensity m
    obtain ⟨r, hr, c_lo, B, hclo, H'⟩ := H D θ _ _ η hD hθ hv le_rfl hη
    have h := (H' cepsLambda (cepsInputClass_cepsLambda hreg hcls hr.le)).1
    change c_lo ≤ 4 * (2⁻¹ : ℝ) ^ 0 * Cs 0 (cepsJetLaw cepsLambda) at h
    linarith
  · obtain ⟨m, H⟩ := cepsGk_zero_eq_on_class (J := J₁) hT5 cepsNormalClose hexp
    obtain ⟨η, hη, hcls⟩ := exists_cepsSobolevClass_cepsLambdaDensity m
    obtain ⟨r, hr, H'⟩ := H D θ _ _ η hD hθ hv le_rfl hη
    intro y
    have h := H' cepsLambda (cepsInputClass_cepsLambda hreg hcls hr.le) y
    change Gk 0 (cepsJetLaw cepsLambda) y =
      cepsLambdaChar (-(4 * (2⁻¹ : ℝ) ^ 0 * Cs 0 (cepsJetLaw cepsLambda)) * y / 4) at h
    rw [h, pow_zero, mul_one]

/-- The real box representation of a mean coefficient as a complex one. -/
theorem cepsJetScal_of_real {p₀ : ℕ → ℝ} {d : ℕ} {F : (ℕ → ℝ) → ℝ} {T : (Fin d → ℕ) → ℝ}
    (h : ∀ N : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      |F p - ∑ α ∈ cepsTaylorBox d N, T α * cepsMonomial (fun i : Fin d => p i - p₀ i) α| ≤
        K * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)) :
    CepsJetScal p₀ (fun p => (F p : ℂ)) (fun α => (T α : ℂ)) := by
  intro N
  obtain ⟨ρ, K, hρ, H⟩ := h N
  refine ⟨ρ, K, hρ, fun p hp => ?_⟩
  have e : (F p : ℂ) - ∑ α ∈ cepsTaylorBox d N,
      (T α : ℂ) * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ) =
      ((F p - ∑ α ∈ cepsTaylorBox d N,
        T α * cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs]
  exact H p hp

/-- The real box remainder from a complex representation of a real function. -/
theorem abs_sub_re_boxPoly_le {d N : ℕ} (x : ℝ) (T : (Fin d → ℕ) → ℂ) (y : Fin d → ℝ) :
    |x - ∑ α ∈ cepsTaylorBox d N, (T α).re * cepsMonomial y α| ≤
      ‖(x : ℂ) - ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial y α : ℂ)‖ := by
  have e : x - ∑ α ∈ cepsTaylorBox d N, (T α).re * cepsMonomial y α =
      ((x : ℂ) - ∑ α ∈ cepsTaylorBox d N, T α * (cepsMonomial y α : ℂ)).re := by
    simp [Complex.sub_re, Complex.re_sum, Complex.mul_re]
  rw [e]
  exact Complex.abs_re_le_norm _

/-- **The interface bundle from the kernel-jet premise.** -/
theorem cepsTransformInterfaces_of_kernelJets (h : CepsKernelJetRepresentation) :
    CepsTransformInterfaces := by
  obtain ⟨Cs, Gk, hmean, hexp, hreg, hCs, hGk⟩ := h
  obtain ⟨hpos, hΛ0⟩ := cepsKernelJet_reference_facts hmean hexp
  choose dC TC hTC using hCs
  choose dG TG hTGs hTGb hTGr using hGk
  set p₀ : ℕ → ℝ := cepsJetLaw cepsLambda with hp₀
  set sc : ℕ → (ℕ → ℝ) → ℝ := fun k p => 4 * (2⁻¹ : ℝ) ^ k * cepsCsAdjust Cs k p with hsc
  set a : ℝ := 4 * Cs 0 p₀ with ha_def
  have ha : 0 < a := by positivity
  have hsc0 : sc 0 p₀ = a := by
    simp only [sc, a, pow_zero, mul_one, cepsCsAdjust_of_ne hpos.ne']
  set D : ℕ → ℕ := fun k => ∑ i ∈ range (k + 1), (dC i + dG i) with hD
  have hdC : ∀ k, ∀ i ≤ k, dC i ≤ D k := fun k i hi =>
    (Nat.le_add_right _ _).trans (single_le_sum (f := fun i => dC i + dG i)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le hi)))
  have hdG : ∀ k, ∀ i ≤ k, dG i ≤ D k := fun k i hi =>
    (Nat.le_add_left _ _).trans (single_le_sum (f := fun i => dC i + dG i)
      (fun _ _ => Nat.zero_le _) (mem_range.mpr (Nat.lt_succ_of_le hi)))
  -- the scalar coefficients in `D k` coordinates
  have hCsc : ∀ i, CepsJetScal p₀ (fun p => (Cs i p : ℂ)) (fun α => (TC i α : ℂ)) :=
    fun i => cepsJetScal_of_real (hTC i)
  have hscD : ∀ k, ∀ i ≤ k, ∃ T : (Fin (D k) → ℕ) → ℂ,
      CepsJetScal p₀ (fun p => (sc i p : ℂ)) T := by
    intro k i hi
    have hext := ((hCsc i).extend (hdC k i hi)).const_mul ((4 : ℂ) * (2⁻¹ : ℂ) ^ i)
    rcases i with _ | i
    · obtain ⟨ρ, hρ, Hρ⟩ := ((hCsc 0).extend (hdC k 0 hi)).near_ref (half_pos hpos)
      refine ⟨_, hext.congr_fun ⟨ρ, hρ, fun p hp => ?_⟩⟩
      have hne : Cs 0 p ≠ 0 := by
        have := (abs_le.mp (Hρ p hp)).1
        intro h0; rw [h0] at this; linarith
      simp only [sc, cepsCsAdjust_of_ne hne]
      push_cast; ring
    · refine ⟨_, hext.congr_fun ⟨1, one_pos, fun p _ => ?_⟩⟩
      simp only [sc, cepsCsAdjust_succ]
      push_cast; ring
  -- the low-band coefficients
  have hGrep : ∀ j m, CepsJetDecay p₀ (fun y p => iteratedDeriv m (Gk j p) y)
      (fun α => iteratedDeriv m (TG j α)) := fun j m =>
    ⟨fun α => hTGb j α m, fun N => hTGr j m N⟩
  have hT00 : ∀ y, TG 0 0 y = Gk 0 p₀ y := fun y => by
    simpa only [iteratedDeriv_zero] using (hGrep 0 0).coeff_zero y
  have hΛ : ∀ x, cepsLambdaChar x = TG 0 0 (-4 * x / a) := by
    intro x
    rw [hT00, hΛ0]
    congr 1
    field_simp
  -- the composed coefficients
  have hphi : ∀ k, ∃ T : (Fin (D k) → ℕ) → ℝ → ℂ,
      CepsJetDecay p₀ (fun u p => cepsLowCoeff (cepsGkLambda Gk sc) sc k u p) T := by
    intro k
    let TGe : ℕ → (Fin (D k) → ℕ) → ℝ → ℂ := fun j =>
      if hj : j ≤ k then cepsJetExtend (hdG k j hj) (TG j) else 0
    have hTGe : ∀ j (hj : j ≤ k), TGe j = cepsJetExtend (hdG k j hj) (TG j) :=
      fun j hj => dif_pos hj
    refine cepsJet_phi_rep (TG := TGe) ha hsc0 (hscD k) (fun j hj α n => ?_)
      (fun j hj α n => ?_) (fun j hj m => ?_) ?_
    · rw [hTGe j hj]
      unfold cepsJetExtend
      split_ifs
      · exact hTGs j _ n
      · exact contDiff_const
    · rw [hTGe j hj, iteratedDeriv_cepsJetExtend]
      unfold cepsJetExtend
      split_ifs
      · exact hTGb j _ n
      · exact ⟨0, 1, one_pos, 0, fun y => by simp⟩
    · have h := (hGrep j m).extend (hdG k j hj)
      rw [hTGe j hj]
      refine ⟨fun α => ?_, fun N => (h.2 N).congr_coeff fun α _ u => ?_⟩
      · simp only [iteratedDeriv_cepsJetExtend]; exact h.1 α
      · rw [iteratedDeriv_cepsJetExtend]
    · intro x
      rw [hTGe 0 (Nat.zero_le k), cepsJetExtend_zero]
      exact hΛ x
  choose TP hTP using hphi
  have hscal : ∀ k, ∃ T : (Fin (D k) → ℕ) → ℂ, CepsJetScal p₀ (fun p => (sc k p : ℂ)) T :=
    fun k => hscD k k le_rfl
  choose TS hTS using hscal
  let J : CepsJetData :=
    { jet := cepsJetLaw
      phi := fun k u p => cepsLowCoeff (cepsGkLambda Gk sc) sc k u p
      scal := sc
      dim := D
      phiTaylor := TP
      scalTaylor := fun k α => (TS k α).re
      jetCoeff := cepsJetCoeff }
  have hz := cepsZeroOrder_of_normal (J := J) (Cs := Cs) (Gk := Gk) hmean (fun _ _ => rfl)
    hexp hreg (fun _ _ _ => rfl)
  have hT3 : CepsT3 J :=
    { phi_zero := hz.2.1
      lambdaChar_bound := hz.2.2
      phiTaylor_bound := fun k _ α => (hTP k).1 α
      phi_remainder := fun k _ N => (hTP k).2 N
      scal_remainder := fun k N => by
        obtain ⟨ρ, K, hρ, H⟩ := hTS k N
        exact ⟨ρ, K, hρ, fun p hp => (abs_sub_re_boxPoly_le (sc k p) (TS k) _).trans (H p hp)⟩ }
  exact ⟨hz.1.1, J, hz.1.2.1, hT3, hz.1.2.2, cepsJF_of_eq rfl rfl⟩

/-- **P-CEPS from the kernel-jet premise.** The all-order expansion of `gepC ε / ε²`, unique,
with leading coefficient `optimalMeanConstant / optimalDispersionConstant`. -/
theorem gepC_asymptoticExpansion_of_kernelJets (h : CepsKernelJetRepresentation) :
    ∃! a : ℕ → ℝ, (∀ M : ℕ, ∃ K eps0 : ℝ, ∀ eps : ℝ, eps0 ≤ eps →
      |gepC eps / eps ^ 2 - ∑ j ∈ Finset.range (M + 1), a j * eps ^ (-(j : ℤ))| ≤
        K * eps ^ (-((M : ℤ) + 1))) ∧
      a 0 = BrownianAffine.optimalMeanConstant / BrownianAffine.optimalDispersionConstant :=
  gepC_asymptoticExpansion_of_interfaces (cepsTransformInterfaces_of_kernelJets h)

end

end PGM
