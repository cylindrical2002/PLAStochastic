import PLAStochastic.Index.CEPS.Strip.WeightBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightedInverse

/-! # Exponential denominator, nonzero divided denominator and its weighted inverse

Admissible-frequency forms of `ComplexJetDeltaBudget`, `ComplexJetDenominatorUniform`
and `ComplexJetWeightedInverse`. The joint origin is excluded by admissibility.
-/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexKernelJetDelta_uniform_lower_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        cepsFiniteComplexDeltaSector vlo vhi / 4 *
          ((|lam| + Real.sqrt ‖z‖) / (1 + |lam| + Real.sqrt ‖z‖)) ≤
          ‖cepsComplexKernelJetDelta (cepsComplexJetPad d p) N lam z b‖ := by
  let A := cepsFiniteQuadraticRootBound vlo
  let S := cepsFiniteWeightSpatialWindow vlo
  let c := cepsFiniteComplexDeltaSector vlo vhi
  let Wlo := vlo / 4 * Real.exp (-2 * M)
  let ε := c * S * Wlo / (64 * A)
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hS : 0 < S := cepsFiniteWeightSpatialWindow_pos hlo
  have hc : 0 < c := cepsFiniteComplexDeltaSector_pos hlo hhi0
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcD : c ≤ cepsFiniteRootPhaseLower vlo vhi := min_le_right _ _
  have hWlo : 0 < Wlo := by dsimp [Wlo]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  let δroot := cepsFiniteWeightedRootRadius N M vlo vhi
  have hδroot : 0 < δroot := cepsFiniteWeightedRootRadius_pos N hM hlo hhi0
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget_adm d N
    (M := M) (vhi := vhi) (S := S) hM hlo
  obtain ⟨δs, hδs, hSlope⟩ := cepsComplexKernelJetWeight_root_slope_uniform_budget_adm d N
    (M := M) (vhi := vhi) hM hlo hε
  refine ⟨min δroot (min δw δs), lt_min hδroot (lt_min hδw hδs), ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let W := cepsComplexKernelJetWeight P N lam z b
  let ratio := W rp / W rm
  let gap := (rp - rm) * (1 + b * lam)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hbroot : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hbNewton := hbroot.trans (min_le_left _ _)
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hrp : ‖rp‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbNewton N).2
  have hrm : ‖rm‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbNewton N).2
  have hmark : ‖rm‖ ≤ S * X := by
    calc
      _ ≤ 2 * A * F := hrm
      _ ≤ 2 * A * X := mul_le_mul_of_nonneg_left hFX (by positivity)
      _ ≤ S * X := mul_le_mul_of_nonneg_right (by dsimp [S, cepsFiniteWeightSpatialWindow]; linarith) hX.le
  have hwm : Wlo ≤ ‖W rm‖ := (hW p hp hv hhi lam z b rm hz
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))) hmark).1
  have hwm0 : W rm ≠ 0 := norm_pos_iff.mp (hWlo.trans_le hwm)
  have hwmn : 0 < ‖W rm‖ := hWlo.trans_le hwm
  have hs : ‖dslope W rm rp‖ ≤ 4 * ε / (S * X) := hSlope p hp hv lam z b hz
    (hb.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hdiff : ‖W rp - W rm‖ ≤ (4 * A * F) * (4 * ε / (S * X)) := by
    have he := sub_smul_dslope W rm rp
    rw [smul_eq_mul] at he
    rw [← he, norm_mul]
    apply mul_le_mul _ hs (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (by linarith)
  have hfactor : ‖ratio - 1‖ ≤ c / 4 * (F / X) := by
    have he : ratio - 1 = (W rp - W rm) / W rm := by dsimp [ratio]; field_simp [hwm0]
    rw [he, norm_div]
    calc
      _ ≤ ((4 * A * F) * (4 * ε / (S * X))) / ‖W rm‖ :=
        div_le_div_of_nonneg_right hdiff hwmn.le
      _ ≤ ((4 * A * F) * (4 * ε / (S * X))) / Wlo :=
        div_le_div_of_nonneg_left (by positivity) hWlo hwm
      _ = _ := by
        dsimp [ε]
        field_simp [hA.ne', hS.ne', hX.ne', hWlo.ne']
        ring
  have hsector : c * (F / X) ≤ gap.re := by
    have hgap := cepsComplexCumulantRootModel_weighted_separation_adm N hM hlo hpκ hv hhi hi
      lam hz hbroot N
    calc
      _ ≤ c * F := mul_le_mul_of_nonneg_left (div_le_self hF hX1) hc.le
      _ ≤ cepsFiniteRootPhaseLower vlo vhi * F := mul_le_mul_of_nonneg_right hcD hF
      _ ≤ _ := hgap
  have hR : 0 ≤ F / X := div_nonneg hF hX.le
  have hR1 : F / X ≤ 1 := (div_le_one hX).mpr hFX
  have hDelta := cepsNormal_delta_lower_bound (η := gap) (P := ratio) (l := 1) (R := F / X)
    (c := c) (C := c / 4) (by norm_num) hR hc hc1 (by positivity) hsector hfactor (by linarith)
  change c / 4 * (F / X) ≤ ‖1 - exp (-gap) * ratio‖
  simpa only [mul_one, Complex.ofReal_one, min_eq_right hR1] using hDelta

theorem cepsComplexKernelDenominatorJetModel_uniform_ne_zero_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d p) N lam z b ≠ 0 := by
  obtain ⟨δd, hδd, hDelta⟩ := cepsComplexKernelJetDelta_uniform_lower_adm d N hM hlo hhi0
  obtain ⟨δg, hδg, hG⟩ := cepsComplexKernelGJetModel_root_uniform_budget_adm d N
    (M := M) (vhi := vhi) hM hlo
  refine ⟨min δd δg, lt_min hδd hδg, ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 0 < X := by dsimp [X]; positivity
  have hF : 0 < F := hz.pos
  have hc : 0 < cepsFiniteComplexDeltaSector vlo vhi := cepsFiniteComplexDeltaSector_pos hlo hhi0
  have hlow := hDelta p hp hv hhi hi lam z b hz (hb.trans (min_le_left _ _))
  have hDelta0 : cepsComplexKernelJetDelta P N lam z b ≠ 0 := norm_pos_iff.mp
    ((mul_pos (div_pos hc (by norm_num)) (div_pos hF hX)).trans_le hlow)
  have hgm := (hG p hp hv hhi lam z b hz
    (hb.trans (min_le_right _ _)) (-1) (Or.inr rfl) N).2.2
  intro hzero
  have he := cepsComplexKernelJetDelta_mul_root_G P N lam z b hgm
  rw [hzero, mul_zero] at he
  exact mul_ne_zero hDelta0 hgm he

theorem cepsComplexKernelDenominatorJetModel_inverse_weighted_budget_adm (d N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖(cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d p) N lam z b)⁻¹‖ ≤
          cepsFiniteComplexSlopeInverseConstant M vlo vhi * (1 + |lam| + Real.sqrt ‖z‖) *
            Real.exp ((cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b *
              (1 + b * lam)).re) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let C := cepsFiniteComplexDeltaSector vlo vhi
  let Wlo := vlo / 4 * Real.exp (-2 * M)
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  have hC : 0 < C := cepsFiniteComplexDeltaSector_pos hlo hhi0
  have hWlo : 0 < Wlo := by dsimp [Wlo]; positivity
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δd, hδd, hDelta⟩ := cepsComplexKernelJetDelta_uniform_lower_adm d N hM hlo hhi0
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget_adm d N
    (M := M) (vhi := vhi) (S := 2 * A) hM hlo
  obtain ⟨δs, hδs, hDen⟩ := cepsComplexKernelDenominatorJetModel_uniform_ne_zero_adm d N hM hlo hhi0
  refine ⟨min δroot (min δd (min δw δs)),
    lt_min hδroot (lt_min hδd (lt_min hδw hδs)), ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let gap := rp - rm
  let Gm := cepsComplexKernelGJetModel P N lam z b rm
  let S := cepsComplexKernelDenominatorJetModel P N lam z b
  let Δ := cepsComplexKernelJetDelta P N lam z b
  have hX : 0 < X := by dsimp [X]; positivity
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hδd' := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδw' := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδs' := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hS0 : S ≠ 0 := hDen p hp hv hhi hi lam z b hz hδs'
  have hF : 0 < F := hz.pos
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hbroot : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hrp : ‖rp‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbroot N).2
  have hrm : ‖rm‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbroot N).2
  have hgap : ‖gap‖ ≤ 4 * A * F := (norm_sub_le _ _).trans (by linarith)
  have hw := hW p hp hv hhi lam z b rm hz hδw'
    (hrm.trans (mul_le_mul_of_nonneg_left hFX (by positivity)))
  have hwm0 := hw.2.2
  have hGm0 : Gm ≠ 0 := by
    dsimp [Gm]
    rw [cepsComplexKernelGJetModel_eq_weight]
    exact mul_ne_zero (exp_ne_zero _) hwm0
  have hΔ : C / 4 * (F / X) ≤ ‖Δ‖ := hDelta p hp hv hhi hi lam z b hz hδd'
  have hlow : 0 < C / 4 * (F / X) := by positivity
  have hΔ0 : Δ ≠ 0 := norm_pos_iff.mp (hlow.trans_le hΔ)
  have hid : Δ * Gm = -gap * S := cepsComplexKernelJetDelta_mul_root_G P N lam z b hGm0
  have he : S⁻¹ = -gap * Δ⁻¹ * Gm⁻¹ := by
    field_simp [hS0, hΔ0, hGm0]
    linear_combination hid
  have hiΔ : ‖Δ⁻¹‖ ≤ (C / 4 * (F / X))⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hlow.trans_le hΔ) hlow).mpr hΔ
  have hgain : ‖gap‖ * ‖Δ⁻¹‖ ≤ 16 * A / C * X := by
    calc
      _ ≤ (4 * A * F) * (C / 4 * (F / X))⁻¹ :=
        mul_le_mul hgap hiΔ (norm_nonneg _) (by positivity)
      _ = _ := by
        field_simp [hC.ne', hF.ne', hX.ne']
        ring
  have hiW : ‖(cepsComplexKernelJetWeight P N lam z b rm)⁻¹‖ ≤ Wlo⁻¹ := by
    rw [norm_inv]
    exact (inv_le_inv₀ (hWlo.trans_le hw.1) hWlo).mpr hw.1
  have hiG : ‖Gm⁻¹‖ ≤ Wlo⁻¹ * Real.exp ((rm * (1 + b * lam)).re) := by
    dsimp [Gm]
    rw [cepsComplexKernelGJetModel_eq_weight, mul_inv, norm_mul, norm_inv,
      norm_exp, neg_mul, neg_re, Real.exp_neg, inv_inv]
    calc
      _ ≤ Real.exp ((rm * (1 + b * lam)).re) * Wlo⁻¹ :=
        mul_le_mul_of_nonneg_left hiW (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  change ‖S⁻¹‖ ≤ cepsFiniteComplexSlopeInverseConstant M vlo vhi * X * _
  rw [he, norm_mul, norm_mul, norm_neg]
  apply (mul_le_mul hgain hiG (norm_nonneg _) (by positivity)).trans
  have hh : 16 * A / C * Wlo⁻¹ ≤ cepsFiniteComplexSlopeInverseConstant M vlo vhi := by
    change 16 * A / C * Wlo⁻¹ ≤ (16 * A / C + 2) / Wlo
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hWlo.le
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hh hX.le) (Real.exp_pos ((rm * (1 + b * lam)).re)).le
  convert hbnd using 1
  ring

end PGM
