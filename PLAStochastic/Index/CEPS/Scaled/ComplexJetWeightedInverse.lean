import PLAStochastic.Index.CEPS.Scaled.ComplexJetDenominatorUniform

/-! # The genuine finite-vector denominator inverse retains its lower-root weight -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteComplexSlopeInverseConstant (M vlo vhi : ℝ) : ℝ :=
  (16 * cepsFiniteQuadraticRootBound vlo / cepsFiniteComplexDeltaSector vlo vhi + 2) /
    (vlo / 4 * Real.exp (-2 * M))

theorem cepsFiniteComplexSlopeInverseConstant_pos {M vlo vhi : ℝ}
    (hlo : 0 < vlo) (hhi : 0 < vhi) :
    0 < cepsFiniteComplexSlopeInverseConstant M vlo vhi := by
  have := cepsFiniteQuadraticRootBound_pos hlo
  have := cepsFiniteComplexDeltaSector_pos hlo hhi
  unfold cepsFiniteComplexSlopeInverseConstant
  positivity

/-- The common radius is chosen before the finite vector and the entire drift-frequency
window. The reciprocal keeps the exact lower-root exponential, including the joint origin. -/
theorem cepsComplexKernelDenominatorJetModel_inverse_weighted_budget (d N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
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
  obtain ⟨δd, hδd, hDelta⟩ := cepsComplexKernelJetDelta_uniform_lower d N hM hlo hhi0
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget d N
    (M := M) (vhi := vhi) (S := 2 * A) hM hlo
  obtain ⟨δo, hδo, hOrigin⟩ := cepsComplexKernelDenominatorJetModel_origin_uniform_lower d N
    (M := M) (vhi := vhi) hM hlo
  obtain ⟨δs, hδs, hDen⟩ := cepsComplexKernelDenominatorJetModel_uniform_ne_zero d N hM hlo hhi0
  refine ⟨min δroot (min δd (min δw (min δo δs))),
    lt_min hδroot (lt_min hδd (lt_min hδw (lt_min hδo hδs))), ?_⟩
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
  have hδo' := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hδs' := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  have hS0 : S ≠ 0 := hDen p hp hv hhi hi lam z b hz hδs'
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · have hF : 0 < F := by
      rcases hne with hl | hz0
      · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hl) (Real.sqrt_nonneg _)
      · exact add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hz0))
    have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
      fun j _ => cepsComplexJetPad_norm_le hM hp _
    have hbroot : ‖b‖ * F ≤ δroot :=
      (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
    have hrp : ‖rp‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
      (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbroot N).2
    have hrm : ‖rm‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
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
  · push Not at hne
    obtain ⟨hlam, hz0⟩ := hne
    subst lam
    subst z
    have hb0 : ‖b‖ ≤ δo := by simpa using hδo'
    have hlow := (hOrigin p hp hv hhi b hb0).1
    have hlo' : Wlo / 2 ≤ ‖cepsComplexKernelDenominatorJetModel P N 0 0 b‖ := by
      convert hlow using 1
      dsimp [Wlo]
      ring
    have hinv' : ‖(cepsComplexKernelDenominatorJetModel P N 0 0 b)⁻¹‖ ≤ 2 / Wlo := by
      rw [norm_inv]
      exact ((inv_le_inv₀ ((by positivity : 0 < Wlo / 2).trans_le hlo')
        (by positivity : 0 < Wlo / 2)).mpr hlo').trans_eq (by ring)
    simp only [cepsComplexCumulantRootModel_joint_zero, zero_mul, zero_re, Real.exp_zero,
      abs_zero, norm_zero, Real.sqrt_zero, add_zero, mul_one]
    apply hinv'.trans
    change 2 / Wlo ≤ (16 * A / C + 2) / Wlo
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) hWlo.le

end PGM
