import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightSpatial
import PLAStochastic.Index.CEPS.Scaled.ComplexJetFactors

/-! # The genuine finite-jet divided denominator at the joint origin -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexKernelDenominatorJetModel_origin (p : ℕ → ℂ) (N : ℕ) (b : ℂ) :
    cepsComplexKernelDenominatorJetModel p N 0 0 b =
      -cepsComplexKernelJetWeight p N 0 0 b 0 + deriv (cepsComplexKernelJetWeight p N 0 0 b) 0 := by
  unfold cepsComplexKernelDenominatorJetModel
  rw [cepsComplexCumulantRootModel_joint_zero, cepsComplexCumulantRootModel_joint_zero, dslope_same]
  let W := cepsComplexKernelJetWeight p N 0 0 b
  have he : cepsComplexKernelGJetModel p N 0 0 b = fun ξ : ℂ => exp (-ξ) * W ξ := by
    funext ξ
    rw [cepsComplexKernelGJetModel_eq_weight]
    simp [W]
  have hdE : HasDerivAt (fun ξ : ℂ => exp (-ξ)) (-1) 0 := by
    simpa only [Pi.neg_apply, id_eq, neg_zero, exp_zero, one_mul] using! ((hasDerivAt_id (0 : ℂ)).neg.cexp)
  have hdW := (cepsComplexKernelJetWeight_spatial_differentiable p N 0 0 b 0).hasDerivAt
  rw [he]
  simpa only [neg_zero, exp_zero, neg_one_mul, one_mul] using! (hdE.mul hdW).deriv

/-- A common finite-vector scale radius pays a strictly positive lower bound at the
coincident zero roots, using the actual derivative value of the spatial divided slope. -/
theorem cepsComplexKernelDenominatorJetModel_origin_uniform_lower (d N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ b : ℂ, ‖b‖ ≤ δ →
        vlo / 8 * Real.exp (-2 * M) ≤
          ‖cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d p) N 0 0 b‖ ∧
        cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d p) N 0 0 b ≠ 0 := by
  let S := cepsFiniteWeightSpatialWindow vlo
  let Wlo := vlo / 4 * Real.exp (-2 * M)
  let ε := Wlo * S / 16
  have hS : 0 < S := cepsFiniteWeightSpatialWindow_pos hlo
  have hWlo : 0 < Wlo := by dsimp [Wlo]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget d N
    (M := M) (vhi := vhi) (S := S) hM hlo
  obtain ⟨δs, hδs, hSlope⟩ := cepsComplexKernelJetWeight_root_slope_uniform_budget d N
    (M := M) (vhi := vhi) hM hlo hε
  refine ⟨min δw δs, lt_min hδw hδs, ?_⟩
  intro p hp hv hhi b hb
  let P := cepsComplexJetPad d p
  let W := cepsComplexKernelJetWeight P N 0 0 b
  have hw : Wlo ≤ ‖W 0‖ := (hW p hp hv hhi 0 0 b 0 (by simp)
    (by simpa using hb.trans (min_le_left _ _)) (by simpa using hS.le)).1
  have hs := hSlope p hp hv hhi 0 0 b (by simp) (by simpa using hb.trans (min_le_right _ _))
  simp only [cepsComplexCumulantRootModel_joint_zero, dslope_same, abs_zero,
    norm_zero, Real.sqrt_zero, add_zero, mul_one] at hs
  have hd : ‖deriv W 0‖ ≤ Wlo / 4 := hs.trans_eq (by
    dsimp [ε]
    change 4 * (Wlo * S / 16) / S = Wlo / 4
    field_simp [hS.ne']
    ring)
  have he : ‖cepsComplexKernelDenominatorJetModel P N 0 0 b‖ = ‖W 0 - deriv W 0‖ := by
    rw [cepsComplexKernelDenominatorJetModel_origin,
      show -W 0 + deriv W 0 = -(W 0 - deriv W 0) by ring, norm_neg]
  have hlow : vlo / 8 * Real.exp (-2 * M) ≤ ‖cepsComplexKernelDenominatorJetModel P N 0 0 b‖ := by
    rw [he]
    have hh := norm_sub_norm_le (W 0) (deriv W 0)
    have ht : vlo / 8 * Real.exp (-2 * M) = Wlo / 2 := by dsimp [Wlo]; ring
    rw [ht]
    linarith only [hw, hd, hh, hWlo]
  exact ⟨hlow, norm_pos_iff.mp ((by positivity : 0 < vlo / 8 * Real.exp (-2 * M)).trans_le hlow)⟩

end PGM
