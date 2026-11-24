import PLAStochastic.Index.CEPS.Scaled.ComplexJetDeltaBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootKernelBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetDenominatorOrigin

/-! # A common finite complex-vector nonzero divided denominator through the joint origin -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexKernelJetDelta_eq_root_ratio (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) :
    cepsComplexKernelJetDelta p N lam z b = 1 -
      cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z 1 N b) /
      cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z (-1) N b) := by
  unfold cepsComplexKernelJetDelta
  rw [cepsComplexKernelGJetModel_eq_weight, cepsComplexKernelGJetModel_eq_weight,
    mul_div_mul_comm, ← exp_sub]
  congr 2
  ring

theorem cepsComplexKernelJetDelta_mul_root_G (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ)
    (hgm : cepsComplexKernelGJetModel p N lam z b
      (cepsComplexCumulantRootModel p N lam z (-1) N b) ≠ 0) :
    cepsComplexKernelJetDelta p N lam z b *
      cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z (-1) N b) =
      -(cepsComplexCumulantRootModel p N lam z 1 N b - cepsComplexCumulantRootModel p N lam z (-1) N b) *
        cepsComplexKernelDenominatorJetModel p N lam z b := by
  rw [cepsComplexKernelJetDelta_eq_root_ratio]
  unfold cepsComplexKernelDenominatorJetModel
  have he := sub_smul_dslope (cepsComplexKernelGJetModel p N lam z b)
    (cepsComplexCumulantRootModel p N lam z (-1) N b) (cepsComplexCumulantRootModel p N lam z 1 N b)
  rw [smul_eq_mul] at he
  field_simp [hgm]
  linear_combination he

/-- The same positive radius pays the genuine divided denominator for every finite vector
in a narrow variance region and every right-half-plane frequency, including both zero roots. -/
theorem cepsComplexKernelDenominatorJetModel_uniform_ne_zero (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        cepsComplexKernelDenominatorJetModel (cepsComplexJetPad d p) N lam z b ≠ 0 := by
  obtain ⟨δd, hδd, hDelta⟩ := cepsComplexKernelJetDelta_uniform_lower d N hM hlo hhi0
  obtain ⟨δg, hδg, hG⟩ := cepsComplexKernelGJetModel_root_uniform_budget d N
    (M := M) (vhi := vhi) hM hlo
  obtain ⟨δo, hδo, hOrigin⟩ := cepsComplexKernelDenominatorJetModel_origin_uniform_lower d N
    (M := M) (vhi := vhi) hM hlo
  refine ⟨min δd (min δg δo), lt_min hδd (lt_min hδg hδo), ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 0 < X := by dsimp [X]; positivity
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · have hF : 0 < F := by
      rcases hne with hl | hz0
      · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hl) (Real.sqrt_nonneg _)
      · exact add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hz0))
    have hc : 0 < cepsFiniteComplexDeltaSector vlo vhi := cepsFiniteComplexDeltaSector_pos hlo hhi0
    have hlow := hDelta p hp hv hhi hi lam z b hz (hb.trans (min_le_left _ _))
    have hDelta0 : cepsComplexKernelJetDelta P N lam z b ≠ 0 := norm_pos_iff.mp
      ((mul_pos (div_pos hc (by norm_num)) (div_pos hF hX)).trans_le hlow)
    have hgm := (hG p hp hv hhi lam z b hz
      (hb.trans ((min_le_right _ _).trans (min_le_left _ _))) (-1) (Or.inr rfl) N).2.2
    intro hzero
    have he := cepsComplexKernelJetDelta_mul_root_G P N lam z b hgm
    rw [hzero, mul_zero] at he
    exact mul_ne_zero hDelta0 hgm he
  · push Not at hne
    obtain ⟨hlam, hz0⟩ := hne
    subst lam
    subst z
    have hb0 : ‖b‖ ≤ δo := by
      have hh := hb.trans ((min_le_right _ _).trans (min_le_right _ _))
      simpa using hh
    exact (hOrigin p hp hv hhi b hb0).2

end PGM
