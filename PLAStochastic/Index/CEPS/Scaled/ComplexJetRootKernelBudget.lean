import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightBudget

/-! # Common full spatial-kernel budgets at all finite Newton root iterates -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexKernelGJetModel_root_uniform_budget (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ∀ (sign : ℂ), sign = 1 ∨ sign = -1 → ∀ k : ℕ,
          let r := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z sign k b
          vlo / 4 * Real.exp (-2 * M) * Real.exp (-(r * (1 + b * lam)).re) ≤
            ‖cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b r‖ ∧
          ‖cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b r‖ ≤
            (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) *
              Real.exp (-(r * (1 + b * lam)).re) ∧
          cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b r ≠ 0 := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget d N
    (M := M) (vhi := vhi) (S := 2 * A) hM hlo
  refine ⟨min δroot δw, lt_min hδroot hδw, ?_⟩
  intro p hp hv hhi lam z b hz hb sign hsign k
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let r := cepsComplexCumulantRootModel P N lam z sign k b
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hr : ‖r‖ ≤ 2 * A * X := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    hsign hbF k).2.trans (mul_le_mul_of_nonneg_left hFX (by positivity))
  have hw := hW p hp hv hhi lam z b r hz (hb.trans (min_le_right _ _)) hr
  change _ ∧ _ ∧ cepsComplexKernelGJetModel P N lam z b r ≠ 0
  have hn : ‖cepsComplexKernelGJetModel P N lam z b r‖ =
      Real.exp (-(r * (1 + b * lam)).re) * ‖cepsComplexKernelJetWeight P N lam z b r‖ := by
    rw [cepsComplexKernelGJetModel_eq_weight, norm_mul, norm_exp, neg_mul, neg_re]
  refine ⟨?_, ?_, ?_⟩
  · rw [hn]
    calc
      _ ≤ ‖cepsComplexKernelJetWeight P N lam z b r‖ * Real.exp (-(r * (1 + b * lam)).re) :=
        mul_le_mul_of_nonneg_right hw.1 (Real.exp_pos _).le
      _ = _ := mul_comm _ _
  · rw [hn]
    calc
      _ = ‖cepsComplexKernelJetWeight P N lam z b r‖ * Real.exp (-(r * (1 + b * lam)).re) := mul_comm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hw.2.1 (Real.exp_pos _).le
  · rw [cepsComplexKernelGJetModel_eq_weight]
    exact mul_ne_zero (exp_ne_zero _) hw.2.2

end PGM
