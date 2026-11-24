import PLAStochastic.Index.CEPS.Scaled.ComplexJetKernelNormalization
import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientBudget

/-! # Uniform full canonical spatial-weight budgets for arbitrary finite complex vectors -/

noncomputable section
open Complex
namespace PGM

/-- The full canonical spatial weight has a uniform zero-scale approximation on the
original drift-frequency window, with the radius fixed before the finite vector. -/
theorem cepsComplexKernelJetWeight_uniform_zero_budget (d N : ℕ) {M vlo vhi S ε : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b ξ : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        ‖cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ -
          cepsFiniteKernelWeightZero d p‖ ≤ ε := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let L := max M (max 1 (max (2 * A) S))
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δw, hδw, hW⟩ := cepsFiniteKernelWeightAt_uniform_zero_budget d N L hε
  refine ⟨min δroot δw, lt_min hδroot hδw, ?_⟩
  intro p hp hv hhi lam z b ξ hz hb hξ
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hXF : F ≤ X := by dsimp [F, X]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hXn : ‖(X : ℂ)‖ = X := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hX]
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hXF (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖cepsComplexJetPad d p (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hplus := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2.trans
      (mul_le_mul_of_nonneg_left hXF (by positivity : 0 ≤ 2 * A))
  have hminus := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbF N).2.trans
      (mul_le_mul_of_nonneg_left hXF (by positivity : 0 ≤ 2 * A))
  obtain ⟨u, hup, hu, hue⟩ := cepsComplexKernelJetWeight_normalization d N p hp lam z b ξ hplus hminus hξ
  have hbW : ‖(X : ℂ) * b‖ ≤ δw := by
    rw [norm_mul, hXn, mul_comm]
    exact hb.trans (min_le_right _ _)
  have hh := hW ((X : ℂ) * b) u hbW hu
  rw [hup, hue] at hh
  exact hh

theorem cepsFiniteKernelWeightZero_norm_budget {d : ℕ} {p : Fin d → ℂ} {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hp : ‖p‖ ≤ M)
    (hv : vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re)
    (_hlo : 0 ≤ vlo) (hhi : ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi) :
    vlo / 2 * Real.exp (-2 * M) ≤ ‖cepsFiniteKernelWeightZero d p‖ ∧
    ‖cepsFiniteKernelWeightZero d p‖ ≤ vhi / 2 * Real.exp (2 * M) := by
  let χ := cepsComplexJetPad d p (cepsJetCode (.inr (0, 0, 0)))
  have hχ : ‖χ‖ ≤ M := cepsComplexJetPad_norm_le hM hp _
  have hrχ : χ.re ≤ M := (re_le_norm _).trans hχ
  have hlχ : -M ≤ χ.re := by
    have hh := re_le_norm (-χ)
    rw [neg_re, norm_neg] at hh
    linarith
  have hloV := hv.trans (re_le_norm _)
  unfold cepsFiniteKernelWeightZero
  rw [norm_mul, norm_div, norm_ofNat, norm_exp]
  have he : (-2 * cepsComplexJetPad d p (cepsJetCode (.inr (0, 0, 0)))).re = -2 * χ.re := by
    simp [χ, Complex.mul_re]
  rw [he]
  constructor
  · exact mul_le_mul (div_le_div_of_nonneg_right hloV (by norm_num))
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le (by positivity)
  · exact mul_le_mul (div_le_div_of_nonneg_right hhi (by norm_num))
      (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (div_nonneg ((norm_nonneg _).trans hhi) (by norm_num))

theorem cepsComplexKernelJetWeight_uniform_nonzero_budget (d N : ℕ)
    {M vlo vhi S : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b ξ : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖) →
        vlo / 4 * Real.exp (-2 * M) ≤ ‖cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ‖ ∧
        ‖cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ‖ ≤
          vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M) ∧
        cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ ≠ 0 := by
  obtain ⟨δ, hδ, hW⟩ := cepsComplexKernelJetWeight_uniform_zero_budget d N
    (M := M) (vhi := vhi) (S := S) hM hlo (by positivity : 0 < vlo / 4 * Real.exp (-2 * M))
  refine ⟨δ, hδ, ?_⟩
  intro p hp hv hhi lam z b ξ hz hb hξ
  let W := cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ
  let W₀ := cepsFiniteKernelWeightZero d p
  have he : ‖W - W₀‖ ≤ vlo / 4 * Real.exp (-2 * M) := hW p hp hv hhi lam z b ξ hz hb hξ
  have hbase := cepsFiniteKernelWeightZero_norm_budget hM hp hv hlo.le hhi
  have hlow : vlo / 4 * Real.exp (-2 * M) ≤ ‖W‖ := by
    have hh := norm_sub_norm_le W₀ W
    rw [norm_sub_rev] at hh
    linarith [hbase.1]
  have hupp : ‖W‖ ≤ vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M) := by
    have hh := norm_add_le (W - W₀) W₀
    rw [sub_add_cancel] at hh
    linarith [hbase.2]
  exact ⟨hlow, hupp, norm_pos_iff.mp ((by positivity : 0 < vlo / 4 * Real.exp (-2 * M)).trans_le hlow)⟩

end PGM
