import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightBudget
import PLAStochastic.Index.CEPS.Normal.FirstSlopeError

/-! # Genuine spatial Cauchy slope budgets for the full finite canonical weight -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsComplexKernelJetWeight_spatial_differentiable (p : ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b : ℂ) : Differentiable ℂ (cepsComplexKernelJetWeight p N lam z b) := by
  let w : ℂ := 1 + b * lam
  have he : (fun ξ : ℂ => exp (ξ * w) * cepsComplexKernelGJetModel p N lam z b ξ) =
      cepsComplexKernelJetWeight p N lam z b := by
    funext ξ
    rw [cepsComplexKernelGJetModel_eq_weight, ← mul_assoc, ← exp_add,
      show ξ * w + -ξ * (1 + b * lam) = 0 by dsimp [w]; ring, exp_zero, one_mul]
  rw [← he]
  exact ((differentiable_id.mul_const w).cexp).mul
    (cepsComplexKernelGJetModel_spatial_differentiable p N lam z b)

def cepsFiniteWeightSpatialWindow (vlo : ℝ) : ℝ := 8 * cepsFiniteQuadraticRootBound vlo + 8

theorem cepsFiniteWeightSpatialWindow_pos {vlo : ℝ} (hlo : 0 < vlo) :
    0 < cepsFiniteWeightSpatialWindow vlo := by
  have hA := cepsFiniteQuadraticRootBound_pos hlo
  unfold cepsFiniteWeightSpatialWindow
  positivity

/-- A single scale radius makes the true spatial first slope of the full canonical weight
arbitrarily small, uniformly over the complex vector and all drift-frequency root nodes. -/
theorem cepsComplexKernelJetWeight_root_slope_uniform_budget (d N : ℕ) {M vlo vhi ε : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖dslope (cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b)
          (cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b)
          (cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b)‖ ≤
          4 * ε / (cepsFiniteWeightSpatialWindow vlo * (1 + |lam| + Real.sqrt ‖z‖)) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let S := cepsFiniteWeightSpatialWindow vlo
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  have hS : 0 < S := cepsFiniteWeightSpatialWindow_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_zero_budget d N
    (M := M) (vhi := vhi) (S := S) hM hlo hε
  refine ⟨min δroot δw, lt_min hδroot hδw, ?_⟩
  intro p hp hv hhi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := S * X
  let W := cepsComplexKernelJetWeight P N lam z b
  let W₀ := cepsFiniteKernelWeightZero d p
  let a := cepsComplexCumulantRootModel P N lam z (-1) N b
  let t := cepsComplexCumulantRootModel P N lam z 1 N b
  have hXF : F ≤ X := by dsimp [F, X]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hR : 0 < R := mul_pos hS hX
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hXF (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have ha : ‖a‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbF N).2
  have ht : ‖t‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2
  have hnodes : 2 * A * F < R / 2 := by
    have hh := mul_le_mul_of_nonneg_left hXF (by positivity : 0 ≤ 2 * A)
    dsimp [R, S, cepsFiniteWeightSpatialWindow]
    nlinarith
  have hbound : ∀ ξ ∈ ball (0 : ℂ) R, ‖W ξ - W₀‖ ≤ ε := by
    intro ξ hξ
    exact hW p hp hv hhi lam z b ξ hz (hb.trans (min_le_right _ _))
      (mem_ball_zero_iff.mp hξ).le
  have hd := cepsComplexKernelJetWeight_spatial_differentiable P N lam z b
  have hs := cepsNormal_norm_dslope_sub_le_of_bound hR hd.differentiableOn
    (differentiable_const W₀).differentiableOn hbound
    (mem_ball_zero_iff.mpr (ha.trans_lt hnodes)) (mem_ball_zero_iff.mpr (ht.trans_lt hnodes))
  have hconst : dslope (fun _ : ℂ => W₀) a t = 0 := by
    by_cases hta : t = a
    · rw [hta, dslope_same]
      exact deriv_const a W₀
    · rw [dslope_of_ne _ hta, slope_def_field, sub_self, zero_div]
  rw [hconst, sub_zero] at hs
  exact hs

end PGM
