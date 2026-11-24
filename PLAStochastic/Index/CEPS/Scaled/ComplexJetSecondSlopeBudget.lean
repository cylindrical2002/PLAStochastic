import PLAStochastic.Index.CEPS.Scaled.ComplexJetFactors
import PLAStochastic.Index.CEPS.Scaled.ComplexJetSpatialBudget
import PLAStochastic.Index.CEPS.Scaled.WeightedSlopeBudget

/-! # Uniform actual entrance divided slopes with all three endpoint weights -/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsFiniteComplexSpatialConstant_pos (n : ℕ) {M vlo vhi : ℝ}
    (hlo : 0 < vlo) (hhi : 0 < vhi) :
    0 < cepsFiniteComplexSpatialConstant n M vlo vhi := by
  have hf : 0 < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  unfold cepsFiniteComplexSpatialConstant
  positivity

/-- The true second divided slope, including every root-marker collision, retains each
endpoint exponential. Constants precede arbitrary finite vectors and the full frequency window. -/
theorem cepsComplexKernelEntranceSlopeJetModel_uniform_budget (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖cepsComplexKernelEntranceSlopeJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          cepsFiniteComplexSpatialConstant 2 M vlo vhi *
            (Real.exp (-(cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b * (1 + b * lam)).re) +
              Real.exp (-(cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b * (1 + b * lam)).re) +
                Real.exp (-((b * z) * (1 + b * lam)).re)) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let S := cepsFiniteWeightSpatialWindow vlo
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δs, hδs, hSpatial⟩ := cepsComplexKernelGJetModel_spatial_uniform_budget d N hM hlo hhi0
  refine ⟨min 1 (min δroot δs), lt_min one_pos (lt_min hδroot hδs), ?_⟩
  intro p hp hv hhi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := S * X
  let G := cepsComplexKernelGJetModel P N lam z b
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  have hX : 0 < X := by dsimp [X]; positivity
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hR : 0 < R := mul_pos (cepsFiniteWeightSpatialWindow_pos hlo) hX
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hbR : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans
      (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hn : 2 * A * F ≤ R / 2 := by
    have hh := mul_le_mul_of_nonneg_left hFX (by positivity : 0 ≤ 2 * A)
    dsimp [R, S, cepsFiniteWeightSpatialWindow]
    nlinarith
  have hrp : ‖rp‖ ≤ R / 2 := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbR N).2.trans hn
  have hrm : ‖rm‖ ≤ R / 2 := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbR N).2.trans hn
  have hmark : ‖b * z‖ ≤ R / 2 := by
    have hsX : Real.sqrt ‖z‖ ≤ X := by dsimp [X]; linarith [abs_nonneg lam]
    have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hsX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
    have hnz := mul_le_mul_of_nonneg_right hbs (Real.sqrt_nonneg ‖z‖)
    rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg z), one_mul] at hnz
    rw [norm_mul]
    have hRX : X ≤ R / 2 := by dsimp [R, S, cepsFiniteWeightSpatialWindow]; nlinarith
    exact hnz.trans (hsX.trans hRX)
  have hd : DifferentiableOn ℂ G (ball 0 R) :=
    (cepsComplexKernelGJetModel_spatial_differentiable P N lam z b).differentiableOn
  have hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ‖deriv (deriv G) ξ‖ ≤
      cepsFiniteComplexSpatialConstant 2 M vlo vhi * Real.exp (-(ξ * (1 + b * lam)).re) := by
    intro ξ hξ
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hSpatial p hp hv hhi lam z b hz
        (hb.trans ((min_le_right _ _).trans (min_le_right _ _))) 2 ξ hξ
  exact cepsNormal_norm_second_dslope_le_weighted hR
    (cepsFiniteComplexSpatialConstant_pos 2 hlo hhi0).le hd hderiv hrm hrp hmark

end PGM
