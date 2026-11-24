import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotient
import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootHomogeneity
import PLAStochastic.Index.CEPS.Normal.SecondSlopeScaleFactor

/-! # Exact normalized scaling of the finite cumulant spatial unit and quotient -/

noncomputable section
open Complex Set
namespace PGM

theorem quadraticExpUnit_scale (b T c : ℂ) :
    quadraticExpUnit b (c ^ 2 * T) = c ^ 2 * quadraticExpUnit (c * b) T := by
  unfold quadraticExpUnit
  rw [show b ^ 2 * (c ^ 2 * T) = (c * b) ^ 2 * T by ring]
  ring

theorem cepsComplexCumulantQuadraticEquation_homogeneous (p : ℕ → ℂ) (N : ℕ)
    (lam : ℝ) (z b ξ : ℂ) (X : ℝ) :
    cepsComplexCumulantQuadraticEquation p N (X * lam) ((X : ℂ) ^ 2 * z) b ((X : ℂ) * ξ) =
      (X : ℂ) ^ 2 * cepsComplexCumulantQuadraticEquation p N lam z ((X : ℂ) * b) ξ := by
  unfold cepsComplexCumulantQuadraticEquation
  rw [show b * ((X : ℂ) * ξ) = ((X : ℂ) * b) * ξ by ring]
  push_cast
  ring

theorem cepsComplexCumulantQuotientSpatialUnit_homogeneous (p : ℕ → ℂ) (N : ℕ)
    (lam : ℝ) (z b ξ : ℂ) (X : ℝ) :
    cepsComplexCumulantQuotientSpatialUnit p N (X * lam) ((X : ℂ) ^ 2 * z) b ((X : ℂ) * ξ) =
      (X : ℂ) ^ 2 * cepsComplexCumulantQuotientSpatialUnit p N lam z ((X : ℂ) * b) ξ := by
  unfold cepsComplexCumulantQuotientSpatialUnit
  rw [cepsComplexCumulantQuadraticEquation_homogeneous, quadraticExpUnit_scale]

/-- The second spatial divided difference exactly cancels the quadratic normalization,
including coincident nodes. No root-chart or nonzero-frequency premise is required. -/
theorem cepsComplexCumulantQuotientSpatialUnit_second_slope_homogeneous
    (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b a d ξ : ℂ) {X : ℝ} (hX : 0 < X) :
    dslope (dslope
      (cepsComplexCumulantQuotientSpatialUnit p N (X * lam) ((X : ℂ) ^ 2 * z) b)
        ((X : ℂ) * a)) ((X : ℂ) * d) ((X : ℂ) * ξ) =
    dslope (dslope (cepsComplexCumulantQuotientSpatialUnit p N lam z ((X : ℂ) * b)) a) d ξ := by
  have hf := cepsComplexCumulantQuotientSpatialUnit_differentiable p N (X * lam) ((X : ℂ) ^ 2 * z) b
  have hg := cepsComplexCumulantQuotientSpatialUnit_differentiable p N lam z ((X : ℂ) * b)
  have hd : Differentiable ℂ (dslope
      (cepsComplexCumulantQuotientSpatialUnit p N (X * lam) ((X : ℂ) ^ 2 * z) b) ((X : ℂ) * a)) := by
    have hh := (differentiableOn_dslope (s := univ) (c := (X : ℂ) * a) Filter.univ_mem).mpr hf.differentiableOn
    exact fun t => (hh t (mem_univ t)).differentiableAt Filter.univ_mem
  exact cepsNormal_second_dslope_scale_factor (by exact_mod_cast hX.ne') isOpen_univ
    hg.differentiableOn (fun ξ _ => cepsComplexCumulantQuotientSpatialUnit_homogeneous p N lam z b ξ X)
    (mem_univ a) (mem_univ d) (mem_univ ξ) (hf _) (hd _)

theorem cepsComplexCumulantJetQuotient_homogeneous (p : ℕ → ℂ) (N : ℕ) (lam : ℝ)
    (z b ξ : ℂ) {X : ℝ} (hX : 0 < X) :
    cepsComplexCumulantJetQuotient p N (X * lam) ((X : ℂ) ^ 2 * z) b ((X : ℂ) * ξ) =
      cepsComplexCumulantJetQuotient p N lam z ((X : ℂ) * b) ξ := by
  unfold cepsComplexCumulantJetQuotient
  rw [cepsComplexCumulantRootModel_homogeneous p N lam z 1 hX N b,
    cepsComplexCumulantRootModel_homogeneous p N lam z (-1) hX N b]
  exact cepsComplexCumulantQuotientSpatialUnit_second_slope_homogeneous p N lam z b _ _ ξ hX

end PGM
