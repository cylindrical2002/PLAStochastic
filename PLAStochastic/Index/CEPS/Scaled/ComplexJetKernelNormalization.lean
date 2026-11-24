import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightCompact
import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuotientHomogeneity

/-! # Exact bounded-parameter normalization of the full finite canonical spatial weight -/

noncomputable section
open Complex
namespace PGM

/-- Root norm budgets, separately paid by uniform finite Newton stability, put the original
canonical spatial weight into one bounded finite-vector and independent-node parameter set. -/
theorem cepsComplexKernelJetWeight_normalization (d N : ℕ) (p : Fin d → ℂ)
    {M C S : ℝ} (hp : ‖p‖ ≤ M) (lam : ℝ) (z b ξ : ℂ)
    (hplus : ‖cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b‖ ≤
      C * (1 + |lam| + Real.sqrt ‖z‖))
    (hminus : ‖cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b‖ ≤
      C * (1 + |lam| + Real.sqrt ‖z‖))
    (hξ : ‖ξ‖ ≤ S * (1 + |lam| + Real.sqrt ‖z‖)) :
    ∃ u : CepsFiniteQuotientParams d, u.1 = p ∧ ‖u‖ ≤ max M (max 1 (max C S)) ∧
      cepsFiniteKernelWeightAt d N (((1 + |lam| + Real.sqrt ‖z‖ : ℝ) : ℂ) * b) u =
        cepsComplexKernelJetWeight (cepsComplexJetPad d p) N lam z b ξ := by
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + F
  let L := max M (max 1 (max C S))
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hX : 0 < X := by dsimp [X]; linarith
  have hXF : F ≤ X := by dsimp [X]; linarith
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hXn : ‖(X : ℂ)‖ = X := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hX]
  let a := cepsComplexCumulantRootModel P N lam z 1 N b / (X : ℂ)
  let e := cepsComplexCumulantRootModel P N lam z (-1) N b / (X : ℂ)
  let t := ξ / (X : ℂ)
  have ha : ‖a‖ ≤ C := by
    dsimp [a]
    rw [norm_div, hXn, div_le_iff₀ hX]
    simpa only [X, F, add_assoc] using hplus
  have he : ‖e‖ ≤ C := by
    dsimp [e]
    rw [norm_div, hXn, div_le_iff₀ hX]
    simpa only [X, F, add_assoc] using hminus
  have ht : ‖t‖ ≤ S := by
    dsimp [t]
    rw [norm_div, hXn, div_le_iff₀ hX]
    simpa only [X, F, add_assoc] using hξ
  have hl : ‖lam / X‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hX, div_le_one hX]
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg ‖z‖)).trans hXF
  have hzF : ‖z‖ ≤ F ^ 2 := by
    calc
      _ = Real.sqrt ‖z‖ ^ 2 := (Real.sq_sqrt (norm_nonneg z)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_add_of_nonneg_left (abs_nonneg lam)) 2
  have hzX : ‖z / (X : ℂ) ^ 2‖ ≤ (1 : ℝ) := by
    rw [norm_div, norm_pow, hXn, div_le_one (pow_pos hX 2)]
    exact hzF.trans (pow_le_pow_left₀ hF hXF 2)
  let u : CepsFiniteQuotientParams d := (p, lam / X, z / (X : ℂ) ^ 2, a, e, t)
  have hu : ‖u‖ ≤ L := by
    have hML : M ≤ L := le_max_left _ _
    have h1L : 1 ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    have hCL : C ≤ L := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    have hSL : S ≤ L := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    dsimp only [u]
    simp only [Prod.norm_def, max_le_iff]
    exact ⟨hp.trans hML, hl.trans h1L, hzX.trans h1L, ha.trans hCL, he.trans hCL, ht.trans hSL⟩
  refine ⟨u, rfl, hu, ?_⟩
  have hLam : X * (lam / X) = lam := mul_div_cancel₀ lam hX.ne'
  have hZ : (X : ℂ) ^ 2 * (z / (X : ℂ) ^ 2) = z := mul_div_cancel₀ z (pow_ne_zero 2 hXc)
  have hnode (w : ℂ) : (X : ℂ) * (w / (X : ℂ)) = w := mul_div_cancel₀ w hXc
  have hscale := cepsComplexCumulantQuotientSpatialUnit_second_slope_homogeneous P N
    (lam / X) (z / (X : ℂ) ^ 2) b a e t hX
  rw [hLam, hZ] at hscale
  dsimp only [a, e, t] at hscale
  rw [hnode, hnode, hnode] at hscale
  have hQ : cepsComplexCumulantJetQuotient P N lam z b ξ = cepsFiniteQuotientAt d N ((X : ℂ) * b) u := hscale
  have hMu : ((X : ℂ) * b) * ((lam / X : ℝ) : ℂ) = b * lam := by
    push_cast
    field_simp [hXc]
  have hDiscount : cepsComplexScaledDiscount (lam / X) (z / (X : ℂ) ^ 2) ((X : ℂ) * b) =
      cepsComplexScaledDiscount lam z b := by
    unfold cepsComplexScaledDiscount
    push_cast
    field_simp [hXc]
  have hXi : ((X : ℂ) * b) * t = b * ξ := by
    dsimp [t]
    field_simp [hXc]
  have hbX : (((1 + |lam| + Real.sqrt ‖z‖ : ℝ) : ℂ) * b) = (X : ℂ) * b := by
    congr 2
    dsimp [X, F]
    ring
  rw [hbX]
  unfold cepsFiniteKernelWeightAt cepsComplexKernelJetWeight
  rw [hQ]
  dsimp only [u]
  rw [hMu, hDiscount, hXi]

end PGM
