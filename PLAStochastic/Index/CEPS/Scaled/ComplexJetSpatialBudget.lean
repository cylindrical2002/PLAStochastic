import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightSpatial
import PLAStochastic.ForMathlib.Analysis.Complex.TaylorDisc

/-! # Entire spatial derivatives preserve the exact endpoint exponential weight -/

noncomputable section
open Complex Set Metric
namespace PGM

def cepsFiniteComplexSpatialConstant (n : ℕ) (M vlo vhi : ℝ) : ℝ :=
  (n.factorial : ℝ) * (Real.exp 2 *
    (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M))) / (1 / 2 : ℝ) ^ n

theorem cepsComplexKernelGJetModel_spatial_uniform_budget (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ∀ (n : ℕ) (ξ : ℂ),
          ‖ξ‖ ≤ cepsFiniteWeightSpatialWindow vlo * (1 + |lam| + Real.sqrt ‖z‖) / 2 →
          ‖iteratedDeriv n (cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b) ξ‖ ≤
            cepsFiniteComplexSpatialConstant n M vlo vhi *
              Real.exp (-(ξ * (1 + b * lam)).re) := by
  let S := cepsFiniteWeightSpatialWindow vlo
  let H := vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)
  have hH : 0 < H := by dsimp [H]; positivity
  have hA := cepsFiniteQuadraticRootBound_pos hlo
  have hS : 2 ≤ S := by dsimp [S, cepsFiniteWeightSpatialWindow]; linarith
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget d N
    (M := M) (vhi := vhi) (S := S) hM hlo
  refine ⟨min 1 δw, lt_min one_pos hδw, ?_⟩
  intro p hp hv hhi lam z b hz hb n ξ hξ
  let P := cepsComplexJetPad d p
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := S * X
  let G := cepsComplexKernelGJetModel P N lam z b
  let w : ℂ := 1 + b * lam
  have hX : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hR : 2 ≤ R := by dsimp [R]; nlinarith
  have hLam : |lam| ≤ X := by dsimp [X]; linarith [Real.sqrt_nonneg ‖z‖]
  have hμ : ‖b * (lam : ℂ)‖ ≤ 1 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hLam (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hw : ‖w‖ ≤ 2 := (norm_add_le _ _).trans (by rw [norm_one]; linarith)
  have hsub : ball ξ (1 : ℝ) ⊆ ball (0 : ℂ) R := by
    intro ζ hζ
    have hn := norm_add_le (ζ - ξ) ξ
    rw [sub_add_cancel] at hn
    have hz1 : ‖ζ - ξ‖ < 1 := by simpa only [dist_eq_norm] using mem_ball.mp hζ
    exact mem_ball_zero_iff.mpr (by linarith)
  have hm : ∀ ζ ∈ ball ξ (1 : ℝ), ‖G ζ‖ ≤ Real.exp (-(ξ * w).re) * (Real.exp 2 * H) := by
    intro ζ hζ
    have hweight : ‖cepsComplexKernelJetWeight P N lam z b ζ‖ ≤ H :=
      (hW p hp hv hhi lam z b ζ hz (hb.trans (min_le_right _ _))
        (mem_ball_zero_iff.mp (hsub hζ)).le).2.1
    have hExp : ‖exp (-(ζ - ξ) * w)‖ ≤ Real.exp 2 := by
      rw [norm_exp]
      apply Real.exp_le_exp.mpr
      have hr := re_le_norm (-(ζ - ξ) * w)
      rw [norm_mul, norm_neg] at hr
      have hz1 : ‖ζ - ξ‖ ≤ 1 := by simpa only [dist_eq_norm] using (mem_ball.mp hζ).le
      exact hr.trans (by nlinarith [norm_nonneg (ζ - ξ)])
    have he : -ζ * w = -ξ * w + -(ζ - ξ) * w := by ring
    change ‖cepsComplexKernelGJetModel P N lam z b ζ‖ ≤ _
    rw [cepsComplexKernelGJetModel_eq_weight]
    change ‖exp (-ζ * w) * cepsComplexKernelJetWeight P N lam z b ζ‖ ≤ _
    rw [he, exp_add, norm_mul, norm_mul]
    apply (mul_le_mul (mul_le_mul_of_nonneg_left hExp (norm_nonneg _)) hweight
      (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)).trans_eq
    rw [norm_exp, neg_mul, neg_re]
    ring
  have hd : DifferentiableOn ℂ G (ball ξ (1 : ℝ)) :=
    (cepsComplexKernelGJetModel_spatial_differentiable P N lam z b).differentiableOn
  have h := norm_iteratedDeriv_le_of_ball n (by norm_num : (0 : ℝ) < 1) hd hm
  apply h.trans_eq
  dsimp [cepsFiniteComplexSpatialConstant, H]
  ring

end PGM
