import PLAStochastic.Index.CEPS.Scaled.ComplexJetBridgeWeighted

/-! # Drift-integrable exponential budgets for the genuine finite-vector subtracted bridge -/

noncomputable section
open Complex
namespace PGM

def cepsComplexKernelSubtractedBridgeJetModel (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  cepsComplexKernelBridgeJetModel p N lam z b -
    if 1 ≤ lam then cepsComplexKernelHalfBridgeJetModel p N lam z b else 0

/-- Constants precede all finite complex vectors, drifts and right-half-plane frequencies.
The subtraction uses the original fixed positive-drift threshold. -/
theorem cepsComplexKernelSubtractedBridgeJetModel_uniform_decay (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ K c : ℝ, 0 < δ ∧ 0 < K ∧ 0 < c ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖cepsComplexKernelSubtractedBridgeJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          K * (1 + |lam| + Real.sqrt ‖z‖) * Real.exp (-c * (|lam| + Real.sqrt ‖z‖)) := by
  let D := cepsFiniteRootPhaseLower vlo vhi
  let B := cepsFiniteComplexBridgeConstant M vlo vhi
  have hD : 0 < D := by
    have := cepsFiniteQuadraticGapLower_pos (vhi := vhi) hlo
    dsimp [D, cepsFiniteRootPhaseLower]
    positivity
  have hB : 0 < B := cepsFiniteComplexBridgeConstant_pos hlo hhi0
  have hK : 0 < B * (1 + Real.exp (1 / vlo)) := by positivity
  have hR := cepsFiniteWeightedRootRadius_pos N hM hlo hhi0
  obtain ⟨δb, hδb, hBridge⟩ := cepsComplexKernelBridgeJetModel_weighted_budget d N hM hlo hhi0
  refine ⟨min δb (cepsFiniteWeightedRootRadius N M vlo vhi), B * (1 + Real.exp (1 / vlo)), D / 2,
    lt_min hδb hR, hK, by positivity, ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hX : 0 < X := by dsimp [X]; positivity
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hbR : ‖b‖ * F ≤ cepsFiniteWeightedRootRadius N M vlo vhi :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_right _ _))
  have hBudget := hBridge p hp hv hhi hi lam z b hz (hb.trans (min_le_left _ _))
  by_cases hl : 1 ≤ lam
  · have hphase := cepsComplexCumulantRootModel_positive_correction_sector N hM hlo hpκ hv hhi hi
      (le_trans (by norm_num) hl) hz hbR N
    rw [cepsComplexKernelSubtractedBridgeJetModel, if_pos hl]
    apply hBudget.2.trans
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hphase)
    have hbnd : B * X * Real.exp (-((2 * cepsComplexCumulantRootModel P N lam z 1 N b -
        cepsComplexCumulantRootModel P N lam z (-1) N b) * (1 + b * lam)).re) ≤
        B * X * Real.exp (-(D / 2 * F)) := mul_le_mul_of_nonneg_left hexp (by positivity)
    apply hbnd.trans
    have hcoef : B ≤ B * (1 + Real.exp (1 / vlo)) := by nlinarith [Real.exp_pos (1 / vlo)]
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hX.le)
      (Real.exp_pos (-(D / 2 * F))).le
    simpa only [neg_mul] using hh
  · have hphase := cepsComplexCumulantRootModel_left_window_sector N hM hlo hpκ hv hhi hi
      (le_of_not_ge hl) hz hbR N
    rw [cepsComplexKernelSubtractedBridgeJetModel, if_neg hl, sub_zero]
    apply hBudget.1.trans
    have hexp := Real.exp_le_exp.mpr (neg_le_neg hphase)
    have hbnd : B * X * Real.exp (-(cepsComplexCumulantRootModel P N lam z 1 N b * (1 + b * lam)).re) ≤
        B * X * Real.exp (-(D / 2 * F - 1 / vlo)) := mul_le_mul_of_nonneg_left hexp (by positivity)
    apply hbnd.trans
    have he : Real.exp (-(D / 2 * F - 1 / vlo)) = Real.exp (1 / vlo) * Real.exp (-(D / 2 * F)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    have hcoef : B * Real.exp (1 / vlo) ≤ B * (1 + Real.exp (1 / vlo)) := by nlinarith
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hX.le)
      (Real.exp_pos (-(D / 2 * F))).le
    convert hh using 1 <;> dsimp [F, X] <;> ring

end PGM
