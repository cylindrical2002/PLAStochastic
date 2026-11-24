import PLAStochastic.Index.CEPS.Scaled.ComplexJetSecondSlopeBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightedInverse
import PLAStochastic.Index.CEPS.Scaled.ComplexJetMarkerBudget

/-! # Complete finite-vector entrance budgets retain cancellation-compatible weights -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteComplexEntranceConstant (N : ℕ) (M vlo vhi : ℝ) : ℝ :=
  Real.exp (((N : ℝ) + 1) ^ 3 * M) * cepsFiniteComplexSpatialConstant 2 M vlo vhi *
    (4 / vlo) * cepsFiniteComplexSlopeInverseConstant M vlo vhi

theorem cepsFiniteComplexEntranceConstant_pos (N : ℕ) {M vlo vhi : ℝ}
    (hlo : 0 < vlo) (hhi : 0 < vhi) :
    0 < cepsFiniteComplexEntranceConstant N M vlo vhi := by
  have := cepsFiniteComplexSpatialConstant_pos 2 (M := M) hlo hhi
  have := cepsFiniteComplexSlopeInverseConstant_pos (M := M) hlo hhi
  unfold cepsFiniteComplexEntranceConstant
  positivity

/-- All three actual factors are paid on a common input-box radius. The resulting
entrance retains precisely the relative root and marker exponents needed by the complete pair. -/
theorem cepsComplexKernelEntranceJetModel_weighted_budget (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        let rp := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b
        let rm := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b
        ‖cepsComplexKernelEntranceJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          cepsFiniteComplexEntranceConstant N M vlo vhi * (1 + |lam| + Real.sqrt ‖z‖) *
            (1 + Real.exp (((rm - rp) * (1 + b * lam)).re) +
              Real.exp (((rm - b * z) * (1 + b * lam)).re)) := by
  obtain ⟨δs, hδs, hSlope⟩ := cepsComplexKernelEntranceSlopeJetModel_uniform_budget d N hM hlo hhi0
  obtain ⟨δi, hδi, hInv⟩ := cepsComplexKernelDenominatorJetModel_inverse_weighted_budget d N hM hlo hhi0
  obtain ⟨δq, hδq, hQuot⟩ := cepsComplexCumulantJetQuotient_uniform_nonzero_budget d N
    (M := M) (vhi := vhi) (S := 1) hM hlo
  refine ⟨min (1 / 2) (min δs (min δi δq)), lt_min (by norm_num) (lt_min hδs (lt_min hδi hδq)), ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let w : ℂ := 1 + b * lam
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let C := cepsFiniteComplexSpatialConstant 2 M vlo vhi
  let K := cepsFiniteComplexSlopeInverseConstant M vlo vhi
  let B := ((N : ℝ) + 1) ^ 3 * M
  let E := Real.exp (-(rm * w).re) + Real.exp (-(rp * w).re) + Real.exp (-((b * z) * w).re)
  have hC : 0 < C := cepsFiniteComplexSpatialConstant_pos 2 hlo hhi0
  have hK : 0 < K := cepsFiniteComplexSlopeInverseConstant_pos hlo hhi0
  have hX : 0 < X := by dsimp [X]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hbhalf := hb.trans (min_le_left _ _)
  have hL : ‖exp (cepsCanonComplexJetPolynomial P N (b * lam)
      (cepsComplexScaledDiscount lam z b) (b ^ 2 * z))‖ ≤ Real.exp B :=
    cepsComplexKernelMarker_exp_uniform_budget d N hM p hp lam z b hbhalf
  have hmark : ‖b * z‖ ≤ 1 * X := by
    have hsX : Real.sqrt ‖z‖ ≤ X := by dsimp [X]; linarith [abs_nonneg lam]
    have hbs : ‖b‖ * Real.sqrt ‖z‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hsX (norm_nonneg b)).trans (hbhalf.trans (by norm_num))
    have hn := mul_le_mul_of_nonneg_right hbs (Real.sqrt_nonneg ‖z‖)
    rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg z), one_mul] at hn
    rw [norm_mul, one_mul]
    exact hn.trans hsX
  have hQ := (hQuot p hp hv hhi lam z b (b * z) hz
    (hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) hmark).1
  have hQinv : ‖(cepsComplexCumulantJetQuotient P N lam z b (b * z))⁻¹‖ ≤ 4 / vlo := by
    rw [norm_inv]
    have hl : 0 < vlo / 4 := by positivity
    exact ((inv_le_inv₀ (hl.trans_le hQ) hl).mpr hQ).trans_eq (by ring)
  have hDD : ‖cepsComplexKernelEntranceSlopeJetModel P N lam z b‖ ≤ C * E :=
    hSlope p hp hv hhi lam z b hz (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hI : ‖(cepsComplexKernelDenominatorJetModel P N lam z b)⁻¹‖ ≤ K * X * Real.exp (rm * w).re :=
    hInv p hp hv hhi hi lam z b hz
      (hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  unfold cepsComplexKernelEntranceJetModel
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_mul, norm_neg, ← mul_assoc]
  apply (mul_le_mul (mul_le_mul (mul_le_mul hL hDD (norm_nonneg _) (Real.exp_pos _).le)
    hQinv (norm_nonneg _) (by positivity)) hI (norm_nonneg _) (by positivity)).trans_eq
  have hExp : E * Real.exp (rm * w).re =
      1 + Real.exp (((rm - rp) * w).re) + Real.exp (((rm - b * z) * w).re) := by
    dsimp only [E]
    rw [add_mul, add_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, sub_mul, sub_re]
    ring_nf
  change Real.exp B * (C * E) * (4 / vlo) * (K * X * Real.exp (rm * w).re) = _
  change _ = (Real.exp B * C * (4 / vlo) * K) * X *
    (1 + Real.exp (((rm - rp) * w).re) + Real.exp (((rm - b * z) * w).re))
  calc
    _ = (Real.exp B * C * (4 / vlo) * K * X) * (E * Real.exp (rm * w).re) := by ring
    _ = _ := by rw [hExp]

end PGM
