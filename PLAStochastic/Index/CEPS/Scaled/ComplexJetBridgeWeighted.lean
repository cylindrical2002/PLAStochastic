import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightedInverse
import PLAStochastic.Index.CEPS.Scaled.ComplexJetPositiveRoot
import PLAStochastic.Index.CEPS.Scaled.ComplexJetHalfFactors

/-! # Exact half-line subtraction and weighted finite-vector bridge budgets -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteComplexBridgeConstant (M vlo vhi : ℝ) : ℝ :=
  (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) ^ 2 *
    cepsFiniteComplexSlopeInverseConstant M vlo vhi

theorem cepsFiniteComplexBridgeConstant_pos {M vlo vhi : ℝ}
    (hlo : 0 < vlo) (hhi : 0 < vhi) : 0 < cepsFiniteComplexBridgeConstant M vlo vhi := by
  have := cepsFiniteComplexSlopeInverseConstant_pos (M := M) hlo hhi
  unfold cepsFiniteComplexBridgeConstant
  positivity

/-- This is the actual bridge minus its actual half-line bridge, through root collisions. -/
theorem cepsComplexKernelBridgeJetModel_sub_half_eq_square (p : ℕ → ℂ) (N : ℕ)
    (lam : ℝ) (z b : ℂ) (hS : cepsComplexKernelDenominatorJetModel p N lam z b ≠ 0) :
    cepsComplexKernelBridgeJetModel p N lam z b - cepsComplexKernelHalfBridgeJetModel p N lam z b =
      -(cepsComplexKernelGJetModel p N lam z b (cepsComplexCumulantRootModel p N lam z 1 N b)) ^ 2 /
        cepsComplexKernelDenominatorJetModel p N lam z b := by
  have hid := sub_smul_dslope (cepsComplexKernelGJetModel p N lam z b)
    (cepsComplexCumulantRootModel p N lam z (-1) N b) (cepsComplexCumulantRootModel p N lam z 1 N b)
  rw [smul_eq_mul] at hid
  change (_ - _) * cepsComplexKernelDenominatorJetModel p N lam z b = _ at hid
  unfold cepsComplexKernelBridgeJetModel cepsComplexKernelHalfBridgeJetModel
  field_simp [hS]
  linear_combination -(cepsComplexKernelGJetModel p N lam z b
    (cepsComplexCumulantRootModel p N lam z 1 N b)) * hid

/-- Both weights are exact and share the same radius. The second one already contains
the positive-side cancellation exponent, rather than a sum of separate factor bounds. -/
theorem cepsComplexKernelBridgeJetModel_weighted_budget (d N : ℕ) {M vlo vhi : ℝ}
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
        let K := cepsFiniteComplexBridgeConstant M vlo vhi
        let X := 1 + |lam| + Real.sqrt ‖z‖
        ‖cepsComplexKernelBridgeJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          K * X * Real.exp (-(rp * (1 + b * lam)).re) ∧
        ‖cepsComplexKernelBridgeJetModel (cepsComplexJetPad d p) N lam z b -
          cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          K * X * Real.exp (-((2 * rp - rm) * (1 + b * lam)).re) := by
  obtain ⟨δg, hδg, hG⟩ := cepsComplexKernelGJetModel_root_uniform_budget d N
    (M := M) (vhi := vhi) hM hlo
  obtain ⟨δi, hδi, hInv⟩ := cepsComplexKernelDenominatorJetModel_inverse_weighted_budget d N hM hlo hhi0
  obtain ⟨δs, hδs, hDen⟩ := cepsComplexKernelDenominatorJetModel_uniform_ne_zero d N hM hlo hhi0
  refine ⟨min δg (min δi δs), lt_min hδg (lt_min hδi hδs), ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let w : ℂ := 1 + b * lam
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let H := vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)
  let K := cepsFiniteComplexSlopeInverseConstant M vlo vhi
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := cepsFiniteComplexSlopeInverseConstant_pos hlo hhi0
  have hX : 0 < X := by dsimp [X]; positivity
  have hpG : ‖cepsComplexKernelGJetModel P N lam z b rp‖ ≤ H * Real.exp (-(rp * w).re) :=
    (hG p hp hv hhi lam z b hz (hb.trans (min_le_left _ _)) 1 (Or.inl rfl) N).2.1
  have hmG : ‖cepsComplexKernelGJetModel P N lam z b rm‖ ≤ H * Real.exp (-(rm * w).re) :=
    (hG p hp hv hhi lam z b hz (hb.trans (min_le_left _ _)) (-1) (Or.inr rfl) N).2.1
  have hI : ‖(cepsComplexKernelDenominatorJetModel P N lam z b)⁻¹‖ ≤ K * X * Real.exp (rm * w).re :=
    hInv p hp hv hhi hi lam z b hz (hb.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hS := hDen p hp hv hhi hi lam z b hz (hb.trans ((min_le_right _ _).trans (min_le_right _ _)))
  change _ ≤ (H ^ 2 * K) * X * Real.exp (-(rp * w).re) ∧
    _ ≤ (H ^ 2 * K) * X * Real.exp (-((2 * rp - rm) * w).re)
  constructor
  · unfold cepsComplexKernelBridgeJetModel
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_neg]
    apply (mul_le_mul (mul_le_mul hpG hmG (norm_nonneg _) (by positivity)) hI
      (norm_nonneg _) (by positivity)).trans_eq
    calc
      _ = H ^ 2 * K * X * Real.exp (-(rp * w).re) *
          (Real.exp (-(rm * w).re) * Real.exp (rm * w).re) := by ring
      _ = _ := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  · rw [cepsComplexKernelBridgeJetModel_sub_half_eq_square P N lam z b hS,
      div_eq_mul_inv, norm_mul, norm_neg, norm_pow]
    apply (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hpG 2) hI
      (norm_nonneg _) (by positivity)).trans_eq
    calc
      _ = H ^ 2 * K * X *
          (Real.exp (-(rp * w).re) * Real.exp (-(rp * w).re) * Real.exp (rm * w).re) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        simp [sub_mul, mul_assoc, mul_re]
        ring

end PGM
