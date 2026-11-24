import PLAStochastic.Index.CEPS.Strip.DenominatorBudget
import PLAStochastic.Index.CEPS.Scaled.ComplexJetEntranceWeighted
import PLAStochastic.Index.CEPS.Scaled.ComplexJetBridgeWeighted
import PLAStochastic.Index.CEPS.Scaled.ComplexJetEntranceCorrection
import PLAStochastic.Index.CEPS.Scaled.WeightedFirstSlope

/-! # Bridge, entrance and half-line factor budgets on admissible frequencies

Admissible-frequency forms of `ComplexJetBridgeWeighted`, `ComplexJetSpatialBudget`,
`ComplexJetSecondSlopeBudget` and `ComplexJetEntranceWeighted`, together with budgets for
the half-line bridge, the half-line entrance and the exact entrance correction.
-/

noncomputable section
open Complex Set Metric
namespace PGM

theorem cepsComplexKernelBridgeJetModel_weighted_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
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
  obtain ⟨δg, hδg, hG⟩ := cepsComplexKernelGJetModel_root_uniform_budget_adm d N
    (M := M) (vhi := vhi) hM hlo
  obtain ⟨δi, hδi, hInv⟩ :=
    cepsComplexKernelDenominatorJetModel_inverse_weighted_budget_adm d N hM hlo hhi0
  obtain ⟨δs, hδs, hDen⟩ := cepsComplexKernelDenominatorJetModel_uniform_ne_zero_adm d N hM hlo hhi0
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
  have hI : ‖(cepsComplexKernelDenominatorJetModel P N lam z b)⁻¹‖ ≤
      K * X * Real.exp (rm * w).re :=
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

theorem cepsComplexKernelGJetModel_spatial_uniform_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ∀ (n : ℕ) (ξ : ℂ),
          ‖ξ‖ ≤ cepsFiniteWeightSpatialWindow vlo * (1 + |lam| + Real.sqrt ‖z‖) / 2 →
          ‖iteratedDeriv n (cepsComplexKernelGJetModel (cepsComplexJetPad d p) N lam z b) ξ‖ ≤
            cepsFiniteComplexSpatialConstant n M vlo vhi *
              Real.exp (-(ξ * (1 + b * lam)).re) := by
  let S := cepsFiniteWeightSpatialWindow vlo
  let H := vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)
  have hA := cepsFiniteQuadraticRootBound_pos hlo
  have hS : 2 ≤ S := by dsimp [S, cepsFiniteWeightSpatialWindow]; linarith
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget_adm d N
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

theorem cepsComplexKernelEntranceSlopeJetModel_uniform_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖cepsComplexKernelEntranceSlopeJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          cepsFiniteComplexSpatialConstant 2 M vlo vhi *
            (Real.exp (-(cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b *
                (1 + b * lam)).re) +
              Real.exp (-(cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b *
                (1 + b * lam)).re) +
                Real.exp (-((b * z) * (1 + b * lam)).re)) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let S := cepsFiniteWeightSpatialWindow vlo
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δs, hδs, hSpatial⟩ := cepsComplexKernelGJetModel_spatial_uniform_budget_adm d N
    (M := M) (vhi := vhi) hM hlo
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
  have hrp : ‖rp‖ ≤ R / 2 := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbR N).2.trans hn
  have hrm : ‖rm‖ ≤ R / 2 := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
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

theorem cepsComplexKernelEntranceJetModel_weighted_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        let rp := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b
        let rm := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b
        ‖cepsComplexKernelEntranceJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          cepsFiniteComplexEntranceConstant N M vlo vhi * (1 + |lam| + Real.sqrt ‖z‖) *
            (1 + Real.exp (((rm - rp) * (1 + b * lam)).re) +
              Real.exp (((rm - b * z) * (1 + b * lam)).re)) := by
  obtain ⟨δs, hδs, hSlope⟩ := cepsComplexKernelEntranceSlopeJetModel_uniform_budget_adm d N hM hlo hhi0
  obtain ⟨δi, hδi, hInv⟩ :=
    cepsComplexKernelDenominatorJetModel_inverse_weighted_budget_adm d N hM hlo hhi0
  obtain ⟨δq, hδq, hQuot⟩ := cepsComplexCumulantJetQuotient_uniform_nonzero_budget_adm d N
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
  have hI : ‖(cepsComplexKernelDenominatorJetModel P N lam z b)⁻¹‖ ≤
      K * X * Real.exp (rm * w).re :=
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

/-- The half-line bridge retains the upper-root exponential and one drift-frequency weight. -/
theorem cepsComplexKernelHalfBridgeJetModel_weighted_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        ‖cepsComplexKernelHalfBridgeJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          4 * cepsFiniteQuadraticRootBound vlo *
            (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) *
            (1 + |lam| + Real.sqrt ‖z‖) *
            Real.exp (-(cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b *
              (1 + b * lam)).re) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δg, hδg, hG⟩ := cepsComplexKernelGJetModel_root_uniform_budget_adm d N
    (M := M) (vhi := vhi) hM hlo
  refine ⟨min δroot δg, lt_min hδroot hδg, ?_⟩
  intro p hp hv hhi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let H := vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hbF : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hrp : ‖rp‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbF N).2
  have hrm : ‖rm‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbF N).2
  have hgap : ‖rp - rm‖ ≤ 4 * A * X :=
    (norm_sub_le _ _).trans (by nlinarith [mul_le_mul_of_nonneg_left hFX hA.le])
  have hpG : ‖cepsComplexKernelGJetModel P N lam z b rp‖ ≤ H * Real.exp (-(rp * (1 + b * lam)).re) :=
    (hG p hp hv hhi lam z b hz (hb.trans (min_le_right _ _)) 1 (Or.inl rfl) N).2.1
  unfold cepsComplexKernelHalfBridgeJetModel
  rw [norm_mul]
  calc
    _ ≤ (4 * A * X) * (H * Real.exp (-(rp * (1 + b * lam)).re)) :=
      mul_le_mul hgap hpG (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The half-line entrance is controlled by the inverse marker gap. -/
theorem cepsComplexKernelHalfEntranceJetModel_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        cepsComplexCumulantJetQuotient (cepsComplexJetPad d p) N lam z b (b * z) ≠ 0 ∧
        ‖cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          Real.exp (((N : ℝ) + 1) ^ 3 * M) * (4 / vlo) /
            ‖b * z - cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b‖ := by
  obtain ⟨δq, hδq, hQuot⟩ := cepsComplexCumulantJetQuotient_uniform_nonzero_budget_adm d N
    (M := M) (vhi := vhi) (S := 1) hM hlo
  refine ⟨min (1 / 2) δq, lt_min (by norm_num) hδq, ?_⟩
  intro p hp hv hhi lam z b hz hb
  let P := cepsComplexJetPad d p
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let B := ((N : ℝ) + 1) ^ 3 * M
  have hX : 0 < X := by dsimp [X]; positivity
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
  have hQ := hQuot p hp hv hhi lam z b (b * z) hz (hb.trans (min_le_right _ _)) hmark
  have hQinv : ‖cepsComplexCumulantJetQuotient P N lam z b (b * z)‖⁻¹ ≤ 4 / vlo := by
    have hl : 0 < vlo / 4 := by positivity
    exact ((inv_le_inv₀ (hl.trans_le hQ.1) hl).mpr hQ.1).trans_eq (by ring)
  refine ⟨hQ.2.2, ?_⟩
  unfold cepsComplexKernelHalfEntranceJetModel
  rw [div_eq_mul_inv, mul_inv, norm_mul, norm_mul, norm_inv, norm_inv]
  calc
    _ ≤ Real.exp B * ((4 / vlo) *
        ‖b * z - cepsComplexCumulantRootModel P N lam z (-1) N b‖⁻¹) :=
      mul_le_mul hL (mul_le_mul_of_nonneg_right hQinv (inv_nonneg.mpr (norm_nonneg _)))
        (by positivity) (Real.exp_pos _).le
    _ = _ := by dsimp only [B, P]; ring

/-- The exact entrance correction keeps the half entrance, a weighted first slope and the
lower-root inverse denominator weight. -/
theorem cepsComplexKernelEntranceJetModel_sub_half_budget_adm (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        b * z ≠ cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b →
        let rp := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z 1 N b
        let rm := cepsComplexCumulantRootModel (cepsComplexJetPad d p) N lam z (-1) N b
        ‖cepsComplexKernelEntranceJetModel (cepsComplexJetPad d p) N lam z b -
          cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d p) N lam z b‖ ≤
          ‖cepsComplexKernelHalfEntranceJetModel (cepsComplexJetPad d p) N lam z b‖ *
            (cepsFiniteComplexSpatialConstant 1 M vlo vhi *
              cepsFiniteComplexSlopeInverseConstant M vlo vhi * (1 + |lam| + Real.sqrt ‖z‖)) *
            (Real.exp (((rm - rp) * (1 + b * lam)).re) +
              Real.exp (((rm - b * z) * (1 + b * lam)).re)) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let c := cepsFiniteQuadraticGapLower vlo vhi
  let S := cepsFiniteWeightSpatialWindow vlo
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  let δroot := cepsFiniteRootScaleRadius A c ((N : ℝ) * M) M
  have hδroot : 0 < δroot :=
    (cepsFiniteRootScaleRadius_admissible hA hc (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  obtain ⟨δs, hδs, hSpatial⟩ := cepsComplexKernelGJetModel_spatial_uniform_budget_adm d N
    (M := M) (vhi := vhi) hM hlo
  obtain ⟨δi, hδi, hInv⟩ :=
    cepsComplexKernelDenominatorJetModel_inverse_weighted_budget_adm d N hM hlo hhi0
  obtain ⟨δd, hδd, hDen⟩ := cepsComplexKernelDenominatorJetModel_uniform_ne_zero_adm d N hM hlo hhi0
  obtain ⟨δq, hδq, hHalf⟩ := cepsComplexKernelHalfEntranceJetModel_budget_adm d N
    (M := M) (vhi := vhi) hM hlo
  refine ⟨min 1 (min δroot (min δs (min δi (min δd δq)))),
    lt_min one_pos (lt_min hδroot (lt_min hδs (lt_min hδi (lt_min hδd hδq)))), ?_⟩
  intro p hp hv hhi hi lam z b hz hb ht
  have hb1 := hb.trans (min_le_left _ _)
  have hbroot := hb.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbs := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbi := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hbd := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbq := hb.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let R := S * X
  let G := cepsComplexKernelGJetModel P N lam z b
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let w : ℂ := 1 + b * lam
  let C1 := cepsFiniteComplexSpatialConstant 1 M vlo vhi
  let K := cepsFiniteComplexSlopeInverseConstant M vlo vhi
  have hX : 0 < X := by dsimp [X]; positivity
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hR : 0 < R := mul_pos (cepsFiniteWeightSpatialWindow_pos hlo) hX
  have hC1 : 0 < C1 := cepsFiniteComplexSpatialConstant_pos 1 hlo hhi0
  have hK : 0 < K := cepsFiniteComplexSlopeInverseConstant_pos hlo hhi0
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hbR : ‖b‖ * F ≤ δroot := (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans hbroot
  have hn : 2 * A * F ≤ R / 2 := by
    have hh := mul_le_mul_of_nonneg_left hFX (by positivity : 0 ≤ 2 * A)
    dsimp [R, S, cepsFiniteWeightSpatialWindow]
    nlinarith
  have hrp : ‖rp‖ ≤ R / 2 := (cepsComplexCumulantRootModel_stability_adm N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbR N).2.trans hn
  have hmark : ‖b * z‖ ≤ R / 2 := by
    have hsX : Real.sqrt ‖z‖ ≤ X := by dsimp [X]; linarith [abs_nonneg lam]
    have hbs' : ‖b‖ * Real.sqrt ‖z‖ ≤ 1 :=
      (mul_le_mul_of_nonneg_left hsX (norm_nonneg b)).trans hb1
    have hnz := mul_le_mul_of_nonneg_right hbs' (Real.sqrt_nonneg ‖z‖)
    rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg z), one_mul] at hnz
    rw [norm_mul]
    have hRX : X ≤ R / 2 := by dsimp [R, S, cepsFiniteWeightSpatialWindow]; nlinarith
    exact hnz.trans (hsX.trans hRX)
  have hd : DifferentiableOn ℂ G (ball 0 R) :=
    (cepsComplexKernelGJetModel_spatial_differentiable P N lam z b).differentiableOn
  have hderiv : ∀ ξ : ℂ, ‖ξ‖ ≤ R / 2 → ‖deriv G ξ‖ ≤ C1 * Real.exp (-(ξ * w).re) := by
    intro ξ hξ
    simpa only [iteratedDeriv_one] using hSpatial p hp hv hhi lam z b hz hbs 1 ξ hξ
  have hslope := cepsNormal_norm_dslope_le_weighted hR hC1.le hd hderiv hrp hmark
  have hS0 := hDen p hp hv hhi hi lam z b hz hbd
  have hI : ‖(cepsComplexKernelDenominatorJetModel P N lam z b)⁻¹‖ ≤
      K * X * Real.exp (rm * w).re := hInv p hp hv hhi hi lam z b hz hbi
  have hQ0 := (hHalf p hp hv hhi lam z b hz hbq).1
  change ‖cepsComplexKernelEntranceJetModel P N lam z b -
      cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
    ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ * (C1 * K * X) *
      (Real.exp (((rm - rp) * w).re) + Real.exp (((rm - b * z) * w).re))
  rw [cepsComplexKernelEntranceJetModel_sub_half_eq_first_slope P N lam z b hS0 hQ0 ht,
    div_eq_mul_inv, norm_mul, norm_mul, norm_neg]
  have hexp : (Real.exp (-(rp * w).re) + Real.exp (-((b * z) * w).re)) * Real.exp (rm * w).re =
      Real.exp (((rm - rp) * w).re) + Real.exp (((rm - b * z) * w).re) := by
    rw [add_mul, ← Real.exp_add, ← Real.exp_add]
    simp only [sub_mul, sub_re]
    ring_nf
  calc
    _ ≤ ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ *
        (C1 * (Real.exp (-(rp * w).re) + Real.exp (-((b * z) * w).re))) *
        (K * X * Real.exp (rm * w).re) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hslope (norm_nonneg _)) hI (norm_nonneg _)
        (by positivity)
    _ = _ := by rw [← hexp]; ring

end PGM
