import PLAStochastic.Index.CEPS.Strip.FactorBudget

/-! # Exponential envelopes of the complete-pair factors on admissible frequencies

All root exponentials are converted into multiples of `F = |λ| + √‖z‖` with the phase
constant `D = cepsFiniteRootPhaseLower vlo vhi`. The finite Newton and width errors are
kept below `D F / 16`, and so is the marker exponent `Re (b z (1 + b λ))`.
-/

noncomputable section
open Complex
namespace PGM

theorem cepsStrip_norm_marker_le {lam : ℝ} {z b : ℂ} {δ : ℝ}
    (hb : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ) :
    ‖b * z‖ ≤ δ * (|lam| + Real.sqrt ‖z‖) := by
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  have hsF : Real.sqrt ‖z‖ ≤ F := le_add_of_nonneg_left (abs_nonneg _)
  have hsX : Real.sqrt ‖z‖ ≤ X := by dsimp [X]; linarith [abs_nonneg lam]
  have hz : ‖z‖ ≤ X * F := by
    rw [← Real.mul_self_sqrt (norm_nonneg z)]
    exact mul_le_mul hsX hsF (Real.sqrt_nonneg _) (by dsimp [X]; positivity)
  rw [norm_mul]
  calc
    ‖b‖ * ‖z‖ ≤ ‖b‖ * (X * F) := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ = (‖b‖ * X) * F := by ring
    _ ≤ δ * F := mul_le_mul_of_nonneg_right hb (by dsimp [F]; positivity)

theorem cepsStrip_norm_width_le {lam : ℝ} {z b : ℂ}
    (hb : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ 1 / 2) :
    ‖b * (lam : ℂ)‖ ≤ 1 / 2 ∧ ‖1 + b * (lam : ℂ)‖ ≤ 2 ∧ 1 + b * (lam : ℂ) ≠ 0 ∧
      ‖(1 + b * (lam : ℂ))⁻¹‖ ≤ 2 := by
  have hl : |lam| ≤ 1 + |lam| + Real.sqrt ‖z‖ := by linarith [Real.sqrt_nonneg ‖z‖]
  have hbl : ‖b * (lam : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_mul, norm_real, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hl (norm_nonneg b)).trans hb
  have hlow : 1 / 2 ≤ ‖1 + b * (lam : ℂ)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-(b * (lam : ℂ)))
    rw [norm_one, norm_neg, sub_neg_eq_add] at h
    linarith
  refine ⟨hbl, (norm_add_le _ _).trans (by rw [norm_one]; linarith), ?_, ?_⟩
  · exact norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hlow)
  · rw [norm_inv]
    exact (inv_le_of_inv_le₀ (by norm_num) (by simpa using hlow))

/-- Factor premises and exponential envelopes on admissible frequencies. -/
theorem cepsStripFactorEnvelope (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), CepsRootAdmissible (cepsComplexJetPad d p) vlo vhi lam z →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        let P := cepsComplexJetPad d p
        let F := |lam| + Real.sqrt ‖z‖
        let X := 1 + |lam| + Real.sqrt ‖z‖
        let D := cepsFiniteRootPhaseLower vlo vhi
        let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
        CepsComplexJetRootChart P lam z ∧
        cepsComplexKernelDenominatorJetModel P N lam z b ≠ 0 ∧
        cepsComplexCumulantJetQuotient P N lam z b (b * z) ≠ 0 ∧
        1 + b * (lam : ℂ) ≠ 0 ∧ ‖(1 + b * (lam : ℂ))⁻¹‖ ≤ 2 ∧ ‖b‖ ≤ 1 / 2 ∧
        ‖exp ((b * z) * (1 + b * lam))‖ ≤ Real.exp (D / 16 * F) ∧
        (lam ≤ 1 → ‖cepsComplexKernelBridgeJetModel P N lam z b‖ ≤
          cepsFiniteComplexBridgeConstant M vlo vhi * Real.exp (1 / vlo) * X *
            Real.exp (-(15 * D / 16 * F)) ∧
          ‖cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
            4 * cepsFiniteQuadraticRootBound vlo *
              (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) * Real.exp (1 / vlo) * X *
              Real.exp (-(15 * D / 16 * F))) ∧
        ‖cepsComplexKernelEntranceJetModel P N lam z b‖ ≤
          3 * cepsFiniteComplexEntranceConstant N M vlo vhi * X * Real.exp (3 * D / 8 * F) ∧
        (0 ≤ lam →
          ‖cepsComplexKernelBridgeJetModel P N lam z b -
            cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
            cepsFiniteComplexBridgeConstant M vlo vhi * X * Real.exp (-(25 * D / 16 * F)) ∧
          ‖cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
            4 * cepsFiniteQuadraticRootBound vlo *
              (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) * X *
              Real.exp (5 * D / 16 * F) ∧
          ‖cepsComplexKernelEntranceJetModel P N lam z b‖ ≤
            3 * cepsFiniteComplexEntranceConstant N M vlo vhi * X ∧
          7 * D / 16 * F ≤ ‖b * z - rm‖ ∧
          ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
            Real.exp (((N : ℝ) + 1) ^ 3 * M) * (4 / vlo) / (7 * D / 16 * F) ∧
          ‖cepsComplexKernelEntranceJetModel P N lam z b -
            cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
            ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ *
              (cepsFiniteComplexSpatialConstant 1 M vlo vhi *
                cepsFiniteComplexSlopeInverseConstant M vlo vhi * X) *
              (2 * Real.exp (-(7 * D / 8 * F)))) := by
  let D := cepsFiniteRootPhaseLower vlo vhi
  have hD : 0 < D := by
    have := cepsFiniteQuadraticGapLower_pos (vhi := vhi) hlo
    dsimp [D, cepsFiniteRootPhaseLower]
    positivity
  let η := D / 16
  have hη : 0 < η := by positivity
  obtain ⟨δB, hδB, hBridge⟩ := cepsComplexKernelBridgeJetModel_weighted_budget_adm d N hM hlo hhi0
  obtain ⟨δA, hδA, hEnt⟩ := cepsComplexKernelEntranceJetModel_weighted_budget_adm d N hM hlo hhi0
  obtain ⟨δH, hδH, hHalfB⟩ := cepsComplexKernelHalfBridgeJetModel_weighted_budget_adm d N
    (vhi := vhi) hM hlo
  obtain ⟨δE, hδE, hHalfE⟩ := cepsComplexKernelHalfEntranceJetModel_budget_adm d N
    (vhi := vhi) hM hlo
  obtain ⟨δC, hδC, hCorr⟩ := cepsComplexKernelEntranceJetModel_sub_half_budget_adm d N hM hlo hhi0
  obtain ⟨δS, hδS, hDen⟩ := cepsComplexKernelDenominatorJetModel_uniform_ne_zero_adm d N hM hlo hhi0
  let δη := cepsFiniteRootSmallRadius N M vlo vhi η
  have hδη : 0 < δη := cepsFiniteRootSmallRadius_pos N hM hlo hη
  let δ := min (min (1 / 2) (D / 32)) (min (min δB δA) (min (min δH δE) (min (min δC δS) δη)))
  have hδ : 0 < δ := by
    apply lt_min (lt_min (by norm_num) (by positivity))
    exact lt_min (lt_min hδB hδA) (lt_min (lt_min hδH hδE) (lt_min (lt_min hδC hδS) hδη))
  refine ⟨δ, hδ, ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  have hbhalf : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ 1 / 2 :=
    hb.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hbD : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ D / 32 :=
    hb.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb2 := hb.trans (min_le_right _ _)
  have hbB : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δB :=
    hb2.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hbA : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δA :=
    hb2.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb3 := hb2.trans (min_le_right _ _)
  have hbH : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δH :=
    hb3.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hbE : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δE :=
    hb3.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hb4 := hb3.trans (min_le_right _ _)
  have hbC : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δC :=
    hb4.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hbS : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δS :=
    hb4.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hbη' : ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δη := hb4.trans (min_le_right _ _)
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let w : ℂ := 1 + b * lam
  let bp := cepsComplexCumulantRootBase P lam z 1
  let bm := cepsComplexCumulantRootBase P lam z (-1)
  have hF : 0 < F := hz.pos
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hbη : ‖b‖ * F ≤ δη := (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans hbη'
  -- base-root facts
  have hsep := cepsComplexCumulantRootBase_separation_lower_adm P hlo hv hhi hi lam hz
  rw [sub_re] at hsep
  have hind := cepsComplexCumulantRootBase_individual_sector_adm P hlo hv hhi hi lam hz
  have hlower := cepsComplexCumulantRootBase_plus_re_lower_adm P hlo hv hhi hi lam hz
  change D * F - |lam| / vlo ≤ bp.re at hlower
  change 2 * D * F ≤ bp.re - bm.re at hsep
  -- weighted Newton errors
  have hEp := cepsComplexCumulantRootModel_weighted_error_small N hM hlo hpκ hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbη N
  have hEm := cepsComplexCumulantRootModel_weighted_error_small N hM hlo hpκ hv lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbη N
  change ‖rp * w - bp‖ ≤ D / 16 * F at hEp
  change ‖rm * w - bm‖ ≤ D / 16 * F at hEm
  have hDF : 0 ≤ D * F := by positivity
  have hEp1 := re_le_norm (rp * w - bp)
  have hEp2 := re_le_norm (-(rp * w - bp))
  have hEm1 := re_le_norm (rm * w - bm)
  have hEm2 := re_le_norm (-(rm * w - bm))
  rw [sub_re] at hEp1 hEm1
  rw [neg_re, sub_re, norm_neg] at hEp2 hEm2
  -- marker and width
  have hmk : ‖b * z‖ ≤ D / 32 * F := cepsStrip_norm_marker_le hbD
  obtain ⟨hbl, hwn, hw0, hwinv⟩ := cepsStrip_norm_width_le hbhalf
  have hbz : ‖(b * z) * w‖ ≤ D / 16 * F := by
    rw [norm_mul]
    calc
      ‖b * z‖ * ‖w‖ ≤ (D / 32 * F) * 2 := mul_le_mul hmk hwn (norm_nonneg _) (by positivity)
      _ = D / 16 * F := by ring
  have hbzre := re_le_norm ((b * z) * w)
  have hbzre' := re_le_norm (-((b * z) * w))
  rw [neg_re, norm_neg] at hbzre'
  have hbn : ‖b‖ ≤ 1 / 2 := by
    have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
    calc
      ‖b‖ = ‖b‖ * 1 := (mul_one _).symm
      _ ≤ ‖b‖ * X := mul_le_mul_of_nonneg_left hX1 (norm_nonneg _)
      _ ≤ 1 / 2 := hbhalf
  -- the four exponent facts
  have hRm_all : (rm * w).re ≤ 5 * D / 16 * F := by
    by_cases hl : 0 ≤ lam
    · have := hind.2 hl
      change bm.re ≤ -(D * F) at this
      linarith
    · have := hz.minus (le_of_not_ge hl)
      change bm.re ≤ D / 4 * F at this
      linarith
  have hRp_left : lam ≤ 1 → 15 * D / 16 * F - 1 / vlo ≤ (rp * w).re := by
    intro hl1
    by_cases hl : lam ≤ 0
    · have := hind.1 hl
      change D * F ≤ bp.re at this
      have : 0 < 1 / vlo := by positivity
      linarith
    · have habs : |lam| ≤ 1 := by rw [abs_of_pos (lt_of_not_ge hl)]; exact hl1
      have : |lam| / vlo ≤ 1 / vlo := div_le_div_of_nonneg_right habs hlo.le
      linarith
  have hgapRe : (rm * w).re - (rp * w).re ≤ -(15 * D / 8 * F) := by linarith
  -- premises
  have hchart : CepsComplexJetRootChart P lam z := hz.chart (hlo.trans_le hv)
  have hS0 := hDen p hp hv hhi hi lam z b hz hbS
  have hQ0 := (hHalfE p hp hv hhi lam z b hz hbE).1
  have hEnorm : ‖exp ((b * z) * (1 + b * lam))‖ ≤ Real.exp (D / 16 * F) := by
    rw [norm_exp]
    exact Real.exp_le_exp.mpr (hbzre.trans hbz)
  -- entrance
  have hEnt' := hEnt p hp hv hhi hi lam z b hz hbA
  change ‖cepsComplexKernelEntranceJetModel P N lam z b‖ ≤
    cepsFiniteComplexEntranceConstant N M vlo vhi * X *
      (1 + Real.exp (((rm - rp) * w).re) + Real.exp (((rm - b * z) * w).re)) at hEnt'
  have hKA : 0 < cepsFiniteComplexEntranceConstant N M vlo vhi :=
    cepsFiniteComplexEntranceConstant_pos N hlo hhi0
  have he1 : ((rm - rp) * w).re = (rm * w).re - (rp * w).re := by rw [sub_mul, sub_re]
  have he2 : ((rm - b * z) * w).re = (rm * w).re - ((b * z) * w).re := by rw [sub_mul, sub_re]
  have hexp1 : Real.exp (((rm - rp) * w).re) ≤ 1 := by
    rw [he1]
    apply Real.exp_le_one_iff.mpr
    linarith
  have hentrance_gen : ‖cepsComplexKernelEntranceJetModel P N lam z b‖ ≤
      3 * cepsFiniteComplexEntranceConstant N M vlo vhi * X * Real.exp (3 * D / 8 * F) := by
    apply hEnt'.trans
    have hexp2 : Real.exp (((rm - b * z) * w).re) ≤ Real.exp (3 * D / 8 * F) := by
      rw [he2]
      apply Real.exp_le_exp.mpr
      linarith
    have hone : 1 ≤ Real.exp (3 * D / 8 * F) := Real.one_le_exp (by positivity)
    calc
      _ ≤ cepsFiniteComplexEntranceConstant N M vlo vhi * X *
          (Real.exp (3 * D / 8 * F) + Real.exp (3 * D / 8 * F) + Real.exp (3 * D / 8 * F)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      _ = _ := by ring
  refine ⟨hchart, hS0, hQ0, hw0, hwinv, hbn, hEnorm, ?_, hentrance_gen, ?_⟩
  · -- the bridge for drifts at most one
    intro hl1
    have hB := (hBridge p hp hv hhi hi lam z b hz hbB).1
    change ‖cepsComplexKernelBridgeJetModel P N lam z b‖ ≤
      cepsFiniteComplexBridgeConstant M vlo vhi * X * Real.exp (-(rp * w).re) at hB
    have hKB : 0 < cepsFiniteComplexBridgeConstant M vlo vhi :=
      cepsFiniteComplexBridgeConstant_pos hlo hhi0
    have hexp : Real.exp (-(rp * w).re) ≤ Real.exp (1 / vlo) * Real.exp (-(15 * D / 16 * F)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hRp_left hl1]
    have hHB := hHalfB p hp hv hhi lam z b hz hbH
    change ‖cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
      4 * cepsFiniteQuadraticRootBound vlo *
        (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) * X *
        Real.exp (-(rp * w).re) at hHB
    have hA0 := cepsFiniteQuadraticRootBound_pos hlo
    constructor
    · apply hB.trans
      calc
        _ ≤ cepsFiniteComplexBridgeConstant M vlo vhi * X *
            (Real.exp (1 / vlo) * Real.exp (-(15 * D / 16 * F))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := by ring
    · apply hHB.trans
      calc
        _ ≤ 4 * cepsFiniteQuadraticRootBound vlo *
            (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) * X *
            (Real.exp (1 / vlo) * Real.exp (-(15 * D / 16 * F))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := by ring
  · -- the nonnegative drift side
    intro hl
    have hbm : bm.re ≤ -(D * F) := hind.2 hl
    have hbp : -(D / 4 * F) ≤ bp.re := hz.plus hl
    have hRm : (rm * w).re ≤ -(15 * D / 16 * F) := by linarith
    have hRp : -(5 * D / 16 * F) ≤ (rp * w).re := by linarith
    have hBB := (hBridge p hp hv hhi hi lam z b hz hbB).2
    change ‖cepsComplexKernelBridgeJetModel P N lam z b -
        cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
      cepsFiniteComplexBridgeConstant M vlo vhi * X * Real.exp (-((2 * rp - rm) * w).re) at hBB
    have hKB : 0 < cepsFiniteComplexBridgeConstant M vlo vhi :=
      cepsFiniteComplexBridgeConstant_pos hlo hhi0
    have h2 : ((2 * rp - rm) * w).re = (rp * w).re + (rp * w).re - (rm * w).re := by
      rw [show (2 * rp - rm) * w = rp * w + rp * w - rm * w by ring, sub_re, add_re]
    have hmarkLow : 7 * D / 8 * F ≤ ((b * z - rm) * w).re := by
      rw [sub_mul, sub_re]
      linarith
    have hmark : 7 * D / 16 * F ≤ ‖b * z - rm‖ := by
      have h1 := re_le_norm ((b * z - rm) * w)
      rw [norm_mul] at h1
      have h2 : ‖b * z - rm‖ * ‖w‖ ≤ ‖b * z - rm‖ * 2 :=
        mul_le_mul_of_nonneg_left hwn (norm_nonneg _)
      linarith
    have hmark0 : b * z ≠ rm := by
      intro h
      rw [h, sub_self, norm_zero] at hmark
      have : 0 < 7 * D / 16 * F := by positivity
      linarith
    have hAh := (hHalfE p hp hv hhi lam z b hz hbE).2
    change ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
      Real.exp (((N : ℝ) + 1) ^ 3 * M) * (4 / vlo) / ‖b * z - rm‖ at hAh
    have hAh' : ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
        Real.exp (((N : ℝ) + 1) ^ 3 * M) * (4 / vlo) / (7 * D / 16 * F) :=
      hAh.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hmark)
    have hC := hCorr p hp hv hhi hi lam z b hz hbC hmark0
    change ‖cepsComplexKernelEntranceJetModel P N lam z b -
        cepsComplexKernelHalfEntranceJetModel P N lam z b‖ ≤
      ‖cepsComplexKernelHalfEntranceJetModel P N lam z b‖ *
        (cepsFiniteComplexSpatialConstant 1 M vlo vhi *
          cepsFiniteComplexSlopeInverseConstant M vlo vhi * X) *
        (Real.exp (((rm - rp) * w).re) + Real.exp (((rm - b * z) * w).re)) at hC
    have hC1 : 0 < cepsFiniteComplexSpatialConstant 1 M vlo vhi :=
      cepsFiniteComplexSpatialConstant_pos 1 hlo hhi0
    have hK1 : 0 < cepsFiniteComplexSlopeInverseConstant M vlo vhi :=
      cepsFiniteComplexSlopeInverseConstant_pos hlo hhi0
    have hHB := hHalfB p hp hv hhi lam z b hz hbH
    change ‖cepsComplexKernelHalfBridgeJetModel P N lam z b‖ ≤
      4 * cepsFiniteQuadraticRootBound vlo *
        (vhi / 2 * Real.exp (2 * M) + vlo / 4 * Real.exp (-2 * M)) * X *
        Real.exp (-(rp * w).re) at hHB
    have hA0 := cepsFiniteQuadraticRootBound_pos hlo
    refine ⟨?_, ?_, ?_, hmark, hAh', ?_⟩
    · apply hBB.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      rw [h2]
      linarith
    · apply hHB.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      linarith
    · apply hEnt'.trans
      have hexp2 : Real.exp (((rm - b * z) * w).re) ≤ 1 := by
        rw [he2]
        apply Real.exp_le_one_iff.mpr
        linarith
      calc
        _ ≤ cepsFiniteComplexEntranceConstant N M vlo vhi * X * (1 + 1 + 1) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
        _ = _ := by ring
    · apply hC.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hexp1' : Real.exp (((rm - rp) * w).re) ≤ Real.exp (-(7 * D / 8 * F)) := by
        rw [he1]
        apply Real.exp_le_exp.mpr
        linarith
      have hexp2' : Real.exp (((rm - b * z) * w).re) ≤ Real.exp (-(7 * D / 8 * F)) := by
        rw [he2]
        apply Real.exp_le_exp.mpr
        linarith
      linarith

end PGM
