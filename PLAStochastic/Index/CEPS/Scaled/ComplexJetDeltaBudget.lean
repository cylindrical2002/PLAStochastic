import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightSpatial
import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightedRoots
import PLAStochastic.Index.CEPS.Normal.DenominatorBound

/-! # A common complex finite-vector lower bound for the full exponential denominator -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteComplexDeltaSector (vlo vhi : ℝ) : ℝ :=
  min 1 (cepsFiniteRootPhaseLower vlo vhi)

def cepsComplexKernelJetDelta (p : ℕ → ℂ) (N : ℕ) (lam : ℝ) (z b : ℂ) : ℂ :=
  1 - exp (-((cepsComplexCumulantRootModel p N lam z 1 N b -
    cepsComplexCumulantRootModel p N lam z (-1) N b) * (1 + b * lam))) *
    (cepsComplexKernelJetWeight p N lam z b (cepsComplexCumulantRootModel p N lam z 1 N b) /
      cepsComplexKernelJetWeight p N lam z b (cepsComplexCumulantRootModel p N lam z (-1) N b))

theorem cepsFiniteComplexDeltaSector_pos {vlo vhi : ℝ} (hlo : 0 < vlo) (hhi : 0 < vhi) :
    0 < cepsFiniteComplexDeltaSector vlo vhi := by
  unfold cepsFiniteComplexDeltaSector cepsFiniteRootPhaseLower
  exact lt_min one_pos (div_pos (cepsFiniteQuadraticGapLower_pos hlo) (by positivity))

/-- The full exponential denominator has a common lower bound on the finite-vector box,
every real drift and every right-half-plane frequency. The joint origin is retained. -/
theorem cepsComplexKernelJetDelta_uniform_lower (d N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi0 : 0 < vhi) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : Fin d → ℂ), ‖p‖ ≤ M →
      vlo ≤ (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re →
      ‖cepsComplexJetPad d p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(cepsComplexJetPad d p (cepsJetCode (.inl 0))).im| ≤
        (cepsComplexJetPad d p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re →
        ‖b‖ * (1 + |lam| + Real.sqrt ‖z‖) ≤ δ →
        cepsFiniteComplexDeltaSector vlo vhi / 4 *
          ((|lam| + Real.sqrt ‖z‖) / (1 + |lam| + Real.sqrt ‖z‖)) ≤
          ‖cepsComplexKernelJetDelta (cepsComplexJetPad d p) N lam z b‖ := by
  let A := cepsFiniteQuadraticRootBound vlo
  let S := cepsFiniteWeightSpatialWindow vlo
  let c := cepsFiniteComplexDeltaSector vlo vhi
  let Wlo := vlo / 4 * Real.exp (-2 * M)
  let ε := c * S * Wlo / (64 * A)
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hS : 0 < S := cepsFiniteWeightSpatialWindow_pos hlo
  have hc : 0 < c := cepsFiniteComplexDeltaSector_pos hlo hhi0
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcD : c ≤ cepsFiniteRootPhaseLower vlo vhi := min_le_right _ _
  have hWlo : 0 < Wlo := by dsimp [Wlo]; positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  let δroot := cepsFiniteWeightedRootRadius N M vlo vhi
  have hδroot : 0 < δroot := cepsFiniteWeightedRootRadius_pos N hM hlo hhi0
  obtain ⟨δw, hδw, hW⟩ := cepsComplexKernelJetWeight_uniform_nonzero_budget d N
    (M := M) (vhi := vhi) (S := S) hM hlo
  obtain ⟨δs, hδs, hSlope⟩ := cepsComplexKernelJetWeight_root_slope_uniform_budget d N
    (M := M) (vhi := vhi) hM hlo hε
  refine ⟨min δroot (min δw δs), lt_min hδroot (lt_min hδw hδs), ?_⟩
  intro p hp hv hhi hi lam z b hz hb
  let P := cepsComplexJetPad d p
  let F := |lam| + Real.sqrt ‖z‖
  let X := 1 + |lam| + Real.sqrt ‖z‖
  let rp := cepsComplexCumulantRootModel P N lam z 1 N b
  let rm := cepsComplexCumulantRootModel P N lam z (-1) N b
  let W := cepsComplexKernelJetWeight P N lam z b
  let ratio := W rp / W rm
  let gap := (rp - rm) * (1 + b * lam)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hX : 0 < X := by dsimp [X]; positivity
  have hX1 : 1 ≤ X := by dsimp [X]; linarith [abs_nonneg lam, Real.sqrt_nonneg ‖z‖]
  have hFX : F ≤ X := by dsimp [F, X]; linarith
  have hbroot : ‖b‖ * F ≤ δroot :=
    (mul_le_mul_of_nonneg_left hFX (norm_nonneg b)).trans (hb.trans (min_le_left _ _))
  have hbNewton := hbroot.trans (min_le_left _ _)
  have hpκ : ∀ j ≤ N, ‖P (cepsJetCode (.inl j))‖ ≤ M :=
    fun j _ => cepsComplexJetPad_norm_le hM hp _
  have hrp : ‖rp‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hbNewton N).2
  have hrm : ‖rm‖ ≤ 2 * A * F := (cepsComplexCumulantRootModel_right_stability N hM hlo hpκ hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hbNewton N).2
  have hmark : ‖rm‖ ≤ S * X := by
    calc
      _ ≤ 2 * A * F := hrm
      _ ≤ 2 * A * X := mul_le_mul_of_nonneg_left hFX (by positivity)
      _ ≤ S * X := mul_le_mul_of_nonneg_right (by dsimp [S, cepsFiniteWeightSpatialWindow]; linarith) hX.le
  have hwm : Wlo ≤ ‖W rm‖ := (hW p hp hv hhi lam z b rm hz
    (hb.trans ((min_le_right _ _).trans (min_le_left _ _))) hmark).1
  have hwm0 : W rm ≠ 0 := norm_pos_iff.mp (hWlo.trans_le hwm)
  have hwmn : 0 < ‖W rm‖ := hWlo.trans_le hwm
  have hs : ‖dslope W rm rp‖ ≤ 4 * ε / (S * X) := hSlope p hp hv hhi lam z b hz
    (hb.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hdiff : ‖W rp - W rm‖ ≤ (4 * A * F) * (4 * ε / (S * X)) := by
    have he := sub_smul_dslope W rm rp
    rw [smul_eq_mul] at he
    rw [← he, norm_mul]
    apply mul_le_mul _ hs (norm_nonneg _) (by positivity)
    exact (norm_sub_le _ _).trans (by linarith)
  have hfactor : ‖ratio - 1‖ ≤ c / 4 * (F / X) := by
    have he : ratio - 1 = (W rp - W rm) / W rm := by dsimp [ratio]; field_simp [hwm0]
    rw [he, norm_div]
    calc
      _ ≤ ((4 * A * F) * (4 * ε / (S * X))) / ‖W rm‖ :=
        div_le_div_of_nonneg_right hdiff hwmn.le
      _ ≤ ((4 * A * F) * (4 * ε / (S * X))) / Wlo :=
        div_le_div_of_nonneg_left (by positivity) hWlo hwm
      _ = _ := by
        dsimp [ε]
        field_simp [hA.ne', hS.ne', hX.ne', hWlo.ne']
        ring
  have hsector : c * (F / X) ≤ gap.re := by
    have hgap := cepsComplexCumulantRootModel_weighted_separation N hM hlo hpκ hv hhi hi lam hz hbroot N
    calc
      _ ≤ c * F := mul_le_mul_of_nonneg_left (div_le_self hF hX1) hc.le
      _ ≤ cepsFiniteRootPhaseLower vlo vhi * F := mul_le_mul_of_nonneg_right hcD hF
      _ ≤ _ := hgap
  have hR : 0 ≤ F / X := div_nonneg hF hX.le
  have hR1 : F / X ≤ 1 := (div_le_one hX).mpr hFX
  have hDelta := cepsNormal_delta_lower_bound (η := gap) (P := ratio) (l := 1) (R := F / X)
    (c := c) (C := c / 4) (by norm_num) hR hc hc1 (by positivity) hsector hfactor (by linarith)
  change c / 4 * (F / X) ≤ ‖1 - exp (-gap) * ratio‖
  simpa only [mul_one, Complex.ofReal_one, min_eq_right hR1] using hDelta

end PGM
