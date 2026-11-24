import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootMagnitude

/-! # Concrete quadratic base-root and gap budgets for bounded complex variance inputs -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexCumulantRootGap_norm_sq (p : ℕ → ℂ) (lam : ℝ) (z sign : ℂ)
    (hv : p (cepsJetCode (.inl 0)) ≠ 0) (hs : ‖sign‖ = 1) :
    ‖cepsComplexCumulantRootGap p lam z sign‖ ^ 2 =
      2 * ‖p (cepsJetCode (.inl 0))‖ *
        ‖z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))‖ := by
  rw [cepsComplexCumulantRootGap_eq p lam z sign hv]
  simp only [norm_mul, mul_pow, hs, mul_one,
    norm_complex_sqrt_sq, norm_div, norm_ofNat]
  field_simp [norm_ne_zero_iff.mpr hv]

theorem cepsFiniteQuadraticRootBound_pos {vlo : ℝ} (hlo : 0 < vlo) :
    0 < cepsFiniteQuadraticRootBound vlo := by
  unfold cepsFiniteQuadraticRootBound
  positivity

theorem cepsFiniteQuadraticGapLower_pos {vlo vhi : ℝ} (hlo : 0 < vlo) :
    0 < cepsFiniteQuadraticGapLower vlo vhi := by
  unfold cepsFiniteQuadraticGapLower cepsFiniteRadicandCoercivity
  positivity

/-- A lower variance real-part bound controls both actual quadratic base roots. -/
theorem cepsComplexCumulantRootBase_norm_le (p : ℕ → ℂ) {vlo : ℝ}
    (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (lam : ℝ) (z sign : ℂ) (hsign : ‖sign‖ ≤ 1) :
    ‖cepsComplexCumulantRootBase p lam z sign‖ ≤
      cepsFiniteQuadraticRootBound vlo * (|lam| + Real.sqrt ‖z‖) := by
  let v := p (cepsJetCode (.inl 0))
  let w := z + (lam : ℂ) ^ 2 / (2 * v)
  let q := sqrt (2 / v) * sqrt w
  let F := |lam| + Real.sqrt ‖z‖
  let C := 2 / vlo + 1 / vlo ^ 2
  have hnv : vlo ≤ ‖v‖ := hv.trans (re_le_norm _)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hlF : |lam| ≤ F := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hsF : Real.sqrt ‖z‖ ≤ F := le_add_of_nonneg_left (abs_nonneg _)
  have hlF2 : lam ^ 2 ≤ F ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hlF 2
  have hzF2 : ‖z‖ ≤ F ^ 2 := by
    rw [← Real.sq_sqrt (norm_nonneg z)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsF 2
  have hw : ‖w‖ ≤ ‖z‖ + lam ^ 2 / (2 * vlo) := by
    calc
      _ ≤ ‖z‖ + ‖(lam : ℂ) ^ 2 / (2 * v)‖ := norm_add_le _ _
      _ ≤ _ := by
        apply add_le_add le_rfl
        rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, norm_mul, norm_ofNat]
        exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have hq2 : ‖q‖ ^ 2 ≤ C * F ^ 2 := by
    calc
      _ = (2 / ‖v‖) * ‖w‖ := by
        dsimp [q]
        rw [norm_mul, mul_pow, norm_complex_sqrt_sq, norm_complex_sqrt_sq, norm_div, norm_ofNat]
      _ ≤ (2 / vlo) * (‖z‖ + lam ^ 2 / (2 * vlo)) := by
        apply mul_le_mul _ hw (norm_nonneg _) (by positivity)
        exact div_le_div_of_nonneg_left (by norm_num) hlo hnv
      _ ≤ (2 / vlo) * (F ^ 2 + F ^ 2 / (2 * vlo)) := by gcongr
      _ = C * F ^ 2 := by dsimp [C]; ring
  have hq : ‖q‖ ≤ Real.sqrt C * F := by
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num : 2 ≠ 0)).mp
    rw [mul_pow, Real.sq_sqrt (by dsimp [C]; positivity)]
    exact hq2
  have hterm : ‖sign * sqrt (2 / v) * sqrt w‖ ≤ ‖q‖ := by
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) hsign
  have hshift : ‖-(lam : ℂ) / v‖ ≤ F / vlo := by
    rw [norm_div, norm_neg, norm_real, Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hlo hnv).trans
      (div_le_div_of_nonneg_right hlF hlo.le)
  change ‖-(lam : ℂ) / v + sign * sqrt (2 / v) * sqrt w‖ ≤ _
  calc
    _ ≤ ‖-(lam : ℂ) / v‖ + ‖sign * sqrt (2 / v) * sqrt w‖ := norm_add_le _ _
    _ ≤ F / vlo + Real.sqrt C * F := add_le_add hshift (hterm.trans hq)
    _ = _ := by dsimp [cepsFiniteQuadraticRootBound, C, F]; ring

/-- The gap lower bound is uniform on the whole right frequency half-plane and on every
complex variance region with the stated real-part and norm bounds. -/
theorem cepsComplexCumulantRootGap_norm_lower (p : ℕ → ℂ) {vlo vhi : ℝ}
    (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi) (lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (sign : ℂ) (hs : ‖sign‖ = 1) :
    cepsFiniteQuadraticGapLower vlo vhi * (|lam| + Real.sqrt ‖z‖) ≤
      ‖cepsComplexCumulantRootGap p lam z sign‖ := by
  let v := p (cepsJetCode (.inl 0))
  let w := z + (lam : ℂ) ^ 2 / (2 * v)
  let F := |lam| + Real.sqrt ‖z‖
  let C := cepsFiniteRadicandCoercivity vlo vhi
  let c := cepsFiniteQuadraticGapLower vlo vhi
  have hC : 0 < C := by dsimp [C, cepsFiniteRadicandCoercivity]; positivity
  have hc : 0 < c := cepsFiniteQuadraticGapLower_pos hlo
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hnv : vlo ≤ ‖v‖ := hv.trans (re_le_norm _)
  have hv0 : v ≠ 0 := norm_pos_iff.mp (hlo.trans_le hnv)
  have hco := cepsComplexQuadraticRadicand_coercive hlo hv hhi lam hz
  have hF2 : F ^ 2 ≤ 2 * (lam ^ 2 + ‖z‖) := by
    dsimp [F]
    nlinarith [Real.sq_sqrt (norm_nonneg z), sq_abs lam,
      sq_nonneg (|lam| - Real.sqrt ‖z‖)]
  have hFco : F ^ 2 ≤ 2 * C * ‖w‖ :=
    hF2.trans ((mul_le_mul_of_nonneg_left hco (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring))
  have hc2 : c ^ 2 = vlo / C := Real.sq_sqrt (div_pos hlo hC).le
  have htarget : (c * F) ^ 2 ≤ 2 * vlo * ‖w‖ := by
    rw [mul_pow, hc2]
    calc
      _ ≤ (vlo / C) * (2 * C * ‖w‖) := mul_le_mul_of_nonneg_left hFco (by positivity)
      _ = _ := by field_simp
  have hgap : 2 * vlo * ‖w‖ ≤ ‖cepsComplexCumulantRootGap p lam z sign‖ ^ 2 := by
    rw [cepsComplexCumulantRootGap_norm_sq p lam z sign hv0 hs]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnv (by norm_num)) (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ (mul_nonneg hc.le hF) (norm_nonneg _)
    (by norm_num : 2 ≠ 0)).mp (htarget.trans hgap)

theorem cepsComplexCumulantRootModel_joint_zero (p : ℕ → ℂ) (N k : ℕ) (sign b : ℂ) :
    cepsComplexCumulantRootModel p N 0 0 sign k b = 0 := by
  induction k with
  | zero => simp [cepsComplexCumulantRootModel, cepsComplexCumulantRootBase]
  | succ k ih => simp [cepsComplexCumulantRootModel, quadraticNewtonStep, ih]

/-- All root iterations have one explicit scale budget uniform on complex variance
regions, all real drifts and all right-half-plane frequencies, including the joint origin. -/
theorem cepsComplexCumulantRootModel_right_stability {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤
      cepsFiniteRootScaleRadius (cepsFiniteQuadraticRootBound vlo)
        (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M) M) (k : ℕ) :
    ‖cepsComplexCumulantRootModel p N lam z sign k b -
      cepsComplexCumulantRootBase p lam z sign‖ ≤
        cepsFiniteRootErrorConstant (cepsFiniteQuadraticRootBound vlo)
          (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M) * ‖b‖ * (|lam| + Real.sqrt ‖z‖) ^ 2 ∧
    ‖cepsComplexCumulantRootModel p N lam z sign k b‖ ≤
      2 * cepsFiniteQuadraticRootBound vlo * (|lam| + Real.sqrt ‖z‖) := by
  have hsg : ‖sign‖ = 1 := by rcases hsign with rfl | rfl <;> norm_num
  have hsg2 : sign ^ 2 = 1 := by rcases hsign with rfl | rfl <;> norm_num
  by_cases hne : lam ≠ 0 ∨ z ≠ 0
  · have hF : 0 < |lam| + Real.sqrt ‖z‖ := by
      rcases hne with hl | hz0
      · exact add_pos_of_pos_of_nonneg (abs_pos.mpr hl) (Real.sqrt_nonneg _)
      · exact add_pos_of_nonneg_of_pos (abs_nonneg _) (Real.sqrt_pos.mpr (norm_pos_iff.mpr hz0))
    have hv0 : p (cepsJetCode (.inl 0)) ≠ 0 := by
      exact norm_pos_iff.mp (hlo.trans_le (hv.trans (re_le_norm _)))
    have hl : ‖(lam : ℂ)‖ ≤ |lam| + Real.sqrt ‖z‖ := by
      rw [norm_real, Real.norm_eq_abs]
      exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
    have hzn : ‖z‖ ≤ (|lam| + Real.sqrt ‖z‖) ^ 2 := by
      calc
        ‖z‖ = Real.sqrt ‖z‖ ^ 2 := (Real.sq_sqrt (norm_nonneg z)).symm
        _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _)
          (le_add_of_nonneg_left (abs_nonneg _)) 2
    exact cepsComplexCumulantRootModel_stability N hM
      (cepsFiniteQuadraticRootBound_pos hlo) (cepsFiniteQuadraticGapLower_pos hlo) hF hp hv0
      lam z sign hsg2 hl hzn (cepsComplexCumulantRootBase_norm_le p hlo hv lam z sign hsg.le)
      (cepsComplexCumulantRootGap_norm_lower p hlo hv hhi lam hz sign hsg) hb k
  · push Not at hne
    rw [hne.1, hne.2, cepsComplexCumulantRootModel_joint_zero]
    have hbase : cepsComplexCumulantRootBase p 0 0 sign = 0 := by simp [cepsComplexCumulantRootBase]
    simp only [hbase, sub_self, norm_zero, abs_zero, Real.sqrt_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
    exact ⟨le_rfl, le_rfl⟩

end PGM
