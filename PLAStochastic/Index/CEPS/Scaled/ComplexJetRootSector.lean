import PLAStochastic.Index.CEPS.Scaled.ComplexJetQuadraticBudget
import PLAStochastic.ForMathlib.Analysis.Complex.SqrtCone

/-! # Actual quadratic root real-part sectors on narrow complex variance regions -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexVariance_inverse_cone {v : ℂ} (hv : 0 < v.re)
    (hi : |v.im| ≤ v.re / 8) :
    0 < (2 / v).re ∧ |(2 / v).im| ≤ (2 / v).re / 8 := by
  have hv0 : v ≠ 0 := fun h => hv.ne' (congrArg Complex.re h)
  have hns : 0 < normSq v := normSq_pos.mpr hv0
  have hre : (2 / v).re = 2 * v.re / normSq v := by simp [Complex.div_re]
  have him : (2 / v).im = -(2 * v.im) / normSq v := by simp [Complex.div_im, neg_div]
  constructor
  · rw [hre]
    exact div_pos (mul_pos (by norm_num) hv) hns
  · rw [him, abs_div, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos hns, hre]
    calc
      _ ≤ 2 * (v.re / 8) / normSq v :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hi (by norm_num)) hns.le
      _ = _ := by ring

theorem cepsComplexQuadraticRootProduct_sector (p : ℕ → ℂ)
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    (3 / 16 : ℝ) * ‖sqrt (2 / p (cepsJetCode (.inl 0))) *
      sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))))‖ ≤
    (sqrt (2 / p (cepsJetCode (.inl 0))) *
      sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))))).re := by
  have hv0 : p (cepsJetCode (.inl 0)) ≠ 0 := fun h => hv.ne' (congrArg Complex.re h)
  have hvInv := cepsComplexVariance_inverse_cone hv hi
  have hrad : 0 ≤ (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))).re := by
    rw [add_re, cepsComplexQuadraticRadicand_re _ hv0 lam]
    exact add_nonneg hz (by positivity)
  exact complex_sqrt_product_re_lower hvInv.1 hvInv.2 hrad

/-- The actual two quadratic roots have a uniform real-part separation throughout the
right frequency half-plane on a narrow complex variance cone, including their common zero. -/
theorem cepsComplexCumulantRootBase_difference_sector (p : ℕ → ℂ)
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    (3 / 16 : ℝ) * ‖cepsComplexCumulantRootBase p lam z 1 -
      cepsComplexCumulantRootBase p lam z (-1)‖ ≤
    (cepsComplexCumulantRootBase p lam z 1 - cepsComplexCumulantRootBase p lam z (-1)).re := by
  let q := sqrt (2 / p (cepsJetCode (.inl 0))) *
    sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))))
  have he : cepsComplexCumulantRootBase p lam z 1 - cepsComplexCumulantRootBase p lam z (-1) = 2 * q := by
    dsimp [cepsComplexCumulantRootBase, q]
    ring
  have hq := cepsComplexQuadraticRootProduct_sector p hv hi lam hz
  change (3 / 16 : ℝ) * ‖q‖ ≤ q.re at hq
  rw [he, norm_mul, norm_ofNat, mul_re]
  norm_num
  linarith

/-- One individual quadratic root has a positive real-part budget on each drift side. -/
theorem cepsComplexCumulantRootBase_individual_sector (p : ℕ → ℂ)
    {vlo vhi : ℝ} (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    (lam ≤ 0 → cepsFiniteQuadraticGapLower vlo vhi / (8 * vhi) * (|lam| + Real.sqrt ‖z‖) ≤
      (cepsComplexCumulantRootBase p lam z 1).re) ∧
    (0 ≤ lam → (cepsComplexCumulantRootBase p lam z (-1)).re ≤
      -(cepsFiniteQuadraticGapLower vlo vhi / (8 * vhi) * (|lam| + Real.sqrt ‖z‖))) := by
  let v := p (cepsJetCode (.inl 0))
  let q := sqrt (2 / v) * sqrt (z + (lam : ℂ) ^ 2 / (2 * v))
  let F := |lam| + Real.sqrt ‖z‖
  let c := cepsFiniteQuadraticGapLower vlo vhi
  have hvr : 0 < v.re := hlo.trans_le hv
  have hv0 : v ≠ 0 := fun h => hvr.ne' (congrArg Complex.re h)
  have hVH : 0 < vhi := (hlo.trans_le (hv.trans (re_le_norm _))).trans_le hhi
  have hgap := cepsComplexCumulantRootGap_norm_lower p hlo hv hhi lam hz 1 (by norm_num)
  have he : cepsComplexCumulantRootGap p lam z 1 = v * q := by
    rw [cepsComplexCumulantRootGap_eq p lam z 1 hv0]
    dsimp [v, q]
    ring
  rw [he, norm_mul] at hgap
  have hqn : c * F ≤ vhi * ‖q‖ := hgap.trans (mul_le_mul_of_nonneg_right hhi (norm_nonneg _))
  have hq := cepsComplexQuadraticRootProduct_sector p hvr hi lam hz
  change (3 / 16 : ℝ) * ‖q‖ ≤ q.re at hq
  have hphase : c / (8 * vhi) * F ≤ q.re := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 8 * vhi)]
    nlinarith [norm_nonneg q]
  have hshift : (-(lam : ℂ) / v).re = -lam * v.re / normSq v := by simp [Complex.div_re]
  constructor
  · intro hl
    have hnon : 0 ≤ (-(lam : ℂ) / v).re := by
      rw [hshift]
      exact div_nonneg (mul_nonneg (neg_nonneg.mpr hl) hvr.le) (normSq_nonneg _)
    have hroot : (cepsComplexCumulantRootBase p lam z 1).re = (-(lam : ℂ) / v).re + q.re := by
      dsimp [cepsComplexCumulantRootBase, v, q]
      simp
    rw [hroot]
    linarith
  · intro hl
    have hnon : (-(lam : ℂ) / v).re ≤ 0 := by
      rw [hshift]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hl) hvr.le) (normSq_nonneg _)
    have hroot : (cepsComplexCumulantRootBase p lam z (-1)).re = (-(lam : ℂ) / v).re - q.re := by
      dsimp [cepsComplexCumulantRootBase, v, q]
      simp
      ring
    rw [hroot]
    linarith

end PGM
