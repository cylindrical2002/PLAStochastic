import PLAStochastic.Index.CEPS.Scaled.ComplexJetPositiveRoot

/-! # Both quadratic root sides and both complete-pair directions for all real drifts -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexCumulantRootBase_plus_re_nonneg_all (p : ℕ → ℂ)
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (cepsComplexCumulantRootBase p lam z 1).re := by
  by_cases hl : 0 ≤ lam
  · exact cepsComplexCumulantRootBase_plus_re_nonneg p hv hi hl hz
  · let v := p (cepsJetCode (.inl 0))
    let q := sqrt (2 / v) * sqrt (z + (lam : ℂ) ^ 2 / (2 * v))
    have hq := cepsComplexQuadraticRootProduct_sector p hv hi lam hz
    change (3 / 16 : ℝ) * ‖q‖ ≤ q.re at hq
    have hqn : 0 ≤ q.re := (mul_nonneg (by norm_num) (norm_nonneg q)).trans hq
    have hshift : 0 ≤ (-(lam : ℂ) / v).re := by
      rw [Complex.div_re]
      simp only [neg_re, ofReal_re, neg_im, ofReal_im, neg_zero, zero_mul, zero_div, add_zero]
      exact div_nonneg (mul_nonneg (by linarith : 0 ≤ -lam) hv.le) (normSq_nonneg _)
    simpa [cepsComplexCumulantRootBase, v, q] using add_nonneg hshift hqn

theorem cepsComplexCumulantRootBase_reflect (p : ℕ → ℂ) (lam : ℝ) (z : ℂ) :
    cepsComplexCumulantRootBase p lam z (-1) = -cepsComplexCumulantRootBase p (-lam) z 1 := by
  unfold cepsComplexCumulantRootBase
  simp only [ofReal_neg, neg_sq]
  ring

theorem cepsComplexCumulantRootBase_minus_re_nonpos_all (p : ℕ → ℂ)
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    (cepsComplexCumulantRootBase p lam z (-1)).re ≤ 0 := by
  rw [cepsComplexCumulantRootBase_reflect, neg_re]
  exact neg_nonpos.mpr (cepsComplexCumulantRootBase_plus_re_nonneg_all p hv hi (-lam) hz)

/-- The two combinations are the exact exponential directions occurring when the
complete entrance square is multiplied by the bridge or its half-line subtraction. -/
theorem cepsComplexCumulantRootModel_pair_directions {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteWeightedRootRadius N M vlo vhi)
    (k : ℕ) :
    cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      ((2 * cepsComplexCumulantRootModel p N lam z 1 k b -
        cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re ∧
    cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      ((cepsComplexCumulantRootModel p N lam z 1 k b -
        2 * cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re := by
  let F := |lam| + Real.sqrt ‖z‖
  let D := cepsFiniteRootPhaseLower vlo vhi
  let rp := cepsComplexCumulantRootBase p lam z 1
  let rm := cepsComplexCumulantRootBase p lam z (-1)
  let xp := cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam)
  let xm := cepsComplexCumulantRootModel p N lam z (-1) k b * (1 + b * lam)
  have hrp : 0 ≤ rp.re := cepsComplexCumulantRootBase_plus_re_nonneg_all p (hlo.trans_le hv) hi lam hz
  have hrm : rm.re ≤ 0 := cepsComplexCumulantRootBase_minus_re_nonpos_all p (hlo.trans_le hv) hi lam hz
  have hgap : 2 * D * F ≤ (rp - rm).re :=
    cepsComplexCumulantRootBase_separation_lower p hlo hv hhi hi lam hz
  have hpE : ‖xp - rp‖ ≤ D / 2 * F := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hb k
  have hmE : ‖xm - rm‖ ≤ D / 2 * F := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hb k
  have hpL := re_le_norm (-(xp - rp))
  have hmU := re_le_norm (xm - rm)
  rw [neg_re, sub_re, norm_neg] at hpL
  rw [sub_re] at hmU hgap
  have he₁ : ((2 * cepsComplexCumulantRootModel p N lam z 1 k b -
      cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re =
      2 * xp.re - xm.re := by
    dsimp [xp, xm]
    rw [sub_mul, mul_assoc]
    simp [mul_re]
  have he₂ : ((cepsComplexCumulantRootModel p N lam z 1 k b -
      2 * cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re =
      xp.re - 2 * xm.re := by
    dsimp [xp, xm]
    rw [sub_mul, mul_assoc]
    simp [mul_re]
  rw [he₁, he₂]
  change D / 2 * F ≤ _ ∧ D / 2 * F ≤ _
  constructor <;> linarith

end PGM
