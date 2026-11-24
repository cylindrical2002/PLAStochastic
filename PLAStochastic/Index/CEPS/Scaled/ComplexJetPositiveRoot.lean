import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightedRoots

/-! # The quadratic upper root and the positive-side subtracted bridge direction -/

noncomputable section
open Complex
namespace PGM

private theorem real_quadratic_upper_root_nonneg {a b x t L : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L)
    (hvertex : -(L * a) / (a ^ 2 + b ^ 2) ≤ x)
    (heq : 0 ≤ (a / 2) * (x ^ 2 - t ^ 2) - b * x * t + L * x) :
    0 ≤ x := by
  have hn : 0 < a ^ 2 + b ^ 2 := by positivity
  have hv : -(L * a) ≤ x * (a ^ 2 + b ^ 2) := (div_le_iff₀ hn).mp hvertex
  by_contra hx
  have hx' : x < 0 := lt_of_not_ge hx
  have hL' : 0 < L := by
    by_contra h
    have h0 : L = 0 := le_antisymm (le_of_not_gt h) hL
    rw [h0] at hv
    nlinarith
  have hpos : 0 < x * (a ^ 2 + b ^ 2) + 2 * a * L := by nlinarith
  have hid : 2 * a * ((a / 2) * (x ^ 2 - t ^ 2) - b * x * t + L * x) =
      x * (x * (a ^ 2 + b ^ 2) + 2 * a * L) - (a * t + b * x) ^ 2 := by ring
  have hnon : 0 ≤ 2 * a * ((a / 2) * (x ^ 2 - t ^ 2) - b * x * t + L * x) :=
    mul_nonneg (by positivity) heq
  rw [hid] at hnon
  nlinarith [sq_nonneg (a * t + b * x), mul_neg_of_neg_of_pos hx' hpos]

/-- Narrow variance cones select the actual upper quadratic root. On the positive
real drift side its real part stays nonnegative throughout the closed frequency half-plane. -/
theorem cepsComplexCumulantRootBase_plus_re_nonneg (p : ℕ → ℂ)
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    {lam : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ (cepsComplexCumulantRootBase p lam z 1).re := by
  let v := p (cepsJetCode (.inl 0))
  let r := cepsComplexCumulantRootBase p lam z 1
  let q := sqrt (2 / v) * sqrt (z + (lam : ℂ) ^ 2 / (2 * v))
  have hv0 : v ≠ 0 := fun h => hv.ne' (congrArg Complex.re h)
  have hq := cepsComplexQuadraticRootProduct_sector p hv hi lam hz
  change (3 / 16 : ℝ) * ‖q‖ ≤ q.re at hq
  have hqn : 0 ≤ q.re := (mul_nonneg (by norm_num) (norm_nonneg q)).trans hq
  have hr : r.re = -(lam * v.re) / (v.re ^ 2 + v.im ^ 2) + q.re := by
    dsimp [r, cepsComplexCumulantRootBase, q, v]
    simp only [one_mul]
    rw [Complex.div_re]
    simp [Complex.normSq_apply]
    ring
  have hvertex : -(lam * v.re) / (v.re ^ 2 + v.im ^ 2) ≤ r.re := by rw [hr]; linarith
  have he := congrArg Complex.re (cepsComplexCumulantRootBase_quadratic_equation p lam z 1 hv0 (by norm_num))
  change (r ^ 2 * (v / 2) + (lam : ℂ) * r).re = z.re at he
  have heq : (v.re / 2) * (r.re ^ 2 - r.im ^ 2) - v.im * r.re * r.im + lam * r.re = z.re := by
    simp only [pow_two, add_re, mul_re, mul_im, Complex.div_re, Complex.ofReal_re,
      Complex.ofReal_im] at he
    norm_num at he
    nlinarith only [he]
  exact real_quadratic_upper_root_nonneg hv hlam hvertex (hz.trans_eq heq.symm)

/-- The same Newton radius pays the complete positive-side bridge correction direction;
the coefficients two and minus one correspond to its exact square-over-denominator form. -/
theorem cepsComplexCumulantRootModel_positive_correction_sector {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    {lam : ℝ} (hlam : 0 ≤ lam) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteWeightedRootRadius N M vlo vhi)
    (k : ℕ) :
    cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      ((2 * cepsComplexCumulantRootModel p N lam z 1 k b -
        cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re := by
  let F := |lam| + Real.sqrt ‖z‖
  let D := cepsFiniteRootPhaseLower vlo vhi
  let rp := cepsComplexCumulantRootBase p lam z 1
  let rm := cepsComplexCumulantRootBase p lam z (-1)
  let xp := cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam)
  let xm := cepsComplexCumulantRootModel p N lam z (-1) k b * (1 + b * lam)
  have hrp : 0 ≤ rp.re := cepsComplexCumulantRootBase_plus_re_nonneg p (hlo.trans_le hv) hi hlam hz
  have hgap : 2 * D * F ≤ (rp - rm).re := cepsComplexCumulantRootBase_separation_lower p hlo hv hhi hi lam hz
  have hpE : ‖xp - rp‖ ≤ D / 2 * F := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hb k
  have hmE : ‖xm - rm‖ ≤ D / 2 * F := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hb k
  have hpL := re_le_norm (-(xp - rp))
  have hmU := re_le_norm (xm - rm)
  rw [neg_re, sub_re, norm_neg] at hpL
  rw [sub_re] at hmU hgap
  have ht : ((2 * cepsComplexCumulantRootModel p N lam z 1 k b -
      cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re = 2 * xp.re - xm.re := by
    dsimp [xp, xm]
    rw [sub_mul, mul_assoc]
    simp [mul_re]
  rw [ht]
  change D / 2 * F ≤ _
  linarith

/-- The upper base root retains frequency growth after the real drift shift. -/
theorem cepsComplexCumulantRootBase_plus_re_lower (p : ℕ → ℂ) {vlo vhi : ℝ}
    (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖) - |lam| / vlo ≤
      (cepsComplexCumulantRootBase p lam z 1).re := by
  let v := p (cepsJetCode (.inl 0))
  let rp := cepsComplexCumulantRootBase p lam z 1
  let rm := cepsComplexCumulantRootBase p lam z (-1)
  have hgap := cepsComplexCumulantRootBase_separation_lower p hlo hv hhi hi lam hz
  have hnorm : ‖-(lam : ℂ) / v‖ ≤ |lam| / vlo := by
    rw [norm_div, norm_neg, norm_real, Real.norm_eq_abs]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hlo (hv.trans (re_le_norm _))
  have hshift := re_le_norm (-(-(lam : ℂ) / v))
  rw [neg_re, norm_neg] at hshift
  have he : rp.re = (-(lam : ℂ) / v).re + (rp - rm).re / 2 := by
    dsimp [rp, rm, cepsComplexCumulantRootBase, v]
    simp [mul_re]
    ring
  change _ ≤ rp.re
  rw [he]
  linarith

/-- This bounded positive-drift window retains the same stretched frequency rate as the
negative side. The offset is uniform and will be absorbed into the kernel constant. -/
theorem cepsComplexCumulantRootModel_left_window_sector {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    {lam : ℝ} (hlam : lam ≤ 1) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteWeightedRootRadius N M vlo vhi)
    (k : ℕ) :
    cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖) - 1 / vlo ≤
      (cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam)).re := by
  by_cases hl : lam ≤ 0
  · have h := (cepsComplexCumulantRootModel_weighted_individual_sector N hM hlo hp hv hhi hi lam hz hb k).1 hl
    linarith [div_pos one_pos hlo]
  · have hl0 : 0 ≤ lam := (le_of_not_ge hl)
    have hbase := cepsComplexCumulantRootBase_plus_re_lower p hlo hv hhi hi lam hz
    have hE := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
      (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hb k
    have hL := re_le_norm (-(cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam) -
      cepsComplexCumulantRootBase p lam z 1))
    rw [neg_re, sub_re, norm_neg] at hL
    have hh : |lam| / vlo ≤ 1 / vlo := div_le_div_of_nonneg_right (by rwa [abs_of_nonneg hl0]) hlo.le
    linarith

end PGM
