import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootSector

/-! # Uniform real-part budgets for the actual finite roots with complex width -/

noncomputable section
open Complex
namespace PGM

def cepsFiniteRootPhaseLower (vlo vhi : ℝ) : ℝ :=
  cepsFiniteQuadraticGapLower vlo vhi / (8 * vhi)

def cepsFiniteWeightedRootRadius (N : ℕ) (M vlo vhi : ℝ) : ℝ :=
  min (cepsFiniteRootScaleRadius (cepsFiniteQuadraticRootBound vlo)
    (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M) M)
    (cepsFiniteRootPhaseLower vlo vhi /
      (2 * (cepsFiniteRootErrorConstant (cepsFiniteQuadraticRootBound vlo)
        (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M) +
        2 * cepsFiniteQuadraticRootBound vlo)))

theorem cepsFiniteWeightedRootRadius_pos (N : ℕ) {M vlo vhi : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hhi : 0 < vhi) :
    0 < cepsFiniteWeightedRootRadius N M vlo vhi := by
  have hA := cepsFiniteQuadraticRootBound_pos hlo
  have hc := cepsFiniteQuadraticGapLower_pos (vhi := vhi) hlo
  have hK := cepsFiniteRootErrorConstant_pos hA hc (mul_nonneg (Nat.cast_nonneg N) hM)
  have hδ := (cepsFiniteRootScaleRadius_admissible hA hc
    (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  unfold cepsFiniteWeightedRootRadius cepsFiniteRootPhaseLower
  exact lt_min hδ (div_pos (div_pos hc (by positivity)) (by positivity))

theorem cepsComplexCumulantRootModel_weighted_error {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi) (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re)
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤
      cepsFiniteWeightedRootRadius N M vlo vhi) (k : ℕ) :
    ‖cepsComplexCumulantRootModel p N lam z sign k b * (1 + b * lam) -
      cepsComplexCumulantRootBase p lam z sign‖ ≤
      cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let K := cepsFiniteRootErrorConstant A (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M)
  let F := |lam| + Real.sqrt ‖z‖
  let D := cepsFiniteRootPhaseLower vlo vhi
  let g := cepsComplexCumulantRootModel p N lam z sign k b
  let r := cepsComplexCumulantRootBase p lam z sign
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hK : 0 < K := cepsFiniteRootErrorConstant_pos hA
    (cepsFiniteQuadraticGapLower_pos hlo) (mul_nonneg (Nat.cast_nonneg N) hM)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hlF : |lam| ≤ F := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hδ := hb.trans (min_le_left _ _)
  have hs := cepsComplexCumulantRootModel_right_stability N hM hlo hp hv hhi lam hz hsign hδ k
  change ‖g - r‖ ≤ K * ‖b‖ * F ^ 2 ∧ ‖g‖ ≤ 2 * A * F at hs
  have hsmall : (K + 2 * A) * (‖b‖ * F) ≤ D / 2 := by
    have hh := hb.trans (min_le_right _ _)
    change ‖b‖ * F ≤ D / (2 * (K + 2 * A)) at hh
    have hd : 0 < 2 * (K + 2 * A) := by positivity
    have hh' := (le_div_iff₀ hd).mp hh
    linarith
  have he : g * (1 + b * lam) - r = (g - r) + g * (b * lam) := by ring
  change ‖g * (1 + b * lam) - r‖ ≤ D / 2 * F
  rw [he]
  calc
    _ ≤ ‖g - r‖ + ‖g * (b * lam)‖ := norm_add_le _ _
    _ ≤ K * ‖b‖ * F ^ 2 + (2 * A * F) * (‖b‖ * F) := by
      apply add_le_add hs.1
      rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs]
      gcongr
      exact hs.2
    _ = ((K + 2 * A) * (‖b‖ * F)) * F := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF

/-- The same positive complex scale radius pays both drift sides and every Newton iterate. -/
theorem cepsComplexCumulantRootModel_weighted_individual_sector {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteWeightedRootRadius N M vlo vhi)
    (k : ℕ) :
    (lam ≤ 0 → cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖) ≤
      (cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam)).re) ∧
    (0 ≤ lam → (cepsComplexCumulantRootModel p N lam z (-1) k b * (1 + b * lam)).re ≤
      -(cepsFiniteRootPhaseLower vlo vhi / 2 * (|lam| + Real.sqrt ‖z‖))) := by
  have hbase := cepsComplexCumulantRootBase_individual_sector p hlo hv hhi hi lam hz
  constructor
  · intro hl
    have herror := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
      (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hb k
    have hphase := hbase.1 hl
    have hre := re_le_norm
      (-(cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam) -
        cepsComplexCumulantRootBase p lam z 1))
    rw [neg_re, sub_re, norm_neg] at hre
    dsimp [cepsFiniteRootPhaseLower] at herror ⊢
    linarith
  · intro hl
    have herror := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
      (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hb k
    have hphase := hbase.2 hl
    have hre := re_le_norm
      (cepsComplexCumulantRootModel p N lam z (-1) k b * (1 + b * lam) -
        cepsComplexCumulantRootBase p lam z (-1))
    rw [sub_re] at hre
    dsimp [cepsFiniteRootPhaseLower] at herror ⊢
    linarith

theorem cepsComplexCumulantRootBase_separation_lower (p : ℕ → ℂ)
    {vlo vhi : ℝ} (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) :
    2 * cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖) ≤
      (cepsComplexCumulantRootBase p lam z 1 - cepsComplexCumulantRootBase p lam z (-1)).re := by
  let V := p (cepsJetCode (.inl 0))
  let g := cepsComplexCumulantRootBase p lam z 1 - cepsComplexCumulantRootBase p lam z (-1)
  have hV : 0 < V.re := hlo.trans_le hv
  have hV0 : V ≠ 0 := fun h => hV.ne' (congrArg Complex.re h)
  have hVH : 0 < vhi := (hlo.trans_le (hv.trans (re_le_norm _))).trans_le hhi
  have hg : cepsComplexCumulantRootGap p lam z 1 = V / 2 * g := by
    rw [cepsComplexCumulantRootGap_eq p lam z 1 hV0]
    dsimp [V, g, cepsComplexCumulantRootBase]
    ring
  have hgap := cepsComplexCumulantRootGap_norm_lower p hlo hv hhi lam hz 1 (by norm_num)
  rw [hg, norm_mul, norm_div, norm_ofNat] at hgap
  have hgphase := cepsComplexCumulantRootBase_difference_sector p hV hi lam hz
  change (3 / 16 : ℝ) * ‖g‖ ≤ g.re at hgphase
  have hmajor : cepsFiniteQuadraticGapLower vlo vhi * (|lam| + Real.sqrt ‖z‖) ≤
      4 * vhi * g.re := by
    calc
      _ ≤ ‖V‖ / 2 * ‖g‖ := hgap
      _ ≤ vhi / 2 * ‖g‖ := by gcongr
      _ ≤ 4 * vhi * g.re := by
        have hh := mul_le_mul_of_nonneg_left hgphase (by positivity : 0 ≤ 4 * vhi)
        nlinarith [norm_nonneg g]
  unfold cepsFiniteRootPhaseLower
  calc
    _ = (cepsFiniteQuadraticGapLower vlo vhi * (|lam| + Real.sqrt ‖z‖)) / (4 * vhi) := by ring
    _ ≤ g.re := (div_le_iff₀ (by positivity : 0 < 4 * vhi)).mpr (by nlinarith [hmajor])

/-- The weighted actual two-root separation retains a positive real part on the same
uniform complex scale radius as the individual root directions. -/
theorem cepsComplexCumulantRootModel_weighted_separation {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteWeightedRootRadius N M vlo vhi)
    (k : ℕ) :
    cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖) ≤
      ((cepsComplexCumulantRootModel p N lam z 1 k b -
        cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re := by
  have hbase := cepsComplexCumulantRootBase_separation_lower p hlo hv hhi hi lam hz
  have hplus := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hb k
  have hminus := cepsComplexCumulantRootModel_weighted_error N hM hlo hp hv hhi lam hz
    (Or.inr rfl : (-1 : ℂ) = 1 ∨ (-1 : ℂ) = -1) hb k
  have hreP := re_le_norm (-(cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam) -
    cepsComplexCumulantRootBase p lam z 1))
  have hreM := re_le_norm (cepsComplexCumulantRootModel p N lam z (-1) k b * (1 + b * lam) -
    cepsComplexCumulantRootBase p lam z (-1))
  rw [neg_re, sub_re, norm_neg] at hreP
  rw [sub_re] at hreM
  rw [sub_mul, sub_re]
  rw [sub_re] at hbase
  linarith

end PGM
