import PLAStochastic.Index.CEPS.Scaled.ComplexJetRootSides

/-! # Admissible frequencies for the finite quadratic roots beyond the right half-plane

The right-half-plane root facts of `Scaled/ComplexJet*` use `0 ≤ z.re` only through
radicand coercivity, a half-norm real-part sector of the radicand and the sign of the
real part of one base root. This file isolates these facts in `CepsRootAdmissible`
and reproves the bottom root budgets from it.
-/

noncomputable section
open Complex
namespace PGM

/-- Frequency admissibility for the finite quadratic roots with variance bounds `vlo`, `vhi`.
The joint origin is excluded. -/
structure CepsRootAdmissible (p : ℕ → ℂ) (vlo vhi : ℝ) (lam : ℝ) (z : ℂ) : Prop where
  pos : 0 < |lam| + Real.sqrt ‖z‖
  coercive : lam ^ 2 + ‖z‖ ≤ cepsFiniteRadicandCoercivity vlo vhi *
    ‖z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))‖
  sector : -‖z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))‖ ≤
    2 * (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))).re
  plus : 0 ≤ lam → -(cepsFiniteRootPhaseLower vlo vhi / 4 * (|lam| + Real.sqrt ‖z‖)) ≤
    (cepsComplexCumulantRootBase p lam z 1).re
  minus : lam ≤ 0 → (cepsComplexCumulantRootBase p lam z (-1)).re ≤
    cepsFiniteRootPhaseLower vlo vhi / 4 * (|lam| + Real.sqrt ‖z‖)

/-- A half-norm real-part sector suffices for the principal square-root sector. -/
theorem complex_sqrt_re_ge_half_norm_of_sector {w : ℂ} (hw : -‖w‖ ≤ 2 * w.re) :
    ‖sqrt w‖ / 2 ≤ (sqrt w).re := by
  have hre : 0 ≤ (sqrt w).re := by
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hs : (sqrt w).re ^ 2 - (sqrt w).im ^ 2 = w.re := by
    have hh := congrArg Complex.re (sqrt_sq_eq w)
    simpa [pow_two, mul_re] using hh
  have hn := Complex.sq_norm_sub_sq_re (sqrt w)
  have hnw := norm_complex_sqrt_sq w
  have h4 : (‖sqrt w‖ / 2) ^ 2 ≤ (sqrt w).re ^ 2 := by nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) hre two_ne_zero).mp h4

theorem complex_sqrt_product_re_lower_of_sector {z w : ℂ} (hz : 0 < z.re)
    (hi : |z.im| ≤ z.re / 8) (hw : -‖w‖ ≤ 2 * w.re) :
    (3 / 16 : ℝ) * ‖sqrt z * sqrt w‖ ≤ (sqrt z * sqrt w).re := by
  have hzR := complex_sqrt_re_ge_half_norm hz.le
  have hwR := complex_sqrt_re_ge_half_norm_of_sector hw
  have hzI := complex_sqrt_im_le_norm_div_sixteen hz hi
  have hwI := abs_im_le_norm (sqrt w)
  have hprod : ‖sqrt z‖ / 2 * (‖sqrt w‖ / 2) ≤ (sqrt z).re * (sqrt w).re :=
    mul_le_mul hzR hwR (by positivity) (by linarith [norm_nonneg (sqrt z)])
  have him : (sqrt z).im * (sqrt w).im ≤ ‖sqrt z‖ / 16 * ‖sqrt w‖ := by
    calc
      _ ≤ |(sqrt z).im * (sqrt w).im| := le_abs_self _
      _ = |(sqrt z).im| * |(sqrt w).im| := abs_mul _ _
      _ ≤ _ := mul_le_mul hzI hwI (abs_nonneg _) (by positivity)
  rw [mul_re, norm_mul]
  nlinarith

namespace CepsRootAdmissible

variable {p : ℕ → ℂ} {vlo vhi : ℝ} {lam : ℝ} {z : ℂ}

theorem sq_add_norm_pos (h : CepsRootAdmissible p vlo vhi lam z) : 0 < lam ^ 2 + ‖z‖ := by
  by_contra hle
  have hl : lam ^ 2 + ‖z‖ ≤ 0 := le_of_not_gt hle
  have hl0 : lam = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
  have hz0 : ‖z‖ = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
  have := h.pos
  rw [hl0, hz0, abs_zero, Real.sqrt_zero, add_zero] at this
  exact lt_irrefl 0 this

theorem radicand_ne (h : CepsRootAdmissible p vlo vhi lam z) :
    z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))) ≠ 0 := by
  intro hw
  have hc := h.coercive
  rw [hw, norm_zero, mul_zero] at hc
  exact (lt_irrefl 0) (h.sq_add_norm_pos.trans_le hc)

theorem radicand_mem_slitPlane (h : CepsRootAdmissible p vlo vhi lam z) :
    z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))) ∈ slitPlane := by
  set w := z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))) with hwdef
  have hw0 : w ≠ 0 := h.radicand_ne
  have hs : -‖w‖ ≤ 2 * w.re := h.sector
  rw [mem_slitPlane_iff]
  by_cases him : w.im = 0
  · left
    have hn : |w.re| = ‖w‖ := Complex.abs_re_eq_norm.mpr him
    by_contra hle
    have hle' : w.re ≤ 0 := le_of_not_gt hle
    rw [abs_of_nonpos hle'] at hn
    have hre0 : w.re = 0 := by linarith
    exact hw0 (Complex.ext hre0 him)
  · exact Or.inr him

/-- Admissible frequencies lie in the actual root chart. -/
theorem chart (h : CepsRootAdmissible p vlo vhi lam z)
    (hp : 0 < (p (cepsJetCode (.inl 0))).re) : CepsComplexJetRootChart p lam z := by
  let v := p (cepsJetCode (.inl 0))
  have hv : v ≠ 0 := by
    intro h0
    have hzero : (p (cepsJetCode (.inl 0))).re = 0 := congrArg Complex.re h0
    exact hp.ne' hzero
  have hi : 0 < v⁻¹.re := by
    rw [inv_re]
    exact div_pos hp (normSq_pos.mpr hv)
  have hr : 2 / v ∈ slitPlane := by
    rw [mem_slitPlane_iff]
    left
    rw [div_eq_mul_inv, mul_re]
    norm_num
    simpa only [inv_re] using hi
  have hs (w : ℂ) (hw : w ≠ 0) : sqrt w ≠ 0 := by
    intro h0
    have he := sqrt_sq_eq w
    rw [h0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at he
    exact hw he.symm
  have hrad0 := h.radicand_ne
  have hg (sign : ℂ) (hsg : sign ≠ 0) : cepsComplexCumulantRootGap p lam z sign ≠ 0 := by
    rw [cepsComplexCumulantRootGap_eq p lam z sign hv]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hv hsg)
      (hs _ (div_ne_zero (by norm_num) hv))) (hs _ hrad0)
  exact ⟨hv, hr, h.radicand_mem_slitPlane, hg 1 (by norm_num), hg (-1) (by norm_num)⟩

/-- Reflection of the drift keeps admissibility. -/
theorem neg_lam (h : CepsRootAdmissible p vlo vhi lam z) :
    CepsRootAdmissible p vlo vhi (-lam) z := by
  have hsq : ((-lam : ℝ) : ℂ) ^ 2 = (lam : ℂ) ^ 2 := by push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa only [abs_neg] using h.pos
  · simpa only [hsq, neg_sq] using h.coercive
  · simpa only [hsq] using h.sector
  · intro hl
    have hm := h.minus (by linarith)
    rw [cepsComplexCumulantRootBase_reflect, neg_re] at hm
    simp only [abs_neg]
    linarith
  · intro hl
    have hm := h.plus (by linarith)
    rw [cepsComplexCumulantRootBase_reflect, neg_neg, neg_re]
    simp only [abs_neg] at hm ⊢
    linarith

end CepsRootAdmissible

/-- The gap lower bound on admissible frequencies. -/
theorem cepsComplexCumulantRootGap_norm_lower_adm (p : ℕ → ℂ) {vlo vhi : ℝ}
    (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) (sign : ℂ) (hs : ‖sign‖ = 1) :
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
  have hco : lam ^ 2 + ‖z‖ ≤ C * ‖w‖ := hz.coercive
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

/-- Uniform finite Newton stability on admissible frequencies. -/
theorem cepsComplexCumulantRootModel_stability_adm {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z)
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
  have hv0 : p (cepsJetCode (.inl 0)) ≠ 0 :=
    norm_pos_iff.mp (hlo.trans_le (hv.trans (re_le_norm _)))
  have hl : ‖(lam : ℂ)‖ ≤ |lam| + Real.sqrt ‖z‖ := by
    rw [norm_real, Real.norm_eq_abs]
    exact le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hzn : ‖z‖ ≤ (|lam| + Real.sqrt ‖z‖) ^ 2 := by
    calc
      ‖z‖ = Real.sqrt ‖z‖ ^ 2 := (Real.sq_sqrt (norm_nonneg z)).symm
      _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (le_add_of_nonneg_left (abs_nonneg _)) 2
  exact cepsComplexCumulantRootModel_stability N hM
    (cepsFiniteQuadraticRootBound_pos hlo) (cepsFiniteQuadraticGapLower_pos hlo) hz.pos hp hv0
    lam z sign hsg2 hl hzn (cepsComplexCumulantRootBase_norm_le p hlo hv lam z sign hsg.le)
    (cepsComplexCumulantRootGap_norm_lower_adm p hlo hv lam hz sign hsg) hb k

theorem cepsComplexQuadraticRootProduct_sector_adm (p : ℕ → ℂ) {vlo vhi : ℝ}
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) :
    (3 / 16 : ℝ) * ‖sqrt (2 / p (cepsJetCode (.inl 0))) *
      sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))))‖ ≤
    (sqrt (2 / p (cepsJetCode (.inl 0))) *
      sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))))).re := by
  have hvInv := cepsComplexVariance_inverse_cone hv hi
  exact complex_sqrt_product_re_lower_of_sector hvInv.1 hvInv.2 hz.sector

theorem cepsComplexCumulantRootBase_difference_sector_adm (p : ℕ → ℂ) {vlo vhi : ℝ}
    (hv : 0 < (p (cepsJetCode (.inl 0))).re)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) :
    (3 / 16 : ℝ) * ‖cepsComplexCumulantRootBase p lam z 1 -
      cepsComplexCumulantRootBase p lam z (-1)‖ ≤
    (cepsComplexCumulantRootBase p lam z 1 - cepsComplexCumulantRootBase p lam z (-1)).re := by
  let q := sqrt (2 / p (cepsJetCode (.inl 0))) *
    sqrt (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))))
  have he : cepsComplexCumulantRootBase p lam z 1 - cepsComplexCumulantRootBase p lam z (-1) = 2 * q := by
    dsimp [cepsComplexCumulantRootBase, q]
    ring
  have hq := cepsComplexQuadraticRootProduct_sector_adm p hv hi lam hz
  change (3 / 16 : ℝ) * ‖q‖ ≤ q.re at hq
  rw [he, norm_mul, norm_ofNat, mul_re]
  norm_num
  linarith

theorem cepsComplexCumulantRootBase_individual_sector_adm (p : ℕ → ℂ)
    {vlo vhi : ℝ} (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) :
    (lam ≤ 0 → cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖) ≤
      (cepsComplexCumulantRootBase p lam z 1).re) ∧
    (0 ≤ lam → (cepsComplexCumulantRootBase p lam z (-1)).re ≤
      -(cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖))) := by
  let v := p (cepsJetCode (.inl 0))
  let q := sqrt (2 / v) * sqrt (z + (lam : ℂ) ^ 2 / (2 * v))
  let F := |lam| + Real.sqrt ‖z‖
  let c := cepsFiniteQuadraticGapLower vlo vhi
  have hvr : 0 < v.re := hlo.trans_le hv
  have hv0 : v ≠ 0 := fun h => hvr.ne' (congrArg Complex.re h)
  have hVH : 0 < vhi := (hlo.trans_le (hv.trans (re_le_norm _))).trans_le hhi
  have hgap := cepsComplexCumulantRootGap_norm_lower_adm p hlo hv lam hz 1 (by norm_num)
  have he : cepsComplexCumulantRootGap p lam z 1 = v * q := by
    rw [cepsComplexCumulantRootGap_eq p lam z 1 hv0]
    dsimp [v, q]
    ring
  rw [he, norm_mul] at hgap
  have hqn : c * F ≤ vhi * ‖q‖ := hgap.trans (mul_le_mul_of_nonneg_right hhi (norm_nonneg _))
  have hq := cepsComplexQuadraticRootProduct_sector_adm p hvr hi lam hz
  change (3 / 16 : ℝ) * ‖q‖ ≤ q.re at hq
  have hphase : c / (8 * vhi) * F ≤ q.re := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : 0 < 8 * vhi)]
    nlinarith [norm_nonneg q]
  have hshift : (-(lam : ℂ) / v).re = -lam * v.re / normSq v := by simp [Complex.div_re]
  unfold cepsFiniteRootPhaseLower
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

theorem cepsComplexCumulantRootBase_separation_lower_adm (p : ℕ → ℂ)
    {vlo vhi : ℝ} (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) :
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
  have hgap := cepsComplexCumulantRootGap_norm_lower_adm p hlo hv lam hz 1 (by norm_num)
  rw [hg, norm_mul, norm_div, norm_ofNat] at hgap
  have hgphase := cepsComplexCumulantRootBase_difference_sector_adm p hV hi lam hz
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

/-- The upper base root grows at the separation rate up to the drift shift. -/
theorem cepsComplexCumulantRootBase_plus_re_lower_adm (p : ℕ → ℂ) {vlo vhi : ℝ}
    (hlo : 0 < vlo) (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) :
    cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖) - |lam| / vlo ≤
      (cepsComplexCumulantRootBase p lam z 1).re := by
  let v := p (cepsJetCode (.inl 0))
  let rp := cepsComplexCumulantRootBase p lam z 1
  let rm := cepsComplexCumulantRootBase p lam z (-1)
  have hgap := cepsComplexCumulantRootBase_separation_lower_adm p hlo hv hhi hi lam hz
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

theorem cepsComplexCumulantRootModel_weighted_error_adm {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z)
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
  have hδ := hb.trans (min_le_left _ _)
  have hs := cepsComplexCumulantRootModel_stability_adm N hM hlo hp hv lam hz hsign hδ k
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
      exact mul_le_mul hs.2 (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (norm_nonneg _)) (by positivity)
        (by positivity)
    _ = ((K + 2 * A) * (‖b‖ * F)) * F := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF

theorem cepsComplexCumulantRootModel_weighted_separation_adm {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (hhi : ‖p (cepsJetCode (.inl 0))‖ ≤ vhi)
    (hi : |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteWeightedRootRadius N M vlo vhi)
    (k : ℕ) :
    cepsFiniteRootPhaseLower vlo vhi * (|lam| + Real.sqrt ‖z‖) ≤
      ((cepsComplexCumulantRootModel p N lam z 1 k b -
        cepsComplexCumulantRootModel p N lam z (-1) k b) * (1 + b * lam)).re := by
  have hbase := cepsComplexCumulantRootBase_separation_lower_adm p hlo hv hhi hi lam hz
  have hplus := cepsComplexCumulantRootModel_weighted_error_adm N hM hlo hp hv lam hz
    (Or.inl rfl : (1 : ℂ) = 1 ∨ (1 : ℂ) = -1) hb k
  have hminus := cepsComplexCumulantRootModel_weighted_error_adm N hM hlo hp hv lam hz
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

/-- The Newton radius after which the weighted finite roots stay within `η F` of the
base roots. -/
def cepsFiniteRootSmallRadius (N : ℕ) (M vlo vhi η : ℝ) : ℝ :=
  min (cepsFiniteRootScaleRadius (cepsFiniteQuadraticRootBound vlo)
    (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M) M)
    (η / (cepsFiniteRootErrorConstant (cepsFiniteQuadraticRootBound vlo)
        (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M) +
        2 * cepsFiniteQuadraticRootBound vlo))

theorem cepsFiniteRootSmallRadius_pos (N : ℕ) {M vlo vhi η : ℝ}
    (hM : 0 ≤ M) (hlo : 0 < vlo) (hη : 0 < η) :
    0 < cepsFiniteRootSmallRadius N M vlo vhi η := by
  have hA := cepsFiniteQuadraticRootBound_pos hlo
  have hc := cepsFiniteQuadraticGapLower_pos (vhi := vhi) hlo
  have hK := cepsFiniteRootErrorConstant_pos hA hc (mul_nonneg (Nat.cast_nonneg N) hM)
  have hδ := (cepsFiniteRootScaleRadius_admissible hA hc
    (mul_nonneg (Nat.cast_nonneg N) hM) hM).1
  unfold cepsFiniteRootSmallRadius
  exact lt_min hδ (div_pos hη (by positivity))

/-- Weighted finite roots stay within an arbitrary multiple `η` of the base roots. -/
theorem cepsComplexCumulantRootModel_weighted_error_small {p : ℕ → ℂ} (N : ℕ)
    {M vlo vhi η : ℝ} (hM : 0 ≤ M) (hlo : 0 < vlo)
    (hp : ∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M)
    (hv : vlo ≤ (p (cepsJetCode (.inl 0))).re)
    (lam : ℝ) {z : ℂ} (hz : CepsRootAdmissible p vlo vhi lam z)
    {sign : ℂ} (hsign : sign = 1 ∨ sign = -1) {b : ℂ}
    (hb : ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ cepsFiniteRootSmallRadius N M vlo vhi η) (k : ℕ) :
    ‖cepsComplexCumulantRootModel p N lam z sign k b * (1 + b * lam) -
      cepsComplexCumulantRootBase p lam z sign‖ ≤ η * (|lam| + Real.sqrt ‖z‖) := by
  let A := cepsFiniteQuadraticRootBound vlo
  let K := cepsFiniteRootErrorConstant A (cepsFiniteQuadraticGapLower vlo vhi) ((N : ℝ) * M)
  let F := |lam| + Real.sqrt ‖z‖
  let g := cepsComplexCumulantRootModel p N lam z sign k b
  let r := cepsComplexCumulantRootBase p lam z sign
  have hA : 0 < A := cepsFiniteQuadraticRootBound_pos hlo
  have hK : 0 < K := cepsFiniteRootErrorConstant_pos hA
    (cepsFiniteQuadraticGapLower_pos hlo) (mul_nonneg (Nat.cast_nonneg N) hM)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hδ := hb.trans (min_le_left _ _)
  have hs := cepsComplexCumulantRootModel_stability_adm N hM hlo hp hv lam hz hsign hδ k
  change ‖g - r‖ ≤ K * ‖b‖ * F ^ 2 ∧ ‖g‖ ≤ 2 * A * F at hs
  have hsmall : (K + 2 * A) * (‖b‖ * F) ≤ η := by
    have hh := hb.trans (min_le_right _ _)
    change ‖b‖ * F ≤ η / (K + 2 * A) at hh
    have hd : 0 < K + 2 * A := by positivity
    have hh' := (le_div_iff₀ hd).mp hh
    linarith
  have he : g * (1 + b * lam) - r = (g - r) + g * (b * lam) := by ring
  change ‖g * (1 + b * lam) - r‖ ≤ η * F
  rw [he]
  calc
    _ ≤ ‖g - r‖ + ‖g * (b * lam)‖ := norm_add_le _ _
    _ ≤ K * ‖b‖ * F ^ 2 + (2 * A * F) * (‖b‖ * F) := by
      apply add_le_add hs.1
      rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs]
      exact mul_le_mul hs.2 (mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (norm_nonneg _)) (by positivity)
        (by positivity)
    _ = ((K + 2 * A) * (‖b‖ * F)) * F := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall hF

end PGM
