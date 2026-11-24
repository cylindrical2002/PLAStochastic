import PLAStochastic.Index.CEPS.Strip.RootAdmissible

/-! # The outer strip consists of admissible root frequencies

On `-δ ≤ Re z` and `F₀ ≤ |λ| + √‖z‖` with `δ` small against `F₀²`, the radicand stays
coercive (with the variance upper bound doubled) and in a half-norm sector, and the upper
base root loses at most a small multiple of `F` of real part compared with the
right half-plane. Small discs around strip points remain in a slightly larger strip.
-/

noncomputable section
open Complex Metric
namespace PGM

/-- Radicand coercivity with a strip defect. -/
theorem cepsComplexQuadraticRadicand_coercive_strip {v : ℂ} {vlo vhi δ : ℝ}
    (hlo : 0 < vlo) (hvre : vlo ≤ v.re) (hvhi : ‖v‖ ≤ vhi) (lam : ℝ) {z : ℂ}
    (hδ : 0 ≤ δ) (hz : -δ ≤ z.re) :
    lam ^ 2 + ‖z‖ ≤ cepsFiniteRadicandCoercivity vlo vhi *
      (‖z + (lam : ℂ) ^ 2 / (2 * v)‖ + δ) := by
  let a := (lam : ℂ) ^ 2 / (2 * v)
  let w := z + a
  have hnv : vlo ≤ ‖v‖ := hvre.trans (re_le_norm _)
  have hvpos : 0 < ‖v‖ := hlo.trans_le hnv
  have hv0 : v ≠ 0 := norm_pos_iff.mp hvpos
  have hhi : 0 < vhi := hvpos.trans_le hvhi
  have hinv : vlo / vhi ^ 2 ≤ v.re / ‖v‖ ^ 2 := by
    calc
      _ ≤ vlo / ‖v‖ ^ 2 := div_le_div_of_nonneg_left hlo.le (pow_pos hvpos 2)
        (pow_le_pow_left₀ (norm_nonneg _) hvhi 2)
      _ ≤ _ := div_le_div_of_nonneg_right hvre (by positivity)
  have hlower : (lam ^ 2 / 2) * (vlo / vhi ^ 2) ≤ ‖w‖ + δ := by
    calc
      _ ≤ (lam ^ 2 / 2) * (v.re / ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = a.re := (cepsComplexQuadraticRadicand_re v hv0 lam).symm
      _ ≤ w.re + δ := by dsimp only [w]; rw [add_re]; linarith
      _ ≤ _ := by linarith [re_le_norm w]
  have hlam : lam ^ 2 ≤ (2 * vhi ^ 2 / vlo) * (‖w‖ + δ) := by
    have hh : (lam ^ 2 * vlo / 2) / vhi ^ 2 ≤ ‖w‖ + δ := by
      convert hlower using 1; ring
    have hh' := (div_le_iff₀ (pow_pos hhi 2)).mp hh
    rw [div_mul_eq_mul_div, le_div_iff₀ hlo]
    nlinarith
  have hanorm : ‖a‖ ≤ lam ^ 2 / (2 * vlo) := by
    dsimp [a]
    rw [norm_div, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, norm_mul, norm_ofNat]
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
  have ha : ‖a‖ ≤ (vhi ^ 2 / vlo ^ 2) * (‖w‖ + δ) := by
    calc
      _ ≤ lam ^ 2 / (2 * vlo) := hanorm
      _ ≤ ((2 * vhi ^ 2 / vlo) * (‖w‖ + δ)) / (2 * vlo) :=
        div_le_div_of_nonneg_right hlam (by positivity)
      _ = _ := by field_simp
  have hzNorm : ‖z‖ ≤ (1 + vhi ^ 2 / vlo ^ 2) * (‖w‖ + δ) := by
    have ht := norm_sub_le w a
    rw [show w - a = z by dsimp [w]; ring] at ht
    have hw : ‖w‖ ≤ ‖w‖ + δ := le_add_of_nonneg_right hδ
    calc
      ‖z‖ ≤ ‖w‖ + ‖a‖ := ht
      _ ≤ (‖w‖ + δ) + (vhi ^ 2 / vlo ^ 2) * (‖w‖ + δ) := add_le_add hw ha
      _ = _ := by ring
  exact (add_le_add hlam hzNorm).trans_eq (by dsimp [cepsFiniteRadicandCoercivity, w, a]; ring)

/-- A real nonnegative shift moves the principal square root of a sector point by at most
`2 t / √‖w‖`. -/
theorem complex_sqrt_add_real_sub_le {w : ℂ} (hw : -‖w‖ ≤ 2 * w.re) (hw0 : w ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖sqrt (w + t) - sqrt w‖ ≤ 2 * t / Real.sqrt ‖w‖ := by
  have hs := complex_sqrt_re_ge_half_norm_of_sector hw
  rw [PGM.norm_sqrt] at hs
  have hs1 : 0 ≤ (sqrt (w + t)).re := by
    rw [Complex.sqrt, cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hpos : 0 < Real.sqrt ‖w‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hw0)
  have hsum : Real.sqrt ‖w‖ / 2 ≤ ‖sqrt (w + t) + sqrt w‖ := by
    have := re_le_norm (sqrt (w + t) + sqrt w)
    rw [add_re] at this
    linarith
  have hprod : (sqrt (w + t) - sqrt w) * (sqrt (w + t) + sqrt w) = t := by
    have h1 := sqrt_sq_eq (w + t)
    have h2 := sqrt_sq_eq w
    linear_combination h1 - h2
  have hn : ‖sqrt (w + t) - sqrt w‖ * ‖sqrt (w + t) + sqrt w‖ = t := by
    rw [← norm_mul, hprod, norm_real, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [le_div_iff₀ hpos]
  have hm := mul_le_mul_of_nonneg_left hsum (norm_nonneg (sqrt (w + t) - sqrt w))
  nlinarith [hm, hn]

theorem cepsFiniteRadicandCoercivity_pos {vlo vhi : ℝ} (hlo : 0 < vlo) :
    0 < cepsFiniteRadicandCoercivity vlo vhi := by
  unfold cepsFiniteRadicandCoercivity
  positivity

theorem cepsFiniteRadicandCoercivity_double {vlo vhi : ℝ} (hlo : 0 < vlo) (hhi : vlo ≤ vhi) :
    2 * cepsFiniteRadicandCoercivity vlo vhi ≤ cepsFiniteRadicandCoercivity vlo (2 * vhi) := by
  unfold cepsFiniteRadicandCoercivity
  have h1 : 1 ≤ vhi ^ 2 / vlo ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h2 : 0 ≤ vhi ^ 2 / vlo := by positivity
  have he : (2 * vhi) ^ 2 / vlo ^ 2 = 4 * (vhi ^ 2 / vlo ^ 2) := by ring
  have he' : 2 * (2 * vhi) ^ 2 / vlo = 4 * (2 * vhi ^ 2 / vlo) := by ring
  rw [he, he']
  have h3 : 0 ≤ 2 * vhi ^ 2 / vlo := by positivity
  linarith

theorem cepsFiniteRootPhaseLower_pos {vlo vhi : ℝ} (hlo : 0 < vlo) (hhi : 0 < vhi) :
    0 < cepsFiniteRootPhaseLower vlo vhi := by
  have := cepsFiniteQuadraticGapLower_pos (vhi := vhi) hlo
  unfold cepsFiniteRootPhaseLower
  positivity

/-- The outer strip is admissible after doubling the variance upper bound. The width is
chosen before the finite vector, the drift and the frequency. -/
theorem cepsRootAdmissible_of_strip {vlo vhi F₀ : ℝ} (hlo : 0 < vlo) (hhi : vlo ≤ vhi)
    (hF₀ : 0 < F₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p : ℕ → ℂ, vlo ≤ (p (cepsJetCode (.inl 0))).re →
      ‖p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
        CepsRootAdmissible p vlo (2 * vhi) lam z := by
  let C := cepsFiniteRadicandCoercivity vlo vhi
  let D := cepsFiniteRootPhaseLower vlo (2 * vhi)
  let κ := Real.sqrt (2 / vlo)
  let sC := Real.sqrt C
  have hvhi : 0 < vhi := hlo.trans_le hhi
  have hC : 0 < C := cepsFiniteRadicandCoercivity_pos hlo
  have hD : 0 < D := cepsFiniteRootPhaseLower_pos hlo (by positivity)
  have hκ : 0 < κ := Real.sqrt_pos.mpr (by positivity)
  have hsC : 0 < sC := Real.sqrt_pos.mpr hC
  let δ := min (F₀ ^ 2 / (8 * C)) (D * F₀ ^ 2 / (16 * κ * sC))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ F₀ ^ 2 / (8 * C) := min_le_left _ _
  have hδ2 : δ ≤ D * F₀ ^ 2 / (16 * κ * sC) := min_le_right _ _
  -- the radicand facts for every drift
  have hrad : ∀ p : ℕ → ℂ, vlo ≤ (p (cepsJetCode (.inl 0))).re →
      ‖p (cepsJetCode (.inl 0))‖ ≤ vhi →
      ∀ (lam : ℝ) (z : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ →
        lam ^ 2 + ‖z‖ ≤ 2 * C * ‖z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))‖ ∧
        F₀ ^ 2 / 2 ≤ lam ^ 2 + ‖z‖ ∧
        -‖z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))‖ ≤
          2 * (z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0)))).re := by
    intro p hv hvh lam z hz hF
    set w := z + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))) with hw
    have hco := cepsComplexQuadraticRadicand_coercive_strip hlo hv hvh lam hδ.le hz
    have hF2 : (|lam| + Real.sqrt ‖z‖) ^ 2 ≤ 2 * (lam ^ 2 + ‖z‖) := by
      nlinarith [Real.sq_sqrt (norm_nonneg z), sq_abs lam,
        sq_nonneg (|lam| - Real.sqrt ‖z‖)]
    have hF02 : F₀ ^ 2 ≤ (|lam| + Real.sqrt ‖z‖) ^ 2 := pow_le_pow_left₀ hF₀.le hF 2
    have hS : F₀ ^ 2 / 2 ≤ lam ^ 2 + ‖z‖ := by linarith
    have hCδ : C * δ ≤ F₀ ^ 2 / 8 := by
      have := mul_le_mul_of_nonneg_left hδ1 hC.le
      calc
        C * δ ≤ C * (F₀ ^ 2 / (8 * C)) := this
        _ = F₀ ^ 2 / 8 := by field_simp
    have hco' : lam ^ 2 + ‖z‖ ≤ 2 * C * ‖w‖ := by
      have : lam ^ 2 + ‖z‖ ≤ C * ‖w‖ + C * δ := by
        have h := hco
        change lam ^ 2 + ‖z‖ ≤ C * (‖w‖ + δ) at h
        linarith [mul_add C ‖w‖ δ]
      nlinarith
    refine ⟨hco', hS, ?_⟩
    have hwlow : F₀ ^ 2 / (4 * C) ≤ ‖w‖ := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hwre : -δ ≤ w.re := by
      rw [hw, add_re, cepsComplexQuadraticRadicand_re _
        (norm_pos_iff.mp (hlo.trans_le (hv.trans (re_le_norm _)))) lam]
      have : 0 ≤ (lam ^ 2 / 2) * ((p (cepsJetCode (.inl 0))).re /
          ‖p (cepsJetCode (.inl 0))‖ ^ 2) :=
        mul_nonneg (by positivity) (div_nonneg (hlo.le.trans hv) (by positivity))
      linarith
    have hδw : 2 * δ ≤ ‖w‖ := by
      have : 2 * δ ≤ F₀ ^ 2 / (4 * C) := by
        calc
          2 * δ ≤ 2 * (F₀ ^ 2 / (8 * C)) := by linarith
          _ = F₀ ^ 2 / (4 * C) := by field_simp; ring
      linarith
    linarith
  -- the upper root on the nonnegative drift side
  have hplus : ∀ p : ℕ → ℂ, vlo ≤ (p (cepsJetCode (.inl 0))).re →
      ‖p (cepsJetCode (.inl 0))‖ ≤ vhi →
      |(p (cepsJetCode (.inl 0))).im| ≤ (p (cepsJetCode (.inl 0))).re / 8 →
      ∀ (lam : ℝ) (z : ℂ), -δ ≤ z.re → F₀ ≤ |lam| + Real.sqrt ‖z‖ → 0 ≤ lam →
        -(D / 4 * (|lam| + Real.sqrt ‖z‖)) ≤ (cepsComplexCumulantRootBase p lam z 1).re := by
    intro p hv hvh hi lam z hz hF hl
    let v := p (cepsJetCode (.inl 0))
    set w := z + (lam : ℂ) ^ 2 / (2 * v) with hw
    let F := |lam| + Real.sqrt ‖z‖
    obtain ⟨hco, hS, hsec⟩ := hrad p hv hvh lam z hz hF
    have hvr : 0 < v.re := hlo.trans_le hv
    have hv0 : v ≠ 0 := fun h => hvr.ne' (congrArg Complex.re h)
    have hF0 : 0 < F := hF₀.trans_le hF
    have hw0 : w ≠ 0 := by
      intro h0
      have : lam ^ 2 + ‖z‖ ≤ 0 := by
        have := hco
        rw [← hw, h0, norm_zero, mul_zero] at this
        exact this
      have : F₀ ^ 2 / 2 ≤ 0 := hS.trans this
      have : 0 < F₀ ^ 2 / 2 := by positivity
      linarith
    let z₁ : ℂ := z + (δ : ℂ)
    have hz₁ : 0 ≤ z₁.re := by
      simp only [z₁, add_re, ofReal_re]
      linarith
    have hr₁ := cepsComplexCumulantRootBase_plus_re_nonneg p hvr hi hl hz₁
    have hw₁ : z₁ + (lam : ℂ) ^ 2 / (2 * v) = w + (δ : ℂ) := by
      simp only [z₁, hw]
      ring
    have hdiff : cepsComplexCumulantRootBase p lam z₁ 1 - cepsComplexCumulantRootBase p lam z 1 =
        sqrt (2 / v) * (sqrt (w + (δ : ℂ)) - sqrt w) := by
      unfold cepsComplexCumulantRootBase
      simp only
      rw [show z₁ + (lam : ℂ) ^ 2 / (2 * p (cepsJetCode (.inl 0))) = w + (δ : ℂ) from hw₁]
      ring
    have hsq := complex_sqrt_add_real_sub_le hsec hw0 hδ.le
    have hκv : ‖sqrt (2 / v)‖ ≤ κ := by
      rw [PGM.norm_sqrt, norm_div, norm_ofNat]
      exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by norm_num) hlo
        (hv.trans (re_le_norm _)))
    have hsw : F / (2 * sC) ≤ Real.sqrt ‖w‖ := by
      have hF2 : F ^ 2 ≤ 2 * (lam ^ 2 + ‖z‖) := by
        dsimp [F]
        nlinarith [Real.sq_sqrt (norm_nonneg z), sq_abs lam,
          sq_nonneg (|lam| - Real.sqrt ‖z‖)]
      have h1 : (F / (2 * sC)) ^ 2 ≤ ‖w‖ := by
        rw [div_pow, mul_pow, Real.sq_sqrt hC.le, div_le_iff₀ (by positivity)]
        nlinarith
      calc
        F / (2 * sC) = Real.sqrt ((F / (2 * sC)) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
        _ ≤ _ := Real.sqrt_le_sqrt h1
    have hswpos : 0 < Real.sqrt ‖w‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hw0)
    have hbound : ‖cepsComplexCumulantRootBase p lam z₁ 1 -
        cepsComplexCumulantRootBase p lam z 1‖ ≤ D / 4 * F := by
      rw [hdiff, norm_mul]
      have hstep : ‖sqrt (w + (δ : ℂ)) - sqrt w‖ ≤ 4 * δ * sC / F := by
        apply hsq.trans
        rw [div_le_div_iff₀ hswpos hF0]
        have := mul_le_mul_of_nonneg_left hsw (by positivity : 0 ≤ 2 * δ)
        have he : 2 * δ * (F / (2 * sC)) = δ * F / sC := by field_simp
        rw [he, div_le_iff₀ hsC] at this
        nlinarith
      calc
        _ ≤ κ * (4 * δ * sC / F) := mul_le_mul hκv hstep (norm_nonneg _) hκ.le
        _ ≤ D / 4 * F := by
          rw [mul_div_assoc', div_le_iff₀ hF0]
          have hFF : F₀ ^ 2 ≤ F ^ 2 := pow_le_pow_left₀ hF₀.le hF 2
          have h16 : 16 * κ * sC * δ ≤ D * F₀ ^ 2 := by
            have := (le_div_iff₀ (by positivity : 0 < 16 * κ * sC)).mp hδ2
            linarith
          nlinarith
    have hre := re_le_norm (cepsComplexCumulantRootBase p lam z₁ 1 -
      cepsComplexCumulantRootBase p lam z 1)
    rw [sub_re] at hre
    change -(D / 4 * F) ≤ _
    linarith
  refine ⟨δ, hδ, ?_⟩
  intro p hv hvh hi lam z hz hF
  obtain ⟨hco, hS, hsec⟩ := hrad p hv hvh lam z hz hF
  refine ⟨hF₀.trans_le hF, ?_, hsec, hplus p hv hvh hi lam z hz hF, ?_⟩
  · exact hco.trans (mul_le_mul_of_nonneg_right
      (cepsFiniteRadicandCoercivity_double hlo hhi) (norm_nonneg _))
  · intro hl
    have hneg := hplus p hv hvh hi (-lam) z hz (by simpa only [abs_neg] using hF) (by linarith)
    rw [cepsComplexCumulantRootBase_reflect, neg_re]
    simp only [abs_neg] at hneg
    linarith

end PGM
