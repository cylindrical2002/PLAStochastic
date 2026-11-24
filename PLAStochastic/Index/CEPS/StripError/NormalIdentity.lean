import PLAStochastic.Index.CEPS.StripError.ExitTop

/-!
# WP9: the normal entrance as the normal exit telescope

At every non-degenerate point (`r₊ ≠ 0`, `d(t) ≠ 0`), the regular normal entrance satisfies the
normal analogue of the strip telescope, `d(t) Ĥ_t = 1 - û_t - ℓ̂_t`
(`strip_normal_identity`; X5 `entrance_eq_passage` and `entrance_eq_regular`).

The right side `stripNormalGap` is an explicit holomorphic function of the mark on the root disc
`‖t‖ < c₀/2` (`stripNormalGap_differentiableOn`) and is bounded by a class constant on
`‖t‖ ≤ c₀/4`, `Re t ≥ -1/l` (`norm_stripNormalGap_le`), uniformly up to merging roots. This is the
normal half of the mark-direction Cauchy budget of S-3 (a).
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric
open WienerHopf

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem strip_normal_identity_WH {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hr : cepsRootR D θ ρ μ q ≠ 0) {l : ℝ}
    (hl : dom.normalWidthThreshold ≤ l) {t : ℂ} (ht : ‖t‖ ≤ dom.c₀ / 4)
    (hd : cepsD ρ μ q t ≠ 0) :
    cepsD ρ μ q t * (cepsWHNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l t =
      1 - (cepsWHNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q t l -
        (cepsWHNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q t l := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  set a := cepsWHNormalData D θ ρ μ q with ha
  set L := dom.canonL ρ with hL
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hQne : ∀ z : ℂ, ‖z‖ ≤ dom.c₀ / 4 → a.Q z ≠ 0 := fun z hz =>
    CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμc hq (mem_ball_zero_iff.mpr (by linarith))
  have hQp : a.Q a.βp ≠ 0 := hQne _ (dom.norm_rootPlus_le hW hθ hD hμc hq)
  have hQm : a.Q a.βm ≠ 0 := hQne _ (dom.norm_rootMinus_le hW hθ hD hμc hq)
  have hQt : a.Q t ≠ 0 := hQne _ ht
  have hfac : a.d t = a.Q t * (a.βp - t) * (t - a.βm) := by
    show cepsD ρ μ q t = cepsQ D θ ρ μ q t * (cepsRootPlus D θ ρ μ q - t) *
      (t - cepsRootMinus D θ ρ μ q)
    rw [CepsC6.cepsD_eq_mul_cepsQ dom hW hθ hD hμc hq t]
    ring
  have hpt : a.βp - t ≠ 0 := by
    intro h0
    apply hd
    show a.d t = 0
    rw [hfac, h0]
    ring
  have htm : t - a.βm ≠ 0 := by
    intro h0
    apply hd
    show a.d t = 0
    rw [hfac, h0]
    ring
  have hη : a.eta ≠ 0 := by
    have hre := cepsRoots_difference_re_ge hW hθ hD dom hμ hq hq0
    have hv := Real.sqrt_pos.mpr (CepsCanonDomain.v_pos hW hθ hD)
    have hrp : 0 < ‖cepsRootR D θ ρ μ q‖ := norm_pos_iff.mpr hr
    intro h0
    have : (cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q).re = 0 := by
      have h0' : cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q = 0 := h0
      rw [h0', zero_re]
    have : 0 < ‖cepsRootR D θ ρ μ q‖ / (2 * Real.sqrt v) := by positivity
    linarith
  have hΔ : a.delta L μ q l ≠ 0 := by
    intro h0
    have h := strip_eta_le_delta dom hW hθ hD hμ hq hq0 hl
    rw [show (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l = 0 from h0, norm_zero,
      mul_zero] at h
    exact hη (norm_le_zero_iff.mp h)
  have hS := cepsNormal_actual_dslope_ne_zero dom hW hθ hD hμ hq hq0 hl
  have hreg := CepsNormalData.entrance_eq_regular a L μ q l t hQm hQt hη hpt htm hS hfac
  have hpas := CepsNormalData.entrance_eq_passage a L μ q t l hQp hQm hQt hd hΔ
  show a.d t * a.regularEntrance L μ q l t = _
  have hd' : a.d t ≠ 0 := hd
  rw [← hreg, hpas, mul_div_assoc', mul_div_cancel_left₀ _ hd']

include hW hθ hD in
/-- **The normal telescope** for the original root-zone data. -/
theorem strip_normal_identity {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) (hr : cepsRootR D θ ρ μ q ≠ 0) {l : ℝ}
    (hl : dom.normalWidthThreshold ≤ l) {t : ℂ} (ht : ‖t‖ ≤ dom.c₀ / 4)
    (hd : cepsD ρ μ q t ≠ 0) :
    cepsD ρ μ q t * (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l t =
      1 - (cepsNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q t l -
        (cepsNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q t l := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hball : ∀ ζ : ℂ, ‖ζ‖ ≤ dom.c₀ / 4 →
      cepsQ D θ ρ μ q ζ = cepsQuotA D θ ρ μ q ζ := fun ζ hζ =>
    CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμc hq (mem_ball_zero_iff.mpr (by linarith))
  obtain ⟨hu, hlo⟩ := CepsNormalData.normal_exits_congr (cepsWHNormalData D θ ρ μ q)
    (cepsNormalData D θ ρ μ q) (dom.canonL ρ) μ q t l rfl rfl (hball t ht)
    (hball _ (dom.norm_rootPlus_le hW hθ hD hμc hq))
    (hball _ (dom.norm_rootMinus_le hW hθ hD hμc hq))
  have hreg := (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμc hq (dom.canonL ρ) l
    (t := t) (mem_ball_zero_iff.mpr (by linarith))).1
  rw [← hu, ← hlo, ← hreg]
  exact strip_normal_identity_WH dom hW hθ hD hμ hq0 hq hr hl ht hd

/-! ## The normal exit telescope as a function of the mark -/

/-- `1 - û_t - ℓ̂_t` for the root-zone data. -/
def stripNormalGap (ρ : Measure ℝ) (μ : ℝ) (q : ℂ) (l : ℝ) (t : ℂ) : ℂ :=
  1 - (cepsWHNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q t l -
    (cepsWHNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q t l

theorem stripNormalGap_eq (ρ : Measure ℝ) (μ : ℝ) (q : ℂ) (l : ℝ) (t : ℂ) :
    stripNormalGap dom ρ μ q l t =
      (cepsRootPlus D θ ρ μ q - t) * cexp (dom.canonL ρ μ q t) +
        cexp (dom.canonL ρ μ q t - dom.canonL ρ μ q (cepsRootPlus D θ ρ μ q)) *
          (cepsWHNormalData D θ ρ μ q).passageY (dom.canonL ρ) μ q l -
        cexp ((cepsRootMinus D θ ρ μ q - t) * (l : ℂ)) *
          cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q (cepsRootMinus D θ ρ μ q)) *
          (cepsWHNormalData D θ ρ μ q).passageX (dom.canonL ρ) μ q l := by
  unfold stripNormalGap CepsNormalData.upperExit CepsNormalData.lowerExit
    CepsNormalData.overshootPlus CepsNormalData.overshootMinus
  simp only [sub_sub_cancel, add_sub_cancel, cepsWHNormalData, CepsNormalData.factorMinus,
    CepsCanonDomain.canonLMinus]
  ring

/-- The class constant of the normal telescope on the mark disc. -/
def CepsCanonDomain.stripGapConst : ℝ :=
  dom.c₀ / 2 * Real.exp dom.normalLogBound +
    (dom.stripBplus * dom.stripBminus + Real.exp 1 * dom.stripBminus) *
      (dom.stripEtaDelta * Real.exp dom.normalLogBound)

include hW hθ hD in
theorem norm_passageX_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    ‖(cepsWHNormalData D θ ρ μ q).passageX (dom.canonL ρ) μ q l‖ ≤
      dom.stripEtaDelta * Real.exp dom.normalLogBound := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hη := strip_eta_le_delta dom hW hθ hD hμ hq hq0 hl
  have hL := norm_canonL_le_logBound dom hW hθ hD hμ hq (z := cepsRootMinus D θ ρ μ q)
    (by have := dom.norm_rootMinus_le hW hθ hD hμc hq; linarith)
  have hE : ‖cexp (dom.canonL ρ μ q (cepsRootMinus D θ ρ μ q))‖ ≤ Real.exp dom.normalLogBound :=
    (norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr hL)
  have hηΔ : 0 ≤ dom.stripEtaDelta := by
    unfold CepsCanonDomain.stripEtaDelta
    have := cepsChartK_pos hD; have := cepsNormal_sectorConst_pos dom hW hθ hD; positivity
  unfold CepsNormalData.passageX CepsNormalData.eta
  set Δ := (cepsWHNormalData D θ ρ μ q).delta (dom.canonL ρ) μ q l
  by_cases hΔ : Δ = 0
  · rw [hΔ, div_zero, norm_zero]
    exact mul_nonneg hηΔ (Real.exp_pos _).le
  · have hΔp : 0 < ‖Δ‖ := norm_pos_iff.mpr hΔ
    rw [norm_div, norm_mul, div_le_iff₀ hΔp]
    calc _ ≤ dom.stripEtaDelta * ‖Δ‖ * Real.exp dom.normalLogBound :=
          mul_le_mul hη hE (norm_nonneg _) (mul_nonneg hηΔ (norm_nonneg _))
      _ = _ := by ring

include hW hθ hD in
/-- The normal telescope is bounded by a class constant on the mark disc. -/
theorem norm_stripNormalGap_le {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 ≤ q.re)
    (hq : ‖q‖ ≤ dom.q₀) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) {t : ℂ}
    (ht : ‖t‖ ≤ dom.c₀ / 4) (htre : -(1 / l) ≤ t.re) :
    ‖stripNormalGap dom ρ μ q l t‖ ≤ dom.stripGapConst := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hl
  have hbp := dom.norm_rootPlus_le hW hθ hD hμc hq
  have hbm := dom.norm_rootMinus_le hW hθ hD hμc hq
  have hbp2 : ‖cepsRootPlus D θ ρ μ q‖ ≤ dom.c₀ / 2 := by linarith
  have hbm2 : ‖cepsRootMinus D θ ρ μ q‖ ≤ dom.c₀ / 2 := by linarith
  have ht2 : ‖t‖ ≤ dom.c₀ / 2 := by linarith
  have hsm := (cepsRoots_re_signs dom hW hθ hD hμ hq0 hq).2
  have hX := norm_passageX_le dom hW hθ hD hμ hq0 hq hl
  have hXn : 0 ≤ dom.stripEtaDelta * Real.exp dom.normalLogBound := le_trans (norm_nonneg _) hX
  have hBp0 : 0 ≤ dom.stripBplus := (Real.exp_pos _).le
  have hBm := norm_cexp_canonLMinus_sub_le dom hW hθ hD hμ hq (z := t)
    (w := cepsRootMinus D θ ρ μ q) ht2 hbm2
  have hBm0 : 0 ≤ dom.stripBminus := le_trans (norm_nonneg _) hBm
  have hY : ‖(cepsWHNormalData D θ ρ μ q).passageY (dom.canonL ρ) μ q l‖ ≤
      dom.stripBminus * (dom.stripEtaDelta * Real.exp dom.normalLogBound) := by
    unfold CepsNormalData.passageY
    rw [norm_mul, norm_mul]
    have hE : ‖(cepsWHNormalData D θ ρ μ q).decay l‖ ≤ 1 := by
      unfold CepsNormalData.decay CepsNormalData.eta
      have hre := cepsRoots_difference_re_ge hW hθ hD dom hμ hq hq0
      have : 0 ≤ (cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q).re :=
        le_trans (by positivity) hre
      refine norm_cexp_mul_ofReal_le_one_of_re_nonpos ?_ hl0.le
      show (-(cepsRootPlus D θ ρ μ q - cepsRootMinus D θ ρ μ q)).re ≤ 0
      rw [neg_re]
      linarith
    have hBmη : ‖(cepsWHNormalData D θ ρ μ q).overshootMinus (dom.canonL ρ) μ q
        (cepsWHNormalData D θ ρ μ q).eta‖ ≤ dom.stripBminus := by
      unfold CepsNormalData.overshootMinus CepsNormalData.eta
      simp only [add_sub_cancel]
      exact norm_cexp_canonLMinus_sub_le dom hW hθ hD hμ hq hbp2 hbm2
    calc _ ≤ 1 * dom.stripBminus * (dom.stripEtaDelta * Real.exp dom.normalLogBound) :=
          mul_le_mul (mul_le_mul hE hBmη (norm_nonneg _) zero_le_one) hX (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hLt := norm_canonL_le_logBound dom hW hθ hD hμ hq ht2
  have hA : ‖(cepsRootPlus D θ ρ μ q - t) * cexp (dom.canonL ρ μ q t)‖ ≤
      dom.c₀ / 2 * Real.exp dom.normalLogBound := by
    rw [norm_mul]
    refine mul_le_mul ?_ ((norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr hLt))
      (norm_nonneg _) (by positivity)
    calc _ ≤ ‖cepsRootPlus D θ ρ μ q‖ + ‖t‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hB : ‖cexp (dom.canonL ρ μ q t - dom.canonL ρ μ q (cepsRootPlus D θ ρ μ q)) *
      (cepsWHNormalData D θ ρ μ q).passageY (dom.canonL ρ) μ q l‖ ≤
      dom.stripBplus * (dom.stripBminus * (dom.stripEtaDelta * Real.exp dom.normalLogBound)) := by
    rw [norm_mul]
    exact mul_le_mul (norm_cexp_canonL_sub_le dom hW hθ hD hμ hq ht2 hbp2) hY (norm_nonneg _) hBp0
  have hexp : ‖cexp ((cepsRootMinus D θ ρ μ q - t) * (l : ℂ))‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    simp only [mul_re, sub_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    have h1 : -t.re * l ≤ 1 := by
      have := mul_le_mul_of_nonneg_right htre hl0.le
      rw [show -(1 / l) * l = -1 by field_simp] at this
      linarith
    nlinarith
  have hC : ‖cexp ((cepsRootMinus D θ ρ μ q - t) * (l : ℂ)) *
      cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q (cepsRootMinus D θ ρ μ q)) *
      (cepsWHNormalData D θ ρ μ q).passageX (dom.canonL ρ) μ q l‖ ≤
      Real.exp 1 * dom.stripBminus * (dom.stripEtaDelta * Real.exp dom.normalLogBound) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul hexp hBm (norm_nonneg _) (Real.exp_pos _).le) hX
      (norm_nonneg _) (by positivity)
  rw [stripNormalGap_eq]
  calc _ ≤ ‖(cepsRootPlus D θ ρ μ q - t) * cexp (dom.canonL ρ μ q t) +
        cexp (dom.canonL ρ μ q t - dom.canonL ρ μ q (cepsRootPlus D θ ρ μ q)) *
          (cepsWHNormalData D θ ρ μ q).passageY (dom.canonL ρ) μ q l‖ +
        ‖cexp ((cepsRootMinus D θ ρ μ q - t) * (l : ℂ)) *
          cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q (cepsRootMinus D θ ρ μ q)) *
          (cepsWHNormalData D θ ρ μ q).passageX (dom.canonL ρ) μ q l‖ := norm_sub_le _ _
    _ ≤ (dom.c₀ / 2 * Real.exp dom.normalLogBound +
          dom.stripBplus * (dom.stripBminus * (dom.stripEtaDelta * Real.exp dom.normalLogBound))) +
        Real.exp 1 * dom.stripBminus * (dom.stripEtaDelta * Real.exp dom.normalLogBound) :=
      add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC
    _ = dom.stripGapConst := by unfold CepsCanonDomain.stripGapConst; ring

include hW hθ hD in
/-- The normal telescope is holomorphic in the mark on the root disc. -/
theorem stripNormalGap_differentiableOn {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq : ‖q‖ ≤ dom.q₀) (l : ℝ) :
    DifferentiableOn ℂ (stripNormalGap dom ρ μ q l) (ball 0 (dom.c₀ / 2)) := by
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 2 < dom.ρA := c₀_half_lt_ρA dom
  set L := dom.canonL ρ μ q with hLdef
  set βp := cepsRootPlus D θ ρ μ q
  set βm := cepsRootMinus D θ ρ μ q
  set Y := (cepsWHNormalData D θ ρ μ q).passageY (dom.canonL ρ) μ q l
  set X := (cepsWHNormalData D θ ρ μ q).passageX (dom.canonL ρ) μ q l
  have hQm : cepsQ D θ ρ μ q βm ≠ 0 := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμc hq
    (mem_ball_zero_iff.mpr (by have := dom.norm_rootMinus_le hW hθ hD hμc hq; linarith))
  -- a log-free form on the root disc
  set G : ℂ → ℂ := fun t => (βp - t) * cexp (L t) + cexp (L t - L βp) * Y -
    cexp ((βm - t) * (l : ℂ)) * (cepsQ D θ ρ μ q t / cepsQ D θ ρ μ q βm *
      cexp (L βm - L t)) * X with hGdef
  have heq : EqOn (stripNormalGap dom ρ μ q l) G (ball 0 (dom.c₀ / 2)) := by
    intro t ht
    have htA : t ∈ ball (0 : ℂ) dom.ρA := ball_subset_ball hρA.le ht
    have hQt := CepsC6.cepsQ_ne_zero_of_mem_ball dom hW hθ hD hμc hq htA
    rw [stripNormalGap_eq]
    have hm : cexp (dom.canonLMinus ρ μ q t - dom.canonLMinus ρ μ q βm) =
        cepsQ D θ ρ μ q t / cepsQ D θ ρ μ q βm * cexp (L βm - L t) := by
      rw [Complex.exp_sub, CepsC6.cexp_canonLMinus_eq dom hQt, CepsC6.cexp_canonLMinus_eq dom hQm,
        Complex.exp_sub, Complex.exp_neg, Complex.exp_neg]
      field_simp
      simp only [hLdef]
      ring
    rw [hm]
  refine DifferentiableOn.congr ?_ heq
  intro t ht
  have hre : t.re < dom.c₀ := by
    have := re_le_norm t; have := mem_ball_zero_iff.mp ht; linarith
  have htA : t ∈ ball (0 : ℂ) dom.ρA := ball_subset_ball hρA.le ht
  have hLd : DifferentiableAt ℂ L t := CepsC6.differentiableAt_canonL dom hW hθ hD hμ hq hre
  have hQd : DifferentiableAt ℂ (cepsQ D θ ρ μ q) t := CepsC6.differentiableAt_cepsQ dom hW hθ hD
    hμc hq htA
  refine DifferentiableAt.differentiableWithinAt ?_
  simp only [hGdef]
  fun_prop

end

end PGM
