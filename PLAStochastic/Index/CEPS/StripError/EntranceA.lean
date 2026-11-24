import PLAStochastic.Index.CEPS.StripError.EntranceB
import PLAStochastic.ForMathlib.Analysis.Calculus.DerivativeTransfer

/-!
# WP9, S-3 (a): the marked entrance error on the marked curve

On the curve `q = -β t` (for the outer walk of theorem (E) this is `q = t(1+μ)`) the
denominator is `d(t) = 1 - e^{σt} M₀(t)` with `σ = β + μ = ±1`, so `|d(t)| ≥ |t|/2` for small
imaginary marks (`norm_curve_denominator_ge`). With `F(s) = d(s; q) H_s(q) - (1 - û_s - ℓ̂_s)` at
the fixed discount `q`, the path `(0,0) → (0,q) → (t,q)` gives
`|F(t)| ≤ |F(t) - F(0)| + |F̃(q)|`: the first term by the interpolation engine along the imaginary
mark axis (actual and normal Cauchy budgets of `MarkHolo`, `NormalIdentity`), the second by the
unmarked estimate of `EntranceB` (`‖F̃(q)‖ ≤ ε₂‖q‖`). Dividing by `|d(t)| ≥ |t|/2` gives the
marked entrance error uniformly in `t → 0` (`strip_entrance_error_marked`).
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open WienerHopf

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}

/-- `|1 - e^{σt} M₀(t)| ≥ |t|/2` for small imaginary `t` and `σ = ±1`. -/
theorem norm_curve_denominator_ge (hW : IsStepLaw ρ fρ D θ v) {σ : ℝ} (hσ : |σ| = 1)
    {t : ℂ} (ht : t.re = 0) (htn : ‖t‖ ≤ 1 / (2 * (v + 1))) :
    ‖t‖ / 2 ≤ ‖1 - cexp (σ * t) * stepTransform ρ t‖ := by
  have := hW.isProbabilityMeasure
  have hv0 : 0 ≤ v := le_trans (integral_nonneg fun x => sq_nonneg x) hW.integral_sq_le
  set y := t.im with hy
  have hty : t = Complex.I * (y : ℂ) := by
    apply Complex.ext <;> simp [ht, hy]
  have hX : Integrable (fun w : ℝ => w + σ) ρ := hW.integrable_id.add (integrable_const σ)
  have hX2 : Integrable (fun w : ℝ => (w + σ) ^ 2) ρ := by
    have : (fun w : ℝ => (w + σ) ^ 2) = fun w => w ^ 2 + (2 * σ) * w + σ ^ 2 := by
      funext w; ring
    rw [this]
    exact (hW.integrable_sq.add (hW.integrable_id.const_mul _)).add (integrable_const _)
  have hm1 : ∫ w, (w + σ) ∂ρ = σ := by
    rw [integral_add hW.integrable_id (integrable_const σ), hW.integral_id]
    simp
  have hm2 : ∫ w, (w + σ) ^ 2 ∂ρ ≤ v + 1 := by
    have e : ∀ w : ℝ, (w + σ) ^ 2 = (w ^ 2 + 2 * σ * w) + σ ^ 2 := fun w => by ring
    simp_rw [e]
    have hi1 : Integrable (fun w : ℝ => w ^ 2 + 2 * σ * w) ρ :=
      hW.integrable_sq.add (hW.integrable_id.const_mul (2 * σ))
    have hi2 : Integrable (fun w : ℝ => 2 * σ * w) ρ := hW.integrable_id.const_mul (2 * σ)
    rw [integral_add hi1 (integrable_const _), integral_add hW.integrable_sq hi2,
      integral_const_mul, hW.integral_id]
    have hσ2 : σ ^ 2 = 1 := by rw [← sq_abs, hσ]; norm_num
    simp only [mul_zero, add_zero, integral_const, probReal_univ, smul_eq_mul, one_mul, hσ2]
    linarith [hW.integral_sq_le]
  have h := norm_integral_cexp_sub_le (P := ρ) hX hX2 (-y)
  rw [hm1] at h
  have hΦ : (∫ w, cexp (-(Complex.I * ((-y : ℝ) : ℂ)) * ((w + σ : ℝ) : ℂ)) ∂ρ) =
      cexp (σ * t) * stepTransform ρ t := by
    unfold stepTransform
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only
    rw [← Complex.exp_add, hty]
    congr 1
    push_cast
    ring
  rw [hΦ] at h
  have hnt : ‖t‖ = |y| := by
    rw [hty, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hIy : ‖Complex.I * ((-y : ℝ) : ℂ)‖ = |y| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  rw [hIy] at h
  -- `1 - Φ = -(Φ - 1 - I(-y)(-σ)) + I(-y)(-σ)`, and `‖I(-y)(-σ)‖ = |y|`
  have hlin : ‖Complex.I * ((-y : ℝ) : ℂ) * (-((σ : ℝ) : ℂ))‖ = |y| := by
    rw [norm_mul, hIy, norm_neg, Complex.norm_real, Real.norm_eq_abs, hσ, mul_one]
  have hkey := norm_sub_norm_le (-(Complex.I * ((-y : ℝ) : ℂ) * (-((σ : ℝ) : ℂ))))
    (cexp (σ * t) * stepTransform ρ t - 1 - Complex.I * ((-y : ℝ) : ℂ) * (-((σ : ℝ) : ℂ)))
  rw [norm_neg, hlin, show -(Complex.I * ((-y : ℝ) : ℂ) * (-((σ : ℝ) : ℂ))) -
      (cexp (σ * t) * stepTransform ρ t - 1 - Complex.I * ((-y : ℝ) : ℂ) * (-((σ : ℝ) : ℂ))) =
      1 - cexp (σ * t) * stepTransform ρ t by ring] at hkey
  have hy1 : |y| * (v + 1) ≤ 1 / 2 := by
    rw [← hnt]
    have hv1 : 0 < v + 1 := by linarith
    calc ‖t‖ * (v + 1) ≤ 1 / (2 * (v + 1)) * (v + 1) := by gcongr
      _ = 1 / 2 := by field_simp
  have : |y| ^ 2 * ∫ w, (w + σ) ^ 2 ∂ρ ≤ |y| / 2 := by
    calc |y| ^ 2 * ∫ w, (w + σ) ^ 2 ∂ρ ≤ |y| ^ 2 * (v + 1) := by gcongr
      _ = |y| * (|y| * (v + 1)) := by ring
      _ ≤ |y| * (1 / 2) := by gcongr
      _ = |y| / 2 := by ring
  rw [hnt]
  linarith

variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The marked telescope error at fixed discount, as a function of the mark. -/
def stripMarkedGap (ν : ProbabilityMeasure ℝ) (β a : ℝ) (ρ : Measure ℝ) (μ l : ℝ) (q s : ℂ) : ℂ :=
  cepsD ρ μ q s * cepsStripSeries ν β a l 0 (-s) q - stripNormalGap dom ρ μ q l s

/-- The mark-direction disc radius. -/
def stripMarkRadius (dom : CepsCanonDomain D θ v) (l : ℝ) : ℝ :=
  min (min (dom.c₀ / 8) (θ / 4)) (1 / l)

/-- The constant of the mark-direction interpolation. -/
def stripEntranceConstA (dom : CepsCanonDomain D θ v) (Dg vlo vhi : ℝ) : ℝ :=
  let K := max dom.stripExitConst 0
  let ρ' := min (min (dom.c₀ / 8) (θ / 4)) 1
  let Cd := 1 + Real.exp 1 * (2 + 128 * D / θ)
  let A := Cd * Real.exp 1 *
      max (cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0) 0 +
    max dom.stripGapConst 0
  8 * K / ρ' + 2 * K + 32 * A / ρ' ^ 2

include hW hθ hD in
theorem stripMarkedGap_disc {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {l : ℝ}
    (hl : dom.stripEntranceWidth ≤ l) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.q₀)
    {x : ℂ} (hx0 : x.re = 0) (hx : ‖x‖ ≤ dom.c₀ / 8) :
    DifferentiableOn ℂ (stripMarkedGap dom ν β a ρ μ l q) (ball x (stripMarkRadius dom l)) ∧
      ∀ z ∈ ball x (stripMarkRadius dom l), ‖stripMarkedGap dom ν β a ρ μ l q z‖ ≤
        (1 + Real.exp 1 * (2 + 128 * D / θ)) * (Real.exp 1 *
          (cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0 * l ^ 3)) +
        dom.stripGapConst := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hl2 : 2 ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hlW : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hl0 : 0 < l := by linarith
  have hc0 := dom.c₀_pos
  have hκ := krKappa_pos hDg hvlo hvhi
  have hμ1 : |μ| ≤ 1 := by
    have := dom.μ₀_C; have := dom.gF_le; linarith
  have hθ4 : 0 < θ / 4 := by positivity
  set r := stripMarkRadius dom l with hrdef
  have hr1 : r ≤ dom.c₀ / 8 := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ θ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ 1 / l := min_le_right _ _
  have hzpts : ∀ z ∈ ball x r, ‖z‖ ≤ dom.c₀ / 4 ∧ |z.re| < r := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    refine ⟨?_, ?_⟩
    · have := norm_sub_norm_le z x
      linarith
    · have h1 := abs_re_le_norm (z - x)
      rw [sub_re, hx0, sub_zero] at h1
      linarith
  -- the survival budget at the fixed discount
  have hmom := cepsBand_survival_moments hDg hθg hvlo hvhi hν (w := l) (l := l) hl2
    (by linarith) (by linarith) β ha (q := q)
    (by have : 0 ≤ krKappa Dg vlo vhi / (16 * l ^ 2) := by positivity
        linarith) 0 0
  simp only [pow_zero, one_mul, Nat.mul_zero, zero_add] at hmom
  obtain ⟨hsum, hS0⟩ := hmom
  set C0 := cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0
  constructor
  · have hH := cepsStripSeries_differentiableOn (ν := ν) β a hl0.le hsum (R := 1 / l)
    have hG := stripNormalGap_differentiableOn dom hW hθ hD hμ0 hq l
    intro z hz
    obtain ⟨hzn, hzre⟩ := hzpts z hz
    have hzre' : |z.re| < θ / 2 := by linarith
    have hd : DifferentiableAt ℂ (fun s => cepsD ρ μ q s) z := by
      unfold cepsD
      have := differentiableAt_stepTransform_strip hW hθ hD hzre'
      fun_prop
    have hHz : DifferentiableAt ℂ (fun s => cepsStripSeries ν β a l 0 (-s) q) z :=
      (hH z (by show |z.re| < 1 / l; linarith)).differentiableAt
        (IsOpen.mem_nhds (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
          (by show |z.re| < 1 / l; linarith))
    have hGz : DifferentiableAt ℂ (stripNormalGap dom ρ μ q l) z :=
      (hG z (mem_ball_zero_iff.mpr (by linarith))).differentiableAt
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by linarith)))
    exact ((hd.mul hHz).sub hGz).differentiableWithinAt
  · intro z hz
    obtain ⟨hzn, hzre⟩ := hzpts z hz
    have hzre' : |z.re| ≤ θ / 2 := by linarith
    unfold stripMarkedGap
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul]
      have hdn : ‖cepsD ρ μ q z‖ ≤ 1 + Real.exp 1 * (2 + 128 * D / θ) := by
        unfold cepsD
        have h1 : ‖cexp (-q)‖ ≤ 1 := by
          rw [Complex.norm_exp, neg_re]; exact Real.exp_le_one_iff.mpr (by linarith)
        have h2 : ‖cexp (μ * z)‖ ≤ Real.exp 1 := by
          refine (norm_cexp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hz1 : ‖z‖ ≤ 1 := by
            have := dom.c₀_le; have := dom.ρA_one; linarith
          calc |μ| * ‖z‖ ≤ 1 * 1 := mul_le_mul hμ1 hz1 (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
        have h3 := norm_stepTransform_le_strip hW hθ hD.le hzre'
        calc ‖1 - cexp (-q) * cexp (μ * z) * stepTransform ρ z‖ ≤
            ‖(1 : ℂ)‖ + ‖cexp (-q) * cexp (μ * z) * stepTransform ρ z‖ := norm_sub_le _ _
          _ = 1 + ‖cexp (-q)‖ * ‖cexp (μ * z)‖ * ‖stepTransform ρ z‖ := by
            rw [norm_one, norm_mul, norm_mul]
          _ ≤ 1 + 1 * Real.exp 1 * (2 + 128 * D / θ) := by
            refine add_le_add_right (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
              (norm_nonneg _) (by positivity)) 1
          _ = 1 + Real.exp 1 * (2 + 128 * D / θ) := by ring
      have hHn : ‖cepsStripSeries ν β a l 0 (-z) q‖ ≤ Real.exp 1 * (C0 * l ^ 3) := by
        refine (norm_cepsStripSeries_le β a hsum z).trans ?_
        have he : Real.exp (|z.re| * l) ≤ Real.exp 1 := by
          refine Real.exp_le_exp.mpr ?_
          have := mul_le_mul_of_nonneg_right (hzre.le.trans hr3) hl0.le
          rw [show 1 / l * l = 1 by field_simp] at this
          exact this
        exact mul_le_mul he hS0 (tsum_nonneg fun n => mul_nonneg (norm_nonneg _)
          (krSurv_nonneg measurableSet_Icc ν β a n 0)) (Real.exp_pos _).le
      exact mul_le_mul hdn hHn (norm_nonneg _) (by positivity)
    · refine norm_stripNormalGap_le dom hW hθ hD hμ0 hq0 hq hlW hzn ?_
      have := neg_abs_le z.re
      linarith

include hW hθ hD in
/-- On the imaginary mark axis the marked telescope error is the exit error. -/
theorem norm_stripMarkedGap_le {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D₀ : ℝ}
    (hf : CepsGapDensity ν f D₀) (β : ℝ) {a : ℝ} (ha : a ≠ 0) {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    (hqne : q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) {s : ℂ} (hs : s.re = 0)
    (hsn : ‖s‖ ≤ dom.c₀ / 4) :
    ‖stripMarkedGap dom ν β a ρ μ l q s‖ ≤ dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l) := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hl
  have hr := cepsRootR_ne_zero_of dom hθ hD hW hμ0 hq0 (Or.inr hqne)
  have htel := strip_actual_telescope hf β ha hlink hl0.le hs hq0
  have hexit := strip_exit_error_WH dom hW hθ hD ν β a hlink hμ hq0 hq hr hl hs
    (by rwa [show dom.c₀ / 2 / 2 = dom.c₀ / 4 by ring])
  rw [show dom.c₀ / 2 / 2 = dom.c₀ / 4 by ring] at hexit
  have he : stripMarkedGap dom ν β a ρ μ l q s =
      -((cepsStripExit ν β a l 0 (Iio 0) (-s) q -
          (cepsWHNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q s l) +
        (cepsStripExit ν β a l 0 (Ioi l) (-s) q -
          (cepsWHNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q s l)) := by
    unfold stripMarkedGap stripNormalGap
    rw [htel]
    ring
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans hexit

/-- The admissible size of marks. -/
def CepsCanonDomain.stripMarkBound (dom : CepsCanonDomain D θ v) : ℝ :=
  min (dom.c₀ / 16) (min (1 / (2 * (v + 1))) (dom.renewalDiscount / 4))

include hW hθ hD in
/-- **S-3 (a), generic band walk**: the marked entrance error on the marked curve `q = -β t`,
uniformly for `t → 0`. -/
theorem strip_entrance_error_marked {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} {D₀ : ℝ} (hf : CepsGapDensity ν f D₀) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|)
    {μ σ : ℝ} (hσ : |σ| = 1) (hβσ : β + μ = σ)
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : dom.stripEntranceWidth ≤ l) {t : ℂ}
    (ht : t.re = 0) (htn : ‖t‖ ≤ dom.stripMarkBound) :
    ‖cepsStripSeries ν β a l 0 (-t) (-β * t) -
        (cepsNormalData D θ ρ μ (-β * t)).regularEntrance (dom.canonL ρ) μ (-β * t) l t‖ ≤
      2 * (stripEntranceConstA dom Dg vlo vhi * (1 + l) ^ 7 *
          Real.exp (-(dom.c₀ / 4 / 2) * l)) +
        4 * (stripEntranceConstB dom Dg vlo vhi * (1 + l) ^ 7 *
          Real.exp (-(dom.c₀ / 4 / 2) * l)) := by
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, abs_zero] at ha; norm_num at ha
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hμ1 : |μ| ≤ 1 / 128 := by
    have := dom.μ₀_C; have := dom.gF_le; linarith
  have hlW : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hl2 : 2 ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hl0 : 0 ≤ l := by linarith
  have hc0 := dom.c₀_pos
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  have hv0 : 0 ≤ v := le_trans (integral_nonneg fun x => sq_nonneg x) hW.integral_sq_le
  have hβ2 : |β| ≤ 2 := by
    have : β = σ - μ := by linarith
    rw [this]
    calc |σ - μ| ≤ |σ| + |μ| := abs_sub _ _
      _ ≤ 2 := by rw [hσ]; linarith
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0, zero_add] at hβσ
    rw [hβσ] at hμ1
    rw [hσ] at hμ1
    norm_num at hμ1
  have ht1 : ‖t‖ ≤ dom.c₀ / 16 := htn.trans (min_le_left _ _)
  have ht2 : ‖t‖ ≤ 1 / (2 * (v + 1)) := htn.trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht3 : ‖t‖ ≤ dom.renewalDiscount / 4 := htn.trans ((min_le_right _ _).trans (min_le_right _ _))
  set q := -(β : ℂ) * t with hqdef
  have hq0 : 0 ≤ q.re := by simp [hqdef, ht]
  have hqre : q.re = 0 := by simp [hqdef, ht]
  have hqn : ‖q‖ ≤ 2 * ‖t‖ := by
    rw [hqdef, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hβ2 (norm_nonneg _)
  have hqh : ‖q‖ ≤ dom.renewalDiscount / 2 := by linarith
  set E := Real.exp (-(dom.c₀ / 4 / 2) * l) with hEdef
  have hE0 : 0 < E := Real.exp_pos _
  set Ka := stripEntranceConstA dom Dg vlo vhi with hKadef
  set Kb := stripEntranceConstB dom Dg vlo vhi with hKbdef
  -- nonnegativity of the constants
  have hKb0 : 0 ≤ Kb := by
    have hK : 0 ≤ max dom.stripExitConst 0 := le_max_right _ _
    have hnr := cepsNormal_negativeRadius_pos dom hD
    have hκ := krKappa_pos hDg hvlo hvhi
    have hsc : 0 < stripDiscScale dom Dg vlo vhi := lt_min (by positivity) hnr
    have hρ' : 0 < min (dom.renewalDiscount / 2) (stripDiscScale dom Dg vlo vhi) :=
      lt_min (by positivity) hsc
    rw [hKbdef]
    unfold stripEntranceConstB
    dsimp only
    positivity
  have hKa0 : 0 ≤ Ka := by
    have hK : 0 ≤ max dom.stripExitConst 0 := le_max_right _ _
    have hρ' : 0 < min (min (dom.c₀ / 8) (θ / 4)) 1 := lt_min (lt_min (by positivity)
      (by positivity)) one_pos
    rw [hKadef]
    unfold stripEntranceConstA
    dsimp only
    positivity
  have hB0 : 0 ≤ Kb * (1 + l) ^ 7 * E := by positivity
  have hA0 : 0 ≤ Ka * (1 + l) ^ 7 * E := by positivity
  by_cases ht0 : t = 0
  · -- zero mark: the unmarked estimate at zero discount
    have hq00 : q = 0 := by rw [hqdef, ht0, mul_zero]
    have hb := strip_entrance_error_unmarked dom hW hθ hD hDg hθg hvlo hvhi hν hf β ha hlink hμ hl
      (q := 0) (by simp) (by simp; positivity)
    have hgoal : cepsStripSeries ν β a l 0 (-t) q -
        (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l t =
        cepsBottomSurv ν β a 0 l -
          (cepsNormalData D θ ρ μ 0).regularEntrance (dom.canonL ρ) μ 0 l 0 := by
      rw [hq00, ht0, cepsStripSeries_zero_eq_surv]
      rfl
    rw [hgoal]
    refine hb.trans ?_
    linarith
  -- non-zero mark
  have hqne : q ≠ 0 := by
    rw [hqdef]
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hβ0)) ht0
  have hr := cepsRootR_ne_zero_of dom hθ hD hW hμ0 hq0 (Or.inr hqne)
  have hq0' : ‖q‖ ≤ dom.q₀ := by
    have : dom.renewalDiscount ≤ dom.q₀ := min_le_left _ _
    linarith
  -- the curve denominator
  have hdcurve : cepsD ρ μ q t = 1 - cexp (σ * t) * stepTransform ρ t := by
    unfold cepsD
    rw [hqdef, ← hβσ]
    have : cexp (-(-(β : ℂ) * t)) * cexp (μ * t) = cexp (((β + μ : ℝ) : ℂ) * t) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]
  have hdlow : ‖t‖ / 2 ≤ ‖cepsD ρ μ q t‖ := by
    rw [hdcurve]; exact norm_curve_denominator_ge hW hσ ht ht2
  have htpos : 0 < ‖t‖ := norm_pos_iff.mpr ht0
  have hdne : cepsD ρ μ q t ≠ 0 := norm_pos_iff.mp (by linarith)
  -- the interpolation along the mark axis
  set F := stripMarkedGap dom ν β a ρ μ l q with hFdef
  set c := dom.c₀ / 4 with hcdef
  have hc : 0 < c := by positivity
  set r := stripMarkRadius dom l with hrdef
  set ρ' := min (min (dom.c₀ / 8) (θ / 4)) 1 with hρ'def
  have hρ' : 0 < ρ' := lt_min (lt_min (by positivity) (by positivity)) one_pos
  have hl1 : 1 ≤ 1 + l := by linarith
  have hrlow : ρ' / (1 + l) ^ 2 ≤ r := by
    have hp : 1 ≤ (1 + l) ^ 2 := one_le_pow₀ hl1
    apply le_min
    · calc ρ' / (1 + l) ^ 2 ≤ ρ' / 1 := div_le_div_of_nonneg_left hρ'.le one_pos hp
        _ = ρ' := div_one _
        _ ≤ _ := min_le_left _ _
    · calc ρ' / (1 + l) ^ 2 ≤ 1 / (1 + l) ^ 2 :=
            div_le_div_of_nonneg_right (min_le_right _ _) (by positivity)
        _ ≤ 1 / l := div_le_div_of_nonneg_left zero_le_one (by linarith) (by nlinarith)
  have hrpos : 0 < r := lt_of_lt_of_le (div_pos hρ' (by positivity)) hrlow
  have hr1 : r ≤ dom.c₀ / 8 := (min_le_left _ _).trans (min_le_left _ _)
  set h := min (r / 4) (Real.exp (-(c / 2) * l)) with hhdef
  have hh : 0 < h := lt_min (by positivity) (Real.exp_pos _)
  have hhr : h < r / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set K := max dom.stripExitConst 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  set C0 := cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0
  set Cd := 1 + Real.exp 1 * (2 + 128 * D / θ) with hCddef
  have hCd : 0 ≤ Cd := by positivity
  set A := Cd * Real.exp 1 * max C0 0 + max dom.stripGapConst 0 with hAdef
  have hA : 0 ≤ A := by positivity
  set M := Cd * (Real.exp 1 * (C0 * l ^ 3)) + dom.stripGapConst with hMdef
  have hM : M ≤ A * (1 + l) ^ 3 := by
    have h1 : C0 * l ^ 3 ≤ max C0 0 * (1 + l) ^ 3 :=
      calc C0 * l ^ 3 ≤ max C0 0 * l ^ 3 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C0 0 * (1 + l) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 (by linarith) 3) (le_max_right _ _)
    have h2 : dom.stripGapConst ≤ max dom.stripGapConst 0 * (1 + l) ^ 3 :=
      (le_max_left _ _).trans (le_mul_of_one_le_right (le_max_right _ _) (one_le_pow₀ hl1))
    calc M ≤ Cd * (Real.exp 1 * (max C0 0 * (1 + l) ^ 3)) + max dom.stripGapConst 0 * (1 + l) ^ 3 := by
          rw [hMdef]; gcongr
      _ = A * (1 + l) ^ 3 := by rw [hAdef]; ring
  have hseg : ∀ x ∈ segment ℝ 0 t, x.re = 0 ∧ ‖x‖ ≤ ‖t‖ := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_segment_zero_iff.mp hx
    refine ⟨by simp [ht], ?_⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2
  have hsmall : ∀ x : ℂ, x.re = 0 → ‖x‖ ≤ dom.c₀ / 4 → ‖F x‖ ≤ K * Real.exp (-c * l) := by
    intro x hx hxn
    exact (norm_stripMarkedGap_le dom hW hθ hD hf β ha0 hlink hμ hq0 (by linarith) hqne hlW hx
      hxn).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have heng := norm_sub_le_of_small_on_segment (F := F) (q := t) (u := Complex.I) (by simp) hrpos hh
    hhr
    (fun x hx => (stripMarkedGap_disc dom hW hθ hD hDg hθg hvlo hvhi hν β ha hμ hl hq0 hq0'
      (hseg x hx).1 ((hseg x hx).2.trans (by linarith))).1)
    (fun x hx => (stripMarkedGap_disc dom hW hθ hD hDg hθg hvlo hvhi hν β ha hμ hl hq0 hq0'
      (hseg x hx).1 ((hseg x hx).2.trans (by linarith))).2)
    (fun x hx => hsmall x (hseg x hx).1 ((hseg x hx).2.trans (by linarith)))
    (fun x hx => by
      obtain ⟨hxr, hxn⟩ := hseg x hx
      refine hsmall _ (by simp [hxr]) ?_
      calc ‖x + (h : ℂ) * Complex.I‖ ≤ ‖x‖ + h := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hh]
        _ ≤ dom.c₀ / 16 + r / 4 := add_le_add (hxn.trans ht1) (min_le_left _ _)
        _ ≤ dom.c₀ / 4 := by linarith)
  have hbud := interp_budget_le hc hK hA hρ' hl0 hrlow hM
  have hKa : 8 * K / ρ' + 2 * K + 32 * A / ρ' ^ 2 = Ka := rfl
  rw [hKa] at hbud
  have hFt0 : ‖F t - F 0‖ ≤ Ka * (1 + l) ^ 7 * E * ‖t‖ := by
    refine heng.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    rw [hEdef, hcdef] at *
    exact hbud
  -- `F 0` is the unmarked telescope error
  have hd0 := cepsD_zero_eq hW (μ : ℂ) q
  have hd0ne : cepsD ρ μ q 0 ≠ 0 := by
    rw [hd0]
    have hqh' : ‖q‖ ≤ 1 / 2 := hqh.trans (by have := renewalDiscount_le_half dom; linarith)
    have := cepsBandDisc_norm_exp_sub_one_lower hqh'
    have : 0 < ‖q‖ := norm_pos_iff.mpr hqne
    exact norm_pos_iff.mp (by linarith)
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hid0 := strip_normal_identity_WH dom hW hθ hD hμ0 hq0 hq0' hr hlW (t := 0)
    (by simp; positivity) hd0ne
  have hreg0 := (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμc hq0' (dom.canonL ρ) l
    (t := 0) (mem_ball_zero_iff.mpr (by simp; exact dom.ρA_pos))).1
  have hF0 : F 0 = stripUnmarkedGap dom ν β a ρ μ l q := by
    rw [hFdef]
    unfold stripMarkedGap stripUnmarkedGap stripNormalGap
    rw [← hid0, hreg0, cepsStripSeries_zero_eq_surv, hd0]
    unfold cepsBottomSurv
    ring
  have hF0b := norm_stripUnmarkedGap_le_mul dom hW hθ hD hDg hθg hvlo hvhi hν hf β ha hlink hμ hl
    hq0 hqh
  rw [← hF0] at hF0b
  -- `F t` is `d(t) (H_t - Ĥ_t)`
  have hidt := strip_normal_identity_WH dom hW hθ hD hμ0 hq0 hq0' hr hlW (t := t)
    (by linarith) hdne
  have hregt := (cepsNormal_actual_regular_forms_eq dom hW hθ hD hμc hq0' (dom.canonL ρ) l
    (t := t) (mem_ball_zero_iff.mpr (by linarith))).1
  have hFt : F t = cepsD ρ μ q t * (cepsStripSeries ν β a l 0 (-t) q -
      (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l t) := by
    rw [hFdef]
    unfold stripMarkedGap stripNormalGap
    rw [← hidt, hregt]
    ring
  -- divide by `|d(t)| ≥ |t|/2`
  have hdpos : 0 < ‖cepsD ρ μ q t‖ := lt_of_lt_of_le (by positivity) hdlow
  have hnum : ‖F t‖ ≤ Ka * (1 + l) ^ 7 * E * ‖t‖ + Kb * (1 + l) ^ 7 * E * (2 * ‖t‖) := by
    calc ‖F t‖ ≤ ‖F t - F 0‖ + ‖F 0‖ := by
          have := norm_add_le (F t - F 0) (F 0); rwa [sub_add_cancel] at this
      _ ≤ _ := add_le_add hFt0 (hF0b.trans (mul_le_mul_of_nonneg_left hqn hB0))
  rw [hFt, norm_mul] at hnum
  rw [← mul_le_mul_iff_of_pos_left hdpos]
  calc _ ≤ Ka * (1 + l) ^ 7 * E * ‖t‖ + Kb * (1 + l) ^ 7 * E * (2 * ‖t‖) := hnum
    _ = ‖t‖ / 2 * (2 * (Ka * (1 + l) ^ 7 * E) + 4 * (Kb * (1 + l) ^ 7 * E)) := by ring
    _ ≤ ‖cepsD ρ μ q t‖ * (2 * (Ka * (1 + l) ^ 7 * E) + 4 * (Kb * (1 + l) ^ 7 * E)) :=
      mul_le_mul_of_nonneg_right hdlow (by positivity)

end

end PGM
