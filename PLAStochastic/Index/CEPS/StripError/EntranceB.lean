import PLAStochastic.Index.CEPS.StripError.MarkHolo
import PLAStochastic.Index.CEPS.StripError.Interp
import PLAStochastic.Index.CEPS.BandDisc.Main

/-!
# WP9, S-3 (b): the unmarked entrance error, including zero discount

For the band walk started at `0`, `h(q) = cepsBottomSurv ν β a q l` (the unmarked entrance) and the
regular normal entrance `ĥ(q)` at mark `0`. The telescope error
`F̃(q) = (1 - e^{-q}) (h(q) - ĥ(q)) = (û₀ + ℓ̂₀) - (u₀ + ℓ₀)` is exponentially small on the closed
right half-disc away from `q = 0` (exit error), vanishes at `q = 0`, and is holomorphic and
polynomially bounded on discs of radius `≍ l⁻²` (X7 actual and WP5 normal negative-discount
extensions). The interpolation engine in the direction of increasing `Re q` gives
`‖F̃(q)‖ ≤ ε₂ ‖q‖`, and `|1 - e^{-q}| ≥ |q|/2` gives `‖h - ĥ‖ ≤ 2 ε₂` for `q ≠ 0`; the point
`q = 0` follows by continuity (`strip_entrance_error_unmarked`).
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open WienerHopf

namespace CepsCanonDomain

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

/-- The width threshold of the entrance errors. -/
def stripEntranceWidth : ℝ :=
  max (max dom.normalWidthThreshold 2) (max dom.normalNegativeWidth dom.normalCoarseWidth)

end CepsCanonDomain

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρ fρ D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The unmarked telescope error `(1 - e^{-q}) (h - ĥ)`. -/
def stripUnmarkedGap (ν : ProbabilityMeasure ℝ) (β a : ℝ) (ρ : Measure ℝ) (μ l : ℝ) (q : ℂ) : ℂ :=
  (1 - cexp (-q)) * (cepsBottomSurv ν β a q l -
    (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l 0)

theorem stripUnmarkedGap_zero (ν : ProbabilityMeasure ℝ) (β a : ℝ) (ρ : Measure ℝ) (μ l : ℝ) :
    stripUnmarkedGap dom ν β a ρ μ l 0 = 0 := by
  simp [stripUnmarkedGap]

theorem renewalDiscount_le_half : dom.renewalDiscount ≤ 1 / 2 := by
  have h1 : dom.renewalDiscount ≤ dom.q₀ := min_le_left _ _
  have h2 := dom.rmax_one
  have h3 := dom.rmax_pos
  rw [dom.q₀_def] at h1
  nlinarith

include hW in
theorem cepsD_zero_eq (μ q : ℂ) : cepsD ρ μ q 0 = 1 - cexp (-q) := by
  unfold cepsD
  rw [stepTransform_zero hW]
  simp

include hW hθ hD in
/-- **The telescope error is exponentially small away from zero discount.** -/
theorem norm_stripUnmarkedGap_le {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D₀ : ℝ}
    (hf : CepsGapDensity ν f D₀) (β : ℝ) {a : ℝ} (ha : a ≠ 0) {μ : ℝ}
    (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    (hqne : q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l) :
    ‖stripUnmarkedGap dom ν β a ρ μ l q‖ ≤ dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l) := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := hq.trans (min_le_left _ _)
  obtain ⟨hl0, -, -⟩ := cepsNormal_width_properties dom hW hθ hD hl
  have hqh : ‖q‖ ≤ 1 / 2 := hq.trans (renewalDiscount_le_half dom)
  have hd0 := cepsD_zero_eq hW (μ : ℂ) q
  have hdne : cepsD ρ μ q 0 ≠ 0 := by
    rw [hd0]
    have h := cepsBandDisc_norm_exp_sub_one_lower hqh
    have : 0 < ‖q‖ := norm_pos_iff.mpr hqne
    exact norm_pos_iff.mp (by linarith)
  have hr := cepsRootR_ne_zero_of dom hθ hD hW hμ0 hq0 (Or.inr hqne)
  have hc0 := dom.c₀_pos
  have htel := strip_actual_telescope hf β ha hlink hl0.le (t := 0) (by simp) hq0
  rw [cepsStripSeries_zero_eq_surv] at htel
  have hnorm := strip_normal_identity dom hW hθ hD hμ0 hq0 hq0' hr hl (t := 0)
    (by simp; positivity) hdne
  have hexit := strip_exit_error dom hθ hD hW ν β a hlink hμ hq0 hq (Or.inr hqne) hl (t := 0)
    (by simp) (by simp; positivity)
  have htel' : cepsD ρ μ q 0 * cepsBottomSurv ν β a q l =
      1 - cepsStripExit ν β a l 0 (Iio 0) (-0) q - cepsStripExit ν β a l 0 (Ioi l) (-0) q := htel
  have he : stripUnmarkedGap dom ν β a ρ μ l q =
      -((cepsStripExit ν β a l 0 (Iio 0) (-0) q -
          (cepsNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q 0 l) +
        (cepsStripExit ν β a l 0 (Ioi l) (-0) q -
          (cepsNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q 0 l)) := by
    unfold stripUnmarkedGap
    rw [← hd0, mul_sub, htel', hnorm]
    ring
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans hexit

/-! ## Holomorphy and the polynomial budget on discs of radius `≍ l⁻²` -/

/-- The disc radius scale `min(κ/32, normalNegativeRadius)`. -/
def stripDiscScale (dom : CepsCanonDomain D θ v) (Dg vlo vhi : ℝ) : ℝ :=
  min (krKappa Dg vlo vhi / 32) dom.normalNegativeRadius

/-- The disc radius at width `l`. -/
def stripDiscRadius (dom : CepsCanonDomain D θ v) (Dg vlo vhi l : ℝ) : ℝ :=
  min (dom.renewalDiscount / 2) (stripDiscScale dom Dg vlo vhi / l ^ 2)

include hW hθ hD in
theorem stripUnmarkedGap_disc {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {l : ℝ}
    (hl : dom.stripEntranceWidth ≤ l) {x : ℂ} (hx0 : 0 ≤ x.re)
    (hx : ‖x‖ ≤ dom.renewalDiscount / 2) :
    DifferentiableOn ℂ (stripUnmarkedGap dom ν β a ρ μ l)
        (ball x (stripDiscRadius dom Dg vlo vhi l)) ∧
      ∀ z ∈ ball x (stripDiscRadius dom Dg vlo vhi l),
        ‖stripUnmarkedGap dom ν β a ρ μ l z‖ ≤
          (1 + Real.exp 1) *
            (cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0 * l ^ 3 +
              dom.normalNegativeEntranceBound * (1 + l) ^ 2) := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hl2 : 2 ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hlN : dom.normalNegativeWidth ≤ l := (le_max_left _ _).trans ((le_max_right _ _).trans hl)
  have hlNC : max dom.normalNegativeWidth dom.normalCoarseWidth ≤ l := (le_max_right _ _).trans hl
  have hl0 : 0 < l := by linarith
  have hκ := krKappa_pos hDg hvlo hvhi
  have hnr := cepsNormal_negativeRadius_pos dom hD
  have hrD := renewalDiscount_le_half dom
  have hrDq : dom.renewalDiscount ≤ dom.q₀ := min_le_left _ _
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  set r := stripDiscRadius dom Dg vlo vhi l with hrdef
  have hr1 : r ≤ dom.renewalDiscount / 2 := min_le_left _ _
  have hr2 : r ≤ stripDiscScale dom Dg vlo vhi / l ^ 2 := min_le_right _ _
  have hscale1 : stripDiscScale dom Dg vlo vhi ≤ krKappa Dg vlo vhi / 32 := min_le_left _ _
  have hscale2 : stripDiscScale dom Dg vlo vhi ≤ dom.normalNegativeRadius := min_le_right _ _
  have hl2' : 0 < l ^ 2 := by positivity
  have hzpts : ∀ z ∈ ball x r, ‖z‖ < dom.q₀ ∧ -(stripDiscScale dom Dg vlo vhi / l ^ 2) < z.re ∧
      -r < z.re := by
    intro z hz
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z‖ < dom.q₀ := by
      have := norm_sub_norm_le z x
      linarith
    have h2 : -r < z.re := by
      have := neg_abs_le (z - x).re
      have := abs_re_le_norm (z - x)
      simp only [sub_re] at *
      linarith
    exact ⟨h1, by linarith, h2⟩
  have hact : ∀ z ∈ ball x r, AnalyticAt ℂ (fun z => cepsBottomSurv ν β a z l) z ∧
      ‖cepsBottomSurv ν β a z l‖ ≤
        cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0 * l ^ 3 := by
    intro z hz
    obtain ⟨-, hre, -⟩ := hzpts z hz
    have hre' : -(krKappa Dg vlo vhi / (32 * l ^ 2)) ≤ z.re := by
      have : stripDiscScale dom Dg vlo vhi / l ^ 2 ≤ krKappa Dg vlo vhi / (32 * l ^ 2) := by
        rw [div_le_div_iff₀ hl2' (by positivity)]
        nlinarith
      linarith
    refine ⟨cepsBandDisc_survival_analyticAt hDg hθg hvlo hvhi hν (w := l) (l := l) hl2
      (by linarith) (by linarith) β ha hre' 0, ?_⟩
    have h := cepsBandDisc_survival_iteratedDeriv_le hDg hθg hvlo hvhi hν (w := l) (l := l) hl2
      (by linarith) (by linarith) β ha hre' 0 0
    rw [iteratedDeriv_zero] at h
    exact h
  have hnormal : ∀ z ∈ ball x r,
      AnalyticAt ℂ (fun z => (cepsNormalData D θ ρ μ z).regularEntrance (dom.canonL ρ) μ z l 0) z ∧
      ‖(cepsNormalData D θ ρ μ z).regularEntrance (dom.canonL ρ) μ z l 0‖ ≤
        dom.normalNegativeEntranceBound * (1 + l) ^ 2 := by
    intro z hz
    obtain ⟨h1, hre, -⟩ := hzpts z hz
    have hre' : -(dom.normalNegativeRadius / l ^ 2) < z.re := by
      have : stripDiscScale dom Dg vlo vhi / l ^ 2 ≤ dom.normalNegativeRadius / l ^ 2 :=
        div_le_div_of_nonneg_right hscale2 hl2'.le
      linarith
    refine ⟨(cepsNormalData_canonical_analyticOnNhd_negative dom hW hθ hD hμ0 (t := 0)
      (by simp; exact dom.c₀_pos) hlN).1 z ⟨h1, hre'⟩, ?_⟩
    exact cepsNormalData_canonical_regularEntrance_bound_negative dom hW hθ hD hμ0 h1.le
        (t := 0) (by simp; exact (div_pos dom.c₀_pos (by norm_num)).le) (by simp) hlNC hre'.le
  constructor
  · intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    unfold stripUnmarkedGap
    have h1 := (hact z hz).1.differentiableAt
    have h2 := (hnormal z hz).1.differentiableAt
    fun_prop
  · intro z hz
    obtain ⟨-, -, hre⟩ := hzpts z hz
    unfold stripUnmarkedGap
    rw [norm_mul]
    have he : ‖1 - cexp (-z)‖ ≤ 1 + Real.exp 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one, Complex.norm_exp, neg_re]
      have : r ≤ 1 := by linarith
      gcongr
      linarith
    refine mul_le_mul he ((norm_sub_le _ _).trans (add_le_add (hact z hz).2 (hnormal z hz).2))
      (norm_nonneg _) (by positivity)

theorem segment_zero_re_norm {q x : ℂ} (hq0 : 0 ≤ q.re) (hx : x ∈ segment ℝ 0 q) :
    0 ≤ x.re ∧ ‖x‖ ≤ ‖q‖ := by
  obtain ⟨s, hs, rfl⟩ := mem_segment_zero_iff.mp hx
  refine ⟨?_, ?_⟩
  · simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hs.1 hq0
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hs.2

/-- The class constant of the unmarked entrance error. -/
def stripEntranceConstB (dom : CepsCanonDomain D θ v) (Dg vlo vhi : ℝ) : ℝ :=
  let K := max dom.stripExitConst 0
  let ρ' := min (dom.renewalDiscount / 2) (stripDiscScale dom Dg vlo vhi)
  let A := (1 + Real.exp 1) *
    (max (cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0) 0 +
      max dom.normalNegativeEntranceBound 0)
  8 * K / ρ' + 2 * K + 32 * A / ρ' ^ 2

include hW hθ hD in
/-- The telescope error is `O((1+l)⁷ e^{-c₀ l/8}) ‖q‖` on the closed right half-disc. -/
theorem norm_stripUnmarkedGap_le_mul {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} {D₀ : ℝ} (hf : CepsGapDensity ν f D₀) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|)
    {μ : ℝ} (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : dom.stripEntranceWidth ≤ l) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount / 2) :
    ‖stripUnmarkedGap dom ν β a ρ μ l q‖ ≤
      stripEntranceConstB dom Dg vlo vhi * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 4 / 2) * l) *
        ‖q‖ := by
  have ha0 : a ≠ 0 := by
    intro h0; rw [h0, abs_zero] at ha; norm_num at ha
  have hlW : dom.normalWidthThreshold ≤ l := (le_max_left _ _).trans ((le_max_left _ _).trans hl)
  have hl2 : 2 ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
  have hl0 : 0 ≤ l := by linarith
  have hc0 := dom.c₀_pos
  have hκ := krKappa_pos hDg hvlo hvhi
  have hnr := cepsNormal_negativeRadius_pos dom hD
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  set c := dom.c₀ / 4 with hcdef
  have hc : 0 < c := by positivity
  set K := max dom.stripExitConst 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  set C0 := cepsBandMomentConst (cepsBandDecayConst Dg vlo vhi) (krKappa Dg vlo vhi) 0
  set CN := dom.normalNegativeEntranceBound
  set A := (1 + Real.exp 1) * (max C0 0 + max CN 0) with hAdef
  have hA : 0 ≤ A := by positivity
  set sc := stripDiscScale dom Dg vlo vhi with hscdef
  have hsc : 0 < sc := lt_min (by positivity) hnr
  set ρ' := min (dom.renewalDiscount / 2) sc with hρ'def
  have hρ' : 0 < ρ' := lt_min (by positivity) hsc
  set r := stripDiscRadius dom Dg vlo vhi l with hrdef
  have hl1 : 1 ≤ 1 + l := by linarith
  have hrlow : ρ' / (1 + l) ^ 2 ≤ r := by
    have hp : 0 < (1 + l) ^ 2 := by positivity
    apply le_min
    · calc ρ' / (1 + l) ^ 2 ≤ ρ' / 1 := div_le_div_of_nonneg_left hρ'.le one_pos
            (one_le_pow₀ hl1)
        _ = ρ' := div_one _
        _ ≤ _ := min_le_left _ _
    · exact div_le_div₀ hsc.le (min_le_right _ _) (by positivity) (by nlinarith)
  have hr : 0 < r := lt_of_lt_of_le (div_pos hρ' (by positivity)) hrlow
  have hr1 : r ≤ dom.renewalDiscount / 2 := min_le_left _ _
  set M := (1 + Real.exp 1) * (C0 * l ^ 3 + CN * (1 + l) ^ 2) with hMdef
  have hM : M ≤ A * (1 + l) ^ 3 := by
    rw [hMdef, hAdef, mul_assoc]
    gcongr
    have h1 : C0 * l ^ 3 ≤ max C0 0 * (1 + l) ^ 3 :=
      calc C0 * l ^ 3 ≤ max C0 0 * l ^ 3 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C0 0 * (1 + l) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 (by linarith) 3) (le_max_right _ _)
    have h2 : CN * (1 + l) ^ 2 ≤ max CN 0 * (1 + l) ^ 3 :=
      calc CN * (1 + l) ^ 2 ≤ max CN 0 * (1 + l) ^ 2 :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max CN 0 * (1 + l) ^ 3 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hl1 (by norm_num)) (le_max_right _ _)
    calc C0 * l ^ 3 + CN * (1 + l) ^ 2 ≤ max C0 0 * (1 + l) ^ 3 + max CN 0 * (1 + l) ^ 3 :=
          add_le_add h1 h2
      _ = _ := by ring
  set h := min (r / 4) (Real.exp (-(c / 2) * l)) with hhdef
  have hh : 0 < h := lt_min (by positivity) (Real.exp_pos _)
  have hhr : h < r / 2 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set ε := K * Real.exp (-c * l) with hεdef
  have hsmall : ∀ x : ℂ, 0 ≤ x.re → ‖x‖ ≤ dom.renewalDiscount →
      ‖stripUnmarkedGap dom ν β a ρ μ l x‖ ≤ ε := by
    intro x hx0 hx
    by_cases hx00 : x = 0
    · rw [hx00, stripUnmarkedGap_zero, norm_zero]
      exact mul_nonneg hK (Real.exp_pos _).le
    · exact (norm_stripUnmarkedGap_le dom hW hθ hD hf β ha0 hlink hμ hx0 hx hx00 hlW).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have heng := norm_sub_le_of_small_on_segment (F := stripUnmarkedGap dom ν β a ρ μ l) (q := q)
    (u := 1) (by simp) hr hh hhr
    (fun x hx => (stripUnmarkedGap_disc dom hW hθ hD hDg hθg hvlo hvhi hν β ha hμ hl
      (segment_zero_re_norm hq0 hx).1 ((segment_zero_re_norm hq0 hx).2.trans hq)).1)
    (fun x hx => (stripUnmarkedGap_disc dom hW hθ hD hDg hθg hvlo hvhi hν β ha hμ hl
      (segment_zero_re_norm hq0 hx).1 ((segment_zero_re_norm hq0 hx).2.trans hq)).2)
    (fun x hx => hsmall x (segment_zero_re_norm hq0 hx).1
      (((segment_zero_re_norm hq0 hx).2.trans hq).trans (by linarith)))
    (fun x hx => by
      obtain ⟨hxr, hxn⟩ := segment_zero_re_norm hq0 hx
      refine hsmall _ ?_ ?_
      · simp only [mul_one, add_re, ofReal_re]; linarith
      · calc ‖x + (h : ℂ) * 1‖ ≤ ‖x‖ + h := by
              rw [mul_one]; refine (norm_add_le _ _).trans ?_
              rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
          _ ≤ dom.renewalDiscount / 2 + r / 4 := add_le_add (hxn.trans hq) (min_le_left _ _)
          _ ≤ _ := by linarith)
  rw [stripUnmarkedGap_zero, sub_zero] at heng
  have hbud := interp_budget_le hc hK hA hρ' hl0 hrlow hM
  refine heng.trans ?_
  rw [hcdef] at hbud ⊢
  have hKB : 8 * K / ρ' + 2 * K + 32 * A / ρ' ^ 2 = stripEntranceConstB dom Dg vlo vhi := rfl
  rw [hKB] at hbud
  exact mul_le_mul_of_nonneg_right hbud (norm_nonneg _)

include hW hθ hD in
/-- **S-3 (b), generic band walk**: the unmarked entrance error on the closed right half-disc,
including zero discount and merging roots. -/
theorem strip_entrance_error_unmarked {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} {D₀ : ℝ} (hf : CepsGapDensity ν f D₀) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|)
    {μ : ℝ} (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : dom.stripEntranceWidth ≤ l) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount / 2) :
    ‖cepsBottomSurv ν β a q l -
        (cepsNormalData D θ ρ μ q).regularEntrance (dom.canonL ρ) μ q l 0‖ ≤
      2 * (stripEntranceConstB dom Dg vlo vhi * (1 + l) ^ 7 *
        Real.exp (-(dom.c₀ / 4 / 2) * l)) := by
  set B := stripEntranceConstB dom Dg vlo vhi * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 4 / 2) * l)
    with hBdef
  have hrDh := renewalDiscount_le_half dom
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  -- away from zero discount: divide the telescope error
  have hmain : ∀ z : ℂ, 0 ≤ z.re → ‖z‖ ≤ dom.renewalDiscount / 2 → z ≠ 0 →
      ‖cepsBottomSurv ν β a z l -
        (cepsNormalData D θ ρ μ z).regularEntrance (dom.canonL ρ) μ z l 0‖ ≤ 2 * B := by
    intro z hz0 hz hzne
    have hg := norm_stripUnmarkedGap_le_mul dom hW hθ hD hDg hθg hvlo hvhi hν hf β ha hlink hμ hl
      hz0 hz
    unfold stripUnmarkedGap at hg
    rw [norm_mul] at hg
    have hzh : ‖z‖ ≤ 1 / 2 := hz.trans (by linarith)
    have hlow := cepsBandDisc_norm_exp_sub_one_lower hzh
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
    have hB0 : 0 ≤ B := by
      have := mul_nonneg (norm_nonneg (1 - cexp (-z))) (norm_nonneg (cepsBottomSurv ν β a z l -
        (cepsNormalData D θ ρ μ z).regularEntrance (dom.canonL ρ) μ z l 0))
      have h2 := this.trans hg
      exact nonneg_of_mul_nonneg_left h2 hzpos
    have hpos : 0 < ‖1 - cexp (-z)‖ := lt_of_lt_of_le (by positivity) hlow
    rw [← mul_le_mul_iff_of_pos_left hpos]
    calc _ ≤ B * ‖z‖ := hg
      _ = ‖z‖ / 2 * (2 * B) := by ring
      _ ≤ ‖1 - cexp (-z)‖ * (2 * B) := mul_le_mul_of_nonneg_right hlow (by linarith)
  by_cases hq00 : q = 0
  · -- zero discount by continuity from the positive real axis
    subst hq00
    have hl2 : 2 ≤ l := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
    have hlN : dom.normalNegativeWidth ≤ l :=
      (le_max_left _ _).trans ((le_max_right _ _).trans hl)
    have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
    have hact : ContinuousAt (fun z : ℂ => cepsBottomSurv ν β a z l) 0 :=
      (cepsBandDisc_survival_analyticAt hDg hθg hvlo hvhi hν (w := l) (l := l) hl2 (by linarith)
        (by linarith) β ha (q := 0) (by simp; positivity [krKappa_pos hDg hvlo hvhi]) 0).continuousAt
    have hnor : ContinuousAt (fun z : ℂ =>
        (cepsNormalData D θ ρ μ z).regularEntrance (dom.canonL ρ) μ z l 0) 0 :=
      ((cepsNormalData_canonical_analyticOnNhd_negative dom hW hθ hD hμ0 (t := 0)
        (by simp; exact dom.c₀_pos) hlN).1 0 ⟨by simp; exact dom.q₀_pos, by
          simp; exact div_pos (cepsNormal_negativeRadius_pos dom hD) (by positivity)⟩).continuousAt
    have hcont : ContinuousAt (fun s : ℝ => ‖cepsBottomSurv ν β a (s : ℂ) l -
        (cepsNormalData D θ ρ μ (s : ℂ)).regularEntrance (dom.canonL ρ) μ (s : ℂ) l 0‖) 0 := by
      have hF : ContinuousAt (fun z : ℂ => cepsBottomSurv ν β a z l -
          (cepsNormalData D θ ρ μ z).regularEntrance (dom.canonL ρ) μ z l 0) ((0 : ℝ) : ℂ) := by
        rw [Complex.ofReal_zero]
        exact hact.sub hnor
      have h2 : ContinuousAt (fun s : ℝ => cepsBottomSurv ν β a (s : ℂ) l -
          (cepsNormalData D θ ρ μ (s : ℂ)).regularEntrance (dom.canonL ρ) μ (s : ℂ) l 0) 0 :=
        hF.comp (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt
      exact h2.norm
    have hev : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), ‖cepsBottomSurv ν β a (s : ℂ) l -
        (cepsNormalData D θ ρ μ (s : ℂ)).regularEntrance (dom.canonL ρ) μ (s : ℂ) l 0‖ ≤ 2 * B := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < dom.renewalDiscount / 2 by positivity)]
        with s hs
      refine hmain (s : ℂ) (by simp; exact hs.1.le) ?_ (by exact_mod_cast hs.1.ne')
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      exact hs.2.le
    have ht := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    have := le_of_tendsto ht hev
    simpa using this
  · exact hmain q hq0 hq hq00

end

end PGM
