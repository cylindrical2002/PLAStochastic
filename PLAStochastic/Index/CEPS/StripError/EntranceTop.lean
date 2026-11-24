import PLAStochastic.Index.CEPS.StripError.EntranceA

/-!
# WP9, S-3: entrance errors for the top- and bottom-started strips

Specializations of `strip_entrance_error_unmarked` and `strip_entrance_error_marked` to the two
strips of the gap walk (`ρW = ν ∘ (1 - ·)⁻¹`, step class `IsStepLaw ρW fW D θ v`, canonical domain
`dom`; the actual gap law in the regular class `RegLaw Dg θg vlo vhi` with a density version `f`):

* top-started (`ceps_strip_entrance_error_top`): the entrance `H_t = cepsStripEntrance ν t μ q l`
  of theorem (E) against the regular normal entrance of `ρW` at drift `μ`, (b) on the closed
  right half-disc at `t = 0` and (a) on the marked curve `q = t(1+μ)`;
* bottom-started (`ceps_strip_entrance_error_bottom`): the `Y_μ` walk from `0`, against the
  regular normal entrance of the reflected step law at drift `-μ` and mark `-s`, (b) unmarked
  (`cepsBottomSurv`) and (a) on the drawup curve `q = s(1+μ)`.

All errors are `≤ K (1+l)⁷ e^{-c₀ l/8}` with class constants, for every width
`l ≥ dom.stripEntranceWidth`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open WienerHopf

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

/-- The class constant of the entrance errors. -/
def stripEntranceConst (dom : CepsCanonDomain D θ v) (Dg vlo vhi : ℝ) : ℝ :=
  2 * stripEntranceConstA dom Dg vlo vhi + 4 * stripEntranceConstB dom Dg vlo vhi

theorem cepsStripEntrance_zero_eq (ν : ProbabilityMeasure ℝ) (μ : ℝ) (q : ℂ) (l : ℝ) :
    cepsStripEntrance ν 0 μ q l = cepsBottomSurv ν (-(1 + μ)) (-1) q l := by
  rw [cepsStripEntrance_eq, cepsStripSeries_zero_eq_surv]
  rfl

include hD in
theorem stripEntranceConstB_nonneg {Dg vlo vhi : ℝ} (hDg : 0 < Dg) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) : 0 ≤ stripEntranceConstB dom Dg vlo vhi := by
  have hK : 0 ≤ max dom.stripExitConst 0 := le_max_right _ _
  have hnr := cepsNormal_negativeRadius_pos dom hD
  have hκ := krKappa_pos hDg hvlo hvhi
  have hrD0 : 0 < dom.renewalDiscount := dom.renewalDiscount_pos hD
  have hsc : 0 < stripDiscScale dom Dg vlo vhi := lt_min (by positivity) hnr
  have hρ' : 0 < min (dom.renewalDiscount / 2) (stripDiscScale dom Dg vlo vhi) :=
    lt_min (by positivity) hsc
  unfold stripEntranceConstB
  dsimp only
  positivity

include hθ hD in
theorem stripEntranceConstA_nonneg (Dg vlo vhi : ℝ) : 0 ≤ stripEntranceConstA dom Dg vlo vhi := by
  have hK : 0 ≤ max dom.stripExitConst 0 := le_max_right _ _
  have hc0 := dom.c₀_pos
  have hρ' : 0 < min (min (dom.c₀ / 8) (θ / 4)) 1 :=
    lt_min (lt_min (by positivity) (by positivity)) one_pos
  unfold stripEntranceConstA
  dsimp only
  positivity

include hθ hD in
theorem stripEntranceConst_nonneg {Dg vlo vhi : ℝ} (hDg : 0 < Dg) (hvlo : 0 < vlo)
    (hvhi : vlo ≤ vhi) : 0 ≤ stripEntranceConst dom Dg vlo vhi := by
  have := stripEntranceConstA_nonneg dom hθ hD Dg vlo vhi
  have := stripEntranceConstB_nonneg dom hD hDg hvlo hvhi
  unfold stripEntranceConst
  positivity

include hθ hD in
/-- **S-3 entrance, top-started strip.** -/
theorem ceps_strip_entrance_error_top {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} {D₀ : ℝ} (hf : CepsGapDensity ν f D₀) {fW : ℝ → ℝ}
    (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v)
    {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : dom.stripEntranceWidth ≤ l) :
    (∀ q : ℂ, 0 ≤ q.re → ‖q‖ ≤ dom.renewalDiscount / 2 →
      ‖cepsStripEntrance ν 0 μ q l -
          (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).regularEntrance
            (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q l 0‖ ≤
        stripEntranceConst dom Dg vlo vhi * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l)) ∧
    (∀ t : ℂ, t.re = 0 → ‖t‖ ≤ dom.stripMarkBound →
      ‖cepsStripEntrance ν t μ (t * ((1 + μ : ℝ) : ℂ)) l -
          (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ
            (t * ((1 + μ : ℝ) : ℂ))).regularEntrance
            (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ (t * ((1 + μ : ℝ) : ℂ)) l t‖ ≤
        stripEntranceConst dom Dg vlo vhi * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l)) := by
  have hc8 : dom.c₀ / 4 / 2 = dom.c₀ / 8 := by ring
  have hA0 := stripEntranceConstA_nonneg dom hθ hD Dg vlo vhi
  have hB0 := stripEntranceConstB_nonneg dom hD hDg hvlo hvhi
  have hE0 : 0 ≤ (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l) := by
    have : 0 ≤ l := by
      have := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
      linarith
    positivity
  have ha : 1 / 2 ≤ |(-1 : ℝ)| := by norm_num
  constructor
  · intro q hq0 hq
    have h := strip_entrance_error_unmarked dom hW hθ hD hDg hθg hvlo hvhi hν hf (-(1 + μ)) ha
      (map_top_link ν μ) hμ hl hq0 hq
    rw [cepsStripEntrance_zero_eq, ← hc8]
    refine h.trans ?_
    unfold stripEntranceConst
    rw [hc8] at *
    nlinarith
  · intro t ht htn
    have h := strip_entrance_error_marked dom hW hθ hD hDg hθg hvlo hvhi hν hf (-(1 + μ)) ha
      (σ := -1) (by norm_num) (by ring) (map_top_link ν μ) hμ hl ht htn
    have hq : -(((-(1 + μ) : ℝ)) : ℂ) * t = t * ((1 + μ : ℝ) : ℂ) := by push_cast; ring
    rw [hq, ← cepsStripEntrance_eq] at h
    refine h.trans (le_of_eq ?_)
    unfold stripEntranceConst
    rw [hc8]
    ring

include hθ hD in
/-- **S-3 entrance, bottom-started strip** (against the reflected top-started normal entrance). -/
theorem ceps_strip_entrance_error_bottom {Dg θg vlo vhi : ℝ} (hDg : 0 < Dg) (hθg : 0 < θg)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ} (hν : RegLaw Dg θg vlo vhi ν)
    {f : ℝ → ℝ} {D₀ : ℝ} (hf : CepsGapDensity ν f D₀) {fW : ℝ → ℝ}
    (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v)
    {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {l : ℝ} (hl : dom.stripEntranceWidth ≤ l) :
    (∀ q : ℂ, 0 ≤ q.re → ‖q‖ ≤ dom.renewalDiscount / 2 →
      ‖cepsBottomSurv ν (1 + μ) 1 q l -
          (cepsNormalData D θ (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)
            ((-μ : ℝ) : ℂ) q).regularEntrance
            (dom.canonL (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)) ((-μ : ℝ) : ℂ) q l 0‖ ≤
        stripEntranceConst dom Dg vlo vhi * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l)) ∧
    (∀ s : ℂ, s.re = 0 → ‖s‖ ≤ dom.stripMarkBound →
      ‖cepsStripSeries ν (1 + μ) 1 l 0 s (s * ((1 + μ : ℝ) : ℂ)) -
          (cepsNormalData D θ (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)
            ((-μ : ℝ) : ℂ) (s * ((1 + μ : ℝ) : ℂ))).regularEntrance
            (dom.canonL (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)) ((-μ : ℝ) : ℂ)
            (s * ((1 + μ : ℝ) : ℂ)) l (-s)‖ ≤
        stripEntranceConst dom Dg vlo vhi * (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l)) := by
  have hc8 : dom.c₀ / 4 / 2 = dom.c₀ / 8 := by ring
  have hA0 := stripEntranceConstA_nonneg dom hθ hD Dg vlo vhi
  have hB0 := stripEntranceConstB_nonneg dom hD hDg hvlo hvhi
  have hE0 : 0 ≤ (1 + l) ^ 7 * Real.exp (-(dom.c₀ / 8) * l) := by
    have : 0 ≤ l := by
      have := (le_max_right _ _).trans ((le_max_left _ _).trans hl)
      linarith
    positivity
  have ha : 1 / 2 ≤ |(1 : ℝ)| := by norm_num
  have hμ' : |(-μ)| ≤ dom.renewalMu := by rwa [abs_neg]
  constructor
  · intro q hq0 hq
    have h := strip_entrance_error_unmarked dom hW.neg hθ hD hDg hθg hvlo hvhi hν hf (1 + μ) ha
      (map_bottom_link ν μ) hμ' hl hq0 hq
    refine h.trans ?_
    unfold stripEntranceConst
    rw [hc8] at *
    nlinarith
  · intro s hs hsn
    have h := strip_entrance_error_marked dom hW.neg hθ hD hDg hθg hvlo hvhi hν hf (1 + μ) ha
      (σ := 1) (by norm_num) (by ring) (map_bottom_link ν μ) hμ' hl (t := -s)
      (by rw [neg_re, hs, neg_zero]) (by rwa [norm_neg])
    have hq : -(((1 + μ : ℝ)) : ℂ) * -s = s * ((1 + μ : ℝ) : ℂ) := by ring
    rw [hq, neg_neg] at h
    refine h.trans (le_of_eq ?_)
    unfold stripEntranceConst
    rw [hc8]
    ring

end

end PGM
