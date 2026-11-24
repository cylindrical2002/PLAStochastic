import PLAStochastic.Index.CEPS.StripError.Exit

/-!
# WP9, S-3: exit errors for the top- and bottom-started strips

The generic exit error `strip_exit_error_WH` is transferred to the original root-zone normal data
`cepsNormalData` (both data agree at `t`, `β±`, all in the disc where `cepsQ = cepsQuotA`) and
specialized to the two strips of the gap walk with step class `ρW = ν ∘ (1 - ·)⁻¹`:

* top-started (`ceps_strip_exit_error_top`): the outer walk `kWalk 0 (-(1+μ)) (-1)` of theorem (E),
  normal data of `ρW` at drift `μ`, mark `t` of `Z = -V`;
* bottom-started (`ceps_strip_exit_error_bottom`): the `Y_μ` walk `kWalk 0 (1+μ) 1`, normal data of
  the reflected law `ρW ∘ neg⁻¹` at drift `-μ`, mark `-s` (the form used by WP10 for S-8).

Both hold on the closed right discount half-disc away from the merging point `(μ, q) = (0, 0)`,
for all imaginary marks `‖t‖ ≤ c₀/4` and widths `l ≥ normalWidthThreshold`, with the class
constant `dom.stripExitConst` and rate `c₀/4`.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Complex Metric
open WienerHopf

namespace CepsNormalData

/-- The normal exits only see `Q` at `t`, `β₊`, `β₋`. -/
theorem normal_exits_congr (a b : CepsNormalData) (L : ℂ → ℂ → ℂ → ℂ) (μ q t l : ℂ)
    (hp : a.βp = b.βp) (hm : a.βm = b.βm) (hQt : a.Q t = b.Q t) (hQp : a.Q a.βp = b.Q b.βp)
    (hQm : a.Q a.βm = b.Q b.βm) :
    a.upperExit L μ q t l = b.upperExit L μ q t l ∧
      a.lowerExit L μ q t l = b.lowerExit L μ q t l := by
  obtain ⟨βp, βm, d, Q, ψp, ψm⟩ := a
  obtain ⟨βp', βm', d', Q', ψp', ψm'⟩ := b
  simp only at hp hm hQt hQp hQm
  subst hp hm
  simp only [upperExit, lowerExit, passageY, passageX, delta, decay, pi, overshootPlus,
    overshootMinus, factorMinus, eta]
  rw [show βm + (βp - βm) = βp by ring, show βm + (t - βm) = t by ring, hQt, hQp, hQm]
  exact ⟨rfl, rfl⟩

end CepsNormalData

variable {ρ : Measure ℝ} {fρ : ℝ → ℝ} {D θ v : ℝ}
variable (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
/-- The Morse radius vanishes only at the merging point. -/
theorem cepsRootR_ne_zero_of (hW : IsStepLaw ρ fρ D θ v) {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ}
    (hq0 : 0 ≤ q.re) (hne : μ ≠ 0 ∨ q ≠ 0) : cepsRootR D θ ρ μ q ≠ 0 := by
  intro h0
  rcases hne with hμ0 | hq1
  · have h := cepsRootR_norm_ge_drift dom hW hθ hD hμ hq0
    rw [h0, norm_zero] at h
    have hv := CepsCanonDomain.v_pos hW hθ hD
    have hs : 0 < Real.sqrt (cepsVarLo D) := Real.sqrt_pos.mpr (cepsVarLo_pos hD)
    have : 0 < Real.sqrt (cepsVarLo D) / (3 * v) * |μ| :=
      mul_pos (by positivity) (abs_pos.mpr hμ0)
    linarith
  · have h := cepsRootR_norm_ge_discount dom hW hθ hD hμ hq0
    rw [h0, norm_zero] at h
    have : 0 < Real.sqrt ‖q‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr hq1)
    linarith

include hθ hD in
/-- The exit error for the original root-zone normal data. -/
theorem strip_exit_error (hW : IsStepLaw ρ fρ D θ v) (ν : ProbabilityMeasure ℝ) (β a : ℝ)
    {μ : ℝ} (hlink : (ν : Measure ℝ).map (fun x => a * x - β) = driftStep ρ μ)
    (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    (hne : μ ≠ 0 ∨ q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l)
    {t : ℂ} (ht : t.re = 0) (htn : ‖t‖ ≤ dom.c₀ / 4) :
    ‖cepsStripExit ν β a l 0 (Iio 0) (-t) q -
        (cepsNormalData D θ ρ μ q).upperExit (dom.canonL ρ) μ q t l‖ +
      ‖cepsStripExit ν β a l 0 (Ioi l) (-t) q -
        (cepsNormalData D θ ρ μ q).lowerExit (dom.canonL ρ) μ q t l‖ ≤
      dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l) := by
  have hμ0 : |μ| ≤ dom.μ₀ := hμ.trans (min_le_left _ _)
  have hq0' : ‖q‖ ≤ dom.q₀ := hq.trans (min_le_left _ _)
  have hμc : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hr := cepsRootR_ne_zero_of dom hθ hD hW hμ0 hq0 hne
  have h := strip_exit_error_WH dom hW hθ hD ν β a hlink hμ hq0 hq hr hl ht
    (by rwa [show dom.c₀ / 2 / 2 = dom.c₀ / 4 by ring])
  rw [show dom.c₀ / 2 / 2 = dom.c₀ / 4 by ring] at h
  have hc0 := dom.c₀_pos
  have hρA : dom.c₀ / 4 < dom.ρA := by have := dom.c₀_le; have := dom.ρA_pos; linarith
  have hball : ∀ ζ : ℂ, ‖ζ‖ ≤ dom.c₀ / 4 →
      cepsQ D θ ρ μ q ζ = cepsQuotA D θ ρ μ q ζ := fun ζ hζ =>
    CepsC6.cepsQ_eq_cepsQuotA dom hW hθ hD hμc hq0' (mem_ball_zero_iff.mpr (by linarith))
  obtain ⟨hu, hlo⟩ := CepsNormalData.normal_exits_congr (cepsWHNormalData D θ ρ μ q)
    (cepsNormalData D θ ρ μ q) (dom.canonL ρ) μ q t l rfl rfl (hball t htn)
    (hball _ (dom.norm_rootPlus_le hW hθ hD hμc hq0'))
    (hball _ (dom.norm_rootMinus_le hW hθ hD hμc hq0'))
  rwa [hu, hlo] at h

/-- The outer walk of theorem (E) has the drifted step `W + μ`. -/
theorem map_top_link (ν : ProbabilityMeasure ℝ) (μ : ℝ) :
    (ν : Measure ℝ).map (fun x => -1 * x - -(1 + μ)) =
      driftStep ((ν : Measure ℝ).map fun x => 1 - x) μ := by
  rw [driftStep_one_sub_eq]
  congr 1
  funext x
  ring

/-- The bottom-started `Y_μ` walk is top-started for the reflected step at drift `-μ`. -/
theorem map_bottom_link (ν : ProbabilityMeasure ℝ) (μ : ℝ) :
    (ν : Measure ℝ).map (fun x => 1 * x - (1 + μ)) =
      driftStep (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg) (-μ) := by
  rw [driftStep_sub_one_eq]
  congr 1
  funext x
  ring

include hθ hD in
/-- **S-3, exits, top-started strip** (the outer walk `V` of theorem (E), `Z = -V` the `Y_μ`
walk in `[-l, 0]` from `0`, marks `e^{tZ}`). -/
theorem ceps_strip_exit_error_top (ν : ProbabilityMeasure ℝ) {fW : ℝ → ℝ}
    (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v)
    {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    (hne : μ ≠ 0 ∨ q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l)
    {t : ℂ} (ht : t.re = 0) (htn : ‖t‖ ≤ dom.c₀ / 4) :
    ‖cepsStripExit ν (-(1 + μ)) (-1) l 0 (Iio 0) (-t) q -
        (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).upperExit
          (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q t l‖ +
      ‖cepsStripExit ν (-(1 + μ)) (-1) l 0 (Ioi l) (-t) q -
        (cepsNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) μ q).lowerExit
          (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) μ q t l‖ ≤
      dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l) :=
  strip_exit_error dom hθ hD hW ν (-(1 + μ)) (-1) (map_top_link ν μ) hμ hq0 hq hne hl ht htn

include hθ hD in
/-- **S-3, exits, bottom-started strip** (the `Y_μ` walk in `[0, l]` from `0`, marks `e^{sY}`),
against the top-started normal exits of the reflected step law at drift `-μ`, mark `-s`. -/
theorem ceps_strip_exit_error_bottom (ν : ProbabilityMeasure ℝ) {fW : ℝ → ℝ}
    (hW : IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v)
    {μ : ℝ} (hμ : |μ| ≤ dom.renewalMu) {q : ℂ} (hq0 : 0 ≤ q.re) (hq : ‖q‖ ≤ dom.renewalDiscount)
    (hne : μ ≠ 0 ∨ q ≠ 0) {l : ℝ} (hl : dom.normalWidthThreshold ≤ l)
    {s : ℂ} (hs : s.re = 0) (hsn : ‖s‖ ≤ dom.c₀ / 4) :
    ‖cepsStripExit ν (1 + μ) 1 l 0 (Iio 0) s q -
        (cepsNormalData D θ (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)
          ((-μ : ℝ) : ℂ) q).upperExit
          (dom.canonL (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)) ((-μ : ℝ) : ℂ) q
          (-s) l‖ +
      ‖cepsStripExit ν (1 + μ) 1 l 0 (Ioi l) s q -
        (cepsNormalData D θ (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)
          ((-μ : ℝ) : ℂ) q).lowerExit
          (dom.canonL (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg)) ((-μ : ℝ) : ℂ) q
          (-s) l‖ ≤
      dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l) := by
  have hne' : -μ ≠ 0 ∨ q ≠ 0 := by
    rcases hne with h | h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr h
  have h := strip_exit_error dom hθ hD hW.neg ν (1 + μ) 1 (map_bottom_link ν μ)
    (by rwa [abs_neg]) hq0 hq hne' hl (t := -s) (by rw [neg_re, hs, neg_zero]) (by rwa [norm_neg])
  rwa [neg_neg] at h

end

end PGM
