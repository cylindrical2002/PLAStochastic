import PLAStochastic.Index.CEPS.Total.Drawup
import PLAStochastic.Index.CEPS.StripError.ExitTop

/-!
# WP10: S-8, class form

WP9's bottom-started exit error (`ceps_strip_exit_error_bottom`, S-3 at drift `μ = δ`, mark
`s = t`) discharges the exit hypothesis of the local S-8 (`drawup_close_of_exit_error`). For a
fixed drift `0 < δ ≤ renewalMu`, all laws of the step class, all imaginary marks
`‖t‖ ≤ c₀/4` with `‖t(1+δ)‖ ≤ renewalDiscount` and all widths `l ≥ l₀`,

  `‖E e^{-t S_{τ_l}} - 𝒜_δ(t) e^{-(β₊-t) l}‖ ≤ C e^{-c l}`  (`drawup_close`).
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf

namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
/-- **S-8.** -/
theorem drawup_close (hv : 0 < v) {δ : ℝ} (hδ : 0 < δ) (hδμ : δ ≤ dom.renewalMu) :
    ∃ C c l₀ : ℝ, 0 < c ∧ 0 ≤ C ∧
      ∀ (ν : ProbabilityMeasure ℝ) (fW : ℝ → ℝ),
        IsStepLaw ((ν : Measure ℝ).map fun x => 1 - x) fW D θ v →
      ∀ t : ℂ, t.re = 0 → ‖t‖ ≤ dom.c₀ / 4 → ‖t * (1 + (δ : ℂ))‖ ≤ dom.renewalDiscount →
      ∀ l : ℝ, l₀ ≤ l →
        ‖cepsDrawup ν (1 + δ) 1 l t (t * (1 + (δ : ℂ))) -
            (cepsWHNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) δ
                (t * (1 + (δ : ℂ)))).regularAmplitude
              (dom.canonL ((ν : Measure ℝ).map fun x => 1 - x)) δ (t * (1 + (δ : ℂ))) t *
              exp (-((cepsWHNormalData D θ ((ν : Measure ℝ).map fun x => 1 - x) δ
                (t * (1 + (δ : ℂ)))).βp - t) * l)‖ ≤ C * Real.exp (-c * l) := by
  have hδμ0 : δ ≤ dom.μ₀ := hδμ.trans (min_le_left _ _)
  obtain ⟨G₀, C₁, l₁, hG₀, hl₁, hb⟩ := drawup_close_of_exit_error dom hθ hD hv hδ hδμ0
  set K := max dom.stripExitConst 0
  set c := min (dom.c₀ / 4) (dom.drawupRate δ)
  have hc0 := dom.c₀_pos
  have hrate : 0 < dom.drawupRate δ := by
    unfold CepsCanonDomain.drawupRate
    have := Real.sqrt_pos.mpr (cepsVarLo_pos hD)
    have := Real.sqrt_pos.mpr hv
    positivity
  have hc : 0 < c := lt_min (by positivity) hrate
  refine ⟨K / G₀ + max C₁ 0, c, max l₁ dom.normalWidthThreshold, hc, by positivity, ?_⟩
  intro ν fW hW t ht0 ht htq l hl
  have hq0 : 0 ≤ (t * (1 + (δ : ℂ))).re := by simp [mul_re, ht0]
  have hqq : ‖t * (1 + (δ : ℂ))‖ ≤ dom.q₀ := htq.trans (min_le_left _ _)
  have hexit := ceps_strip_exit_error_bottom dom hθ hD ν hW (μ := δ) (by rwa [abs_of_pos hδ]) hq0 htq (Or.inl hδ.ne')
    ((le_max_right _ _).trans hl) (s := t) ht0 ht
  have hloc := hb ν fW hW t ht0 ht hqq l ((le_max_left _ _).trans hl)
    (dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l)) (by simpa only [neg_neg] using hexit)
  have he1 : Real.exp (-(dom.c₀ / 4) * l) ≤ Real.exp (-c * l) := by
    have hl0 : 0 ≤ l := (le_max_left _ _ |>.trans hl) |> fun h => hl₁.trans h
    exact Real.exp_le_exp.mpr (by nlinarith [min_le_left (dom.c₀ / 4) (dom.drawupRate δ)])
  have he2 : Real.exp (-dom.drawupRate δ * l) ≤ Real.exp (-c * l) := by
    have hl0 : 0 ≤ l := (le_max_left _ _ |>.trans hl) |> fun h => hl₁.trans h
    exact Real.exp_le_exp.mpr (by nlinarith [min_le_right (dom.c₀ / 4) (dom.drawupRate δ)])
  refine hloc.trans ?_
  have hK : dom.stripExitConst ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := le_max_right _ _
  have hE := Real.exp_pos (-c * l)
  calc dom.stripExitConst * Real.exp (-(dom.c₀ / 4) * l) / G₀ +
        C₁ * Real.exp (-dom.drawupRate δ * l)
      ≤ K * Real.exp (-c * l) / G₀ + max C₁ 0 * Real.exp (-c * l) := by
        refine add_le_add (div_le_div_of_nonneg_right ?_ hG₀.le) ?_
        · exact (mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le).trans
            (mul_le_mul_of_nonneg_left he1 hK0)
        · exact (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (Real.exp_pos _).le).trans
            (mul_le_mul_of_nonneg_left he2 (le_max_right _ _))
    _ = (K / G₀ + max C₁ 0) * Real.exp (-c * l) := by ring

end PGM
