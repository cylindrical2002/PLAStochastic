import PLAStochastic.Index.CEPS.Jets.Basic
import PLAStochastic.Index.CEPS.Scaled.MorseChart
import PLAStochastic.Index.GEP.Response.OfInterfaces

/-!
# X8: the step law of a regular law, shrunk domains, and the band at the origin

* `isStepLaw_of_density`: for a regular law `X` (density `f ≤ D e^{-θx}` on `(0, ∞)`, mean one,
  variance at most `vhi`) the step `W = 1 - X` has density `y ↦ f (1 - y)` and lies in the step
  class `(D e^θ, θ, vhi)` (via `IsGapLaw.toStepLaw`).
* `CepsCanonDomain.shrink`: the same class constants with any smaller line scale `σ ≤ c₀`;
  `rmax` and `μ₀` scale by `σ/c₀`, `q₀ = rmax²/2` is recomputed, and `d₀`, `CF` are unchanged.
* `cepsQuad_origin`, `cepsF_origin`: at `(μ, q) = (0, 0)` both roots vanish, so `D₀ = s²` and
  `F(s; 0, 0) = (1 - M₀(s))(s² - 1)/s² = cepsJetF s M₀(s)` (with `γ = 1`, as in `canonL`).
* `CepsCanonDomain.re_cepsJetF_ge_of_band`, `…norm_one_sub_stepTransform_ge_of_band`: the line
  bounds `Re F ≥ d₀`, `‖F‖ ≤ CF`, `‖1 - M₀‖ ≥ min g (v₋ (Re s/2)²/32)` at the origin hold on the
  whole strip `0 < Re s ≤ 2 c₀` (apply C-1 to the domain shrunk to `σ = Re s / 2`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex

namespace PGM

/-! ### The step law of a regular law -/

/-- The step `W = 1 - X` of a regular law with density `f` is in the step class
`(D e^θ, θ, vhi)`, with density `y ↦ f (1 - y)`. -/
theorem isStepLaw_of_density {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D θ vhi : ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hneg : ∀ x, x ≤ 0 → f x = 0)
    (hfb : ∀ x, f x ≤ D * Real.exp (-θ * x))
    (hν : (ν : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hmean : lawMean ν = 1) (hvar : lawVar ν ≤ vhi) (hθ : 0 < θ) (hD : 0 ≤ D) :
    WienerHopf.IsStepLaw (volume.withDensity fun y => ENNReal.ofReal (f (1 - y)))
      (fun y => f (1 - y)) (D * Real.exp θ) θ vhi := by
  have hreg : RegLaw D θ (lawVar ν) vhi ν :=
    ⟨⟨f, hfm, hf0, hneg, hfb, hν⟩, hmean, le_rfl, hvar⟩
  have hsq : Integrable (fun x : ℝ => (x - 1) ^ 2) (ν : Measure ℝ) := by
    have e : (fun x : ℝ => (x - 1) ^ 2) = fun x => x ^ 2 - 2 * x + 1 := by ext x; ring
    rw [e]
    exact ((hreg.tail_sq hθ).1.sub ((hreg.tail_mean hθ).1.const_mul 2)).add (integrable_const _)
  have hX : WienerHopf.IsGapLaw (ν : Measure ℝ) f D θ vhi :=
    ⟨inferInstance, hν, hfm, hf0, hneg, fun x _ => hfb x, hsq, hmean, by
      simpa [lawVar, hmean] using hvar⟩
  have h := hX.toStepLaw hθ.le hD
  have e := h.eq_withDensity
  rw [e] at h
  exact h

/-! ### Shrinking the line scale -/

private theorem scale_le_aux {X B t : ℝ} (h : X ≤ B) (hB : 0 ≤ B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * X ≤ B :=
  (mul_le_mul_of_nonneg_left h ht0).trans (mul_le_of_le_one_left hB ht1)

private theorem cepsVarLo_nonneg (D : ℝ) : 0 ≤ cepsVarLo D := by
  unfold cepsVarLo; positivity

namespace CepsCanonDomain

variable {D θ v : ℝ}

/-- The same class constants with line scale `σ ≤ c₀`; `rmax` and `μ₀` scale by `σ/c₀`. -/
def shrink (dom : CepsCanonDomain D θ v) (σ : ℝ) (hσ : 0 < σ) (hσc : σ ≤ dom.c₀) :
    CepsCanonDomain D θ v :=
  have hc := dom.c₀_pos
  have ht0 : 0 ≤ σ / dom.c₀ := div_nonneg hσ.le hc.le
  have ht1 : σ / dom.c₀ ≤ 1 := div_le_one_of_le₀ hσc hc.le
  have htc : σ / dom.c₀ * dom.c₀ = σ := div_mul_cancel₀ σ hc.ne'
  have ht : 0 < σ / dom.c₀ := div_pos hσ hc
  have hv0 := cepsVarLo_nonneg D
  have hρA := dom.ρA_pos
  have hr := dom.rmax_pos
  have hμ := dom.μ₀_pos
  { ρA := dom.ρA
    ρB := dom.ρB
    gF := dom.gF
    g := dom.g
    c₀ := σ
    μ₀ := dom.μ₀ * (σ / dom.c₀)
    q₀ := (dom.rmax * (σ / dom.c₀)) ^ 2 / 2
    η := dom.η
    rmax := dom.rmax * (σ / dom.c₀)
    ρA_pos := dom.ρA_pos
    ρA_R := dom.ρA_R
    ρA_C3 := dom.ρA_C3
    ρA_one := dom.ρA_one
    ρA_v := dom.ρA_v
    ρA_ρB := dom.ρA_ρB
    ρB_r0 := dom.ρB_r0
    ρB_C3 := dom.ρB_C3
    gF_pos := dom.gF_pos
    gF_le := dom.gF_le
    gF_gap := dom.gF_gap
    g_pos := dom.g_pos
    g_gF := dom.g_gF
    g_B := dom.g_B
    c₀_pos := hσ
    c₀_g := by have := dom.c₀_g; have := dom.c₀_pos; nlinarith [mul_pos hρA dom.g_pos]
    c₀_W := by
      have := scale_le_aux dom.c₀_W dom.gF_pos.le ht0 ht1
      calc 8 * σ * cepsShiftConst D θ = 8 * (σ / dom.c₀ * dom.c₀) * cepsShiftConst D θ := by
            rw [htc]
        _ = σ / dom.c₀ * (8 * dom.c₀ * cepsShiftConst D θ) := by ring
        _ ≤ dom.gF := this
    η_pos := dom.η_pos
    η_le := dom.η_le
    rmax_pos := mul_pos hr ht
    rmax_r1 := by
      have := scale_le_aux dom.rmax_r1 (by linarith [dom.rmax_r1]) ht0 ht1; linarith
    rmax_c₀ := by
      have := mul_le_mul_of_nonneg_left dom.rmax_c₀ ht0
      calc 8 * cepsChartK D * (dom.rmax * (σ / dom.c₀)) =
            σ / dom.c₀ * (8 * cepsChartK D * dom.rmax) := by ring
        _ ≤ σ / dom.c₀ * dom.c₀ := this
        _ = σ := htc
    rmax_A1 := by
      have := scale_le_aux dom.rmax_A1 (by linarith [dom.rmax_A1]) ht0 ht1; linarith
    rmax_A1' := by
      have := scale_le_aux dom.rmax_A1' hρA.le ht0 ht1; linarith
    rmax_A2 := by
      have := scale_le_aux dom.rmax_A2 (mul_nonneg hρA.le hv0) ht0 ht1; linarith
    rmax_A3 := by
      have := scale_le_aux dom.rmax_A3 hv0 ht0 ht1; linarith
    rmax_one := by
      have := scale_le_aux dom.rmax_one zero_le_one ht0 ht1; linarith
    rmax_B := by
      have := scale_le_aux dom.rmax_B (by linarith [dom.rmax_B]) ht0 ht1; linarith
    rmax_C := by
      have := scale_le_aux dom.rmax_C (by linarith [dom.rmax_C]) ht0 ht1; linarith
    μ₀_pos := mul_pos hμ ht
    μ₀_r := by
      have := mul_le_mul_of_nonneg_left dom.μ₀_r ht0
      calc 4 * (v + 1) * (dom.μ₀ * (σ / dom.c₀)) = σ / dom.c₀ * (4 * (v + 1) * dom.μ₀) := by
            ring
        _ ≤ σ / dom.c₀ * (cepsVarLo D * dom.rmax) := this
        _ = cepsVarLo D * (dom.rmax * (σ / dom.c₀)) := by ring
    μ₀_c₀ := by
      have := mul_le_mul_of_nonneg_left dom.μ₀_c₀ ht0
      calc 16 * (dom.μ₀ * (σ / dom.c₀)) = σ / dom.c₀ * (16 * dom.μ₀) := by ring
        _ ≤ σ / dom.c₀ * (cepsVarLo D * dom.c₀) := this
        _ = cepsVarLo D * (σ / dom.c₀ * dom.c₀) := by ring
        _ = cepsVarLo D * σ := by rw [htc]
    μ₀_B := by
      have := scale_le_aux dom.μ₀_B (mul_nonneg hv0 (sq_nonneg _)) ht0 ht1; linarith
    μ₀_C := by
      have := scale_le_aux dom.μ₀_C (by linarith [dom.μ₀_C]) ht0 ht1; linarith
    μ₀_chart := by
      have := scale_le_aux dom.μ₀_chart (by linarith [dom.μ₀_chart]) ht0 ht1; linarith
    q₀_def := rfl }

variable (dom : CepsCanonDomain D θ v) (σ : ℝ) (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

@[simp] theorem shrink_c₀ : (dom.shrink σ hσ hσc).c₀ = σ := rfl

@[simp] theorem shrink_g : (dom.shrink σ hσ hσc).g = dom.g := rfl

@[simp] theorem shrink_ρA : (dom.shrink σ hσ hσc).ρA = dom.ρA := rfl

theorem shrink_d₀ : (dom.shrink σ hσ hσc).d₀ = dom.d₀ := rfl

theorem shrink_CF : (dom.shrink σ hσ hσc).CF = dom.CF := rfl

end CepsCanonDomain

/-! ### The origin `(μ, q) = (0, 0)` -/

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

section Origin

variable (hW : WienerHopf.IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem cepsMorseMin_at_zero : cepsMorseMin D θ ρW 0 = 0 := by
  rw [cepsMorseMin, cepsCgfShift, cepsMorseCenter_at_zero hW hθ hD, cepsCgf_zero hW, mul_zero,
    add_zero]

theorem cepsRootR_origin : cepsRootR D θ ρW 0 0 = 0 := by
  have h := cepsRootR_sq D θ ρW 0 0
  rw [cepsMorseMin_at_zero hW hθ hD, sub_zero] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h

theorem cepsRootPlus_origin : cepsRootPlus D θ ρW 0 0 = 0 := by
  rw [cepsRootPlus, cepsRootR_origin hW hθ hD,
    cepsMorseRoot_zero hW hθ hD (by simpa using cepsChartMu_pos hD hθ),
    cepsMorseCenter_at_zero hW hθ hD]

theorem cepsRootMinus_origin : cepsRootMinus D θ ρW 0 0 = 0 := by
  rw [cepsRootMinus, cepsRootR_origin hW hθ hD, neg_zero,
    cepsMorseRoot_zero hW hθ hD (by simpa using cepsChartMu_pos hD hθ),
    cepsMorseCenter_at_zero hW hθ hD]

/-- At the origin both roots vanish: `D₀(s; 0, 0) = s²`. -/
theorem cepsQuad_origin (s : ℂ) : cepsQuad D θ ρW 0 0 s = s ^ 2 := by
  rw [cepsQuad, cepsRootPlus_origin hW hθ hD, cepsRootMinus_origin hW hθ hD]; ring

/-- At the origin (with `γ = 1`, as in `canonL`) the canonical `F` is the root-free quotient
`cepsJetF s M₀(s) = (1 - M₀(s))(s² - 1)/s²`. -/
theorem cepsF_origin (s : ℂ) :
    cepsF D θ ρW ((1 : ℝ) : ℂ) 0 0 s = cepsJetF s (WienerHopf.stepTransform ρW s) := by
  rw [cepsF, cepsQuad_origin hW hθ hD, cepsD, cepsJetF, neg_zero, Complex.exp_zero, zero_mul,
    Complex.exp_zero, one_mul, one_mul, Complex.ofReal_one, one_pow]

end Origin

/-! ### The band at the origin -/

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)
  (hW : WienerHopf.IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `Re F̃ ≥ d₀` and `‖F̃‖ ≤ CF` for `F̃ = cepsJetF s M₀(s)` on the whole strip
`0 < Re s ≤ 2 c₀` (C-1 for the domain shrunk to `σ = Re s / 2`). -/
theorem re_cepsJetF_ge_of_band {s : ℂ} (h1 : 0 < s.re) (h2 : s.re ≤ 2 * dom.c₀) :
    dom.d₀ ≤ (cepsJetF s (WienerHopf.stepTransform ρW s)).re ∧
      ‖cepsJetF s (WienerHopf.stepTransform ρW s)‖ ≤ dom.CF := by
  have hσ : 0 < s.re / 2 := by linarith
  have hσc : s.re / 2 ≤ dom.c₀ := by linarith
  set dom' := dom.shrink (s.re / 2) hσ hσc with hdom'
  have hre : |s.re| = s.re := abs_of_pos h1
  have h := dom'.re_cepsF_ge hW hθ hD (γ := 1) (μ := 0) (q := 0) (ζ := s) (by norm_num) le_rfl
    (by rw [norm_zero]; exact dom'.μ₀_pos.le)
    (by rw [zero_im, abs_zero, zero_mul]; exact dom'.η_pos.le)
    (by rw [norm_zero]; exact dom'.q₀_pos.le)
    (by rw [hdom', shrink_c₀, hre]; linarith)
    (by rw [hdom', shrink_c₀, hre]; linarith)
  rwa [hdom', shrink_d₀, shrink_CF, cepsF_origin hW hθ hD] at h

/-- `‖1 - M₀(s)‖ ≥ min g (v₋ (Re s/2)²/32)` on the whole strip `0 < Re s ≤ 2 c₀`. -/
theorem norm_one_sub_stepTransform_ge_of_band {s : ℂ} (h1 : 0 < s.re)
    (h2 : s.re ≤ 2 * dom.c₀) :
    min dom.g (cepsVarLo D * (s.re / 2) ^ 2 / 32) ≤ ‖1 - WienerHopf.stepTransform ρW s‖ := by
  have hσ : 0 < s.re / 2 := by linarith
  have hσc : s.re / 2 ≤ dom.c₀ := by linarith
  set dom' := dom.shrink (s.re / 2) hσ hσc with hdom'
  have hre : |s.re| = s.re := abs_of_pos h1
  have h := dom'.norm_cepsD_ge hW hθ hD (μ := 0) (q := 0) (ζ := s)
    (by rw [norm_zero]; exact dom'.μ₀_pos.le)
    (by rw [zero_im, abs_zero, zero_mul]; exact dom'.η_pos.le)
    (by rw [norm_zero]; exact dom'.q₀_pos.le)
    (by rw [hdom', shrink_c₀, hre]; linarith)
    (by rw [hdom', shrink_c₀, hre]; linarith)
  rwa [hdom', shrink_g, shrink_c₀, cepsD, neg_zero, Complex.exp_zero, zero_mul, Complex.exp_zero,
    one_mul, one_mul] at h

end CepsCanonDomain

end PGM
