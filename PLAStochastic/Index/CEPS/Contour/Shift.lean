import PLAStochastic.Index.CEPS.Canonical.Factor
import PLAStochastic.Index.CEPS.Jets.Shrink

/-!
# X9: the canonical factor on smaller vertical lines

`CepsCanonDomain.shrink dom σ` (X8, `Jets.Shrink`) keeps the class constants of `dom` and moves the
line scale to `σ ∈ (0, c₀]`; the drift and discount radii shrink to `μ₀ σ/c₀` and
`q₀' = (rmax σ/c₀)²/2`, while `d₀`, `CF`, `CL` and the admissible imaginary drift are unchanged.

* `re_cepsF_ge_of_shrink`, `norm_log_cepsF_le_of_shrink`: for `(μ, q)` in the range of
  `dom.shrink σ`, C-1 holds on the whole strip `σ ≤ |Re s| ≤ 2 c₀` with the constants of `dom`;
  `norm_roots_le_of_shrink`: both roots lie in `‖ζ‖ ≤ σ/4`, strictly left of `Re s = σ`.
* `cepsCanonL_eq_of_abscissa_shrink` (**abscissa independence**): for such `(μ, q)` (real `μ`) the
  line integral defining `L` is the same on every line `Re s = c`, `σ ≤ c ≤ 2 c₀`, for
  `Re ζ < c`. Proof: WP3's rectangle argument `cepsCanonL_eq_of_abscissa` on the domain shrunk to
  `min a c₀` moves a line from `a` to any `b ≤ 2a`; dyadic induction connects all lines.
* `cepsCanonL_eq_canonL_of_shrink`, `shrink_canonL_eq`: the value is `dom.canonL`.
* `contour dom η`: the domain shrunk to the abscissa `min c₀ (η/2)`, so that
  `2 (contour η).c₀ ≤ η` (`two_contour_c₀_le`); `contour_canonL_eq`.
-/

noncomputable section

open MeasureTheory Set Complex
open PGM.WienerHopf

namespace PGM

namespace CepsCanonDomain

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ} (dom : CepsCanonDomain D θ v)

/-! ### Fields of the shrunk domain -/

section ShrinkFields

variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

theorem shrink_μ₀ : (dom.shrink σ hσ hσc).μ₀ = dom.μ₀ * (σ / dom.c₀) := rfl

theorem shrink_rmax : (dom.shrink σ hσ hσc).rmax = dom.rmax * (σ / dom.c₀) := rfl

theorem shrink_q₀ : (dom.shrink σ hσ hσc).q₀ = (dom.rmax * (σ / dom.c₀)) ^ 2 / 2 := rfl

theorem shrink_η : (dom.shrink σ hσ hσc).η = dom.η := rfl

theorem shrink_CL : (dom.shrink σ hσ hσc).CL = dom.CL := rfl

theorem shrink_μ₀_mono {σ' : ℝ} (hσ' : 0 < σ') (hσc' : σ' ≤ dom.c₀) (h : σ ≤ σ') :
    (dom.shrink σ hσ hσc).μ₀ ≤ (dom.shrink σ' hσ' hσc').μ₀ := by
  rw [shrink_μ₀, shrink_μ₀]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h dom.c₀_pos.le) dom.μ₀_pos.le

theorem shrink_q₀_mono {σ' : ℝ} (hσ' : 0 < σ') (hσc' : σ' ≤ dom.c₀) (h : σ ≤ σ') :
    (dom.shrink σ hσ hσc).q₀ ≤ (dom.shrink σ' hσ' hσc').q₀ := by
  rw [shrink_q₀, shrink_q₀]
  have hc := dom.c₀_pos
  have hr := dom.rmax_pos
  have h1 : dom.rmax * (σ / dom.c₀) ≤ dom.rmax * (σ' / dom.c₀) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hc.le) hr.le
  have h0 : 0 ≤ dom.rmax * (σ / dom.c₀) := by positivity
  have := pow_le_pow_left₀ h0 h1 2
  linarith

theorem shrink_μ₀_le : (dom.shrink σ hσ hσc).μ₀ ≤ dom.μ₀ := by
  rw [shrink_μ₀]
  exact mul_le_of_le_one_right dom.μ₀_pos.le (div_le_one_of_le₀ hσc dom.c₀_pos.le)

theorem shrink_q₀_le : (dom.shrink σ hσ hσc).q₀ ≤ dom.q₀ := by
  rw [shrink_q₀, dom.q₀_def]
  have hc := dom.c₀_pos
  have hr := dom.rmax_pos
  have h1 : dom.rmax * (σ / dom.c₀) ≤ dom.rmax :=
    mul_le_of_le_one_right hr.le (div_le_one_of_le₀ hσc hc.le)
  have h0 : 0 ≤ dom.rmax * (σ / dom.c₀) := by positivity
  have := pow_le_pow_left₀ h0 h1 2
  linarith

end ShrinkFields

/-! ### C-1 on the whole strip `σ ≤ |Re s| ≤ 2 c₀` -/

section Strip

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

/-- **C-1 on the strip.** For `(μ, q)` in the range of `dom.shrink σ`, `Re F ≥ d₀` and
`‖F‖ ≤ CF` on every line `σ ≤ |Re s| ≤ 2 c₀`, with the constants of `dom`. -/
theorem re_cepsF_ge_of_shrink {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q s : ℂ}
    (hμ : ‖μ‖ ≤ (dom.shrink σ hσ hσc).μ₀) (hμη : |μ.im| * |s.im| ≤ dom.η)
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (h1 : σ ≤ |s.re|) (h2 : |s.re| ≤ 2 * dom.c₀) :
    dom.d₀ ≤ (cepsF D θ ρW γ μ q s).re ∧ ‖cepsF D θ ρW γ μ q s‖ ≤ dom.CF := by
  set a := max σ (|s.re| / 2) with ha
  have hσa : σ ≤ a := le_max_left _ _
  have ha0 : 0 < a := lt_of_lt_of_le hσ hσa
  have hac : a ≤ dom.c₀ := max_le hσc (by linarith)
  have h := (dom.shrink a ha0 hac).re_cepsF_ge hW hθ hD hγ1 hγ2
    (hμ.trans (dom.shrink_μ₀_mono hσ hσc ha0 hac hσa)) (by rwa [shrink_η])
    (hq.trans (dom.shrink_q₀_mono hσ hσc ha0 hac hσa))
    (by rw [shrink_c₀]; exact max_le h1 (by linarith [abs_nonneg s.re]))
    (by rw [shrink_c₀]; have := le_max_right σ (|s.re| / 2); linarith)
  rwa [shrink_d₀, shrink_CF] at h

/-- **C-1 logarithm bound on the strip.** -/
theorem norm_log_cepsF_le_of_shrink {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q s : ℂ}
    (hμ : ‖μ‖ ≤ (dom.shrink σ hσ hσc).μ₀) (hμη : |μ.im| * |s.im| ≤ dom.η)
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (h1 : σ ≤ |s.re|) (h2 : |s.re| ≤ 2 * dom.c₀) :
    ‖Complex.log (cepsF D θ ρW γ μ q s)‖ ≤ dom.CL * (‖stepTransform ρW s‖ + 1 / ‖s‖) := by
  set a := max σ (|s.re| / 2) with ha
  have hσa : σ ≤ a := le_max_left _ _
  have ha0 : 0 < a := lt_of_lt_of_le hσ hσa
  have hac : a ≤ dom.c₀ := max_le hσc (by linarith)
  have h := (dom.shrink a ha0 hac).norm_log_cepsF_le hW hθ hD hγ1 hγ2
    (hμ.trans (dom.shrink_μ₀_mono hσ hσc ha0 hac hσa)) (by rwa [shrink_η])
    (hq.trans (dom.shrink_q₀_mono hσ hσc ha0 hac hσa))
    (by rw [shrink_c₀]; exact max_le h1 (by linarith [abs_nonneg s.re]))
    (by rw [shrink_c₀]; have := le_max_right σ (|s.re| / 2); linarith)
  rwa [shrink_CL] at h

/-- Both roots lie strictly to the left of the line `Re s = σ`: `‖β±‖ ≤ σ/4`. -/
theorem norm_roots_le_of_shrink {μ q : ℂ} (hμ : ‖μ‖ ≤ (dom.shrink σ hσ hσc).μ₀)
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) :
    ‖cepsRootPlus D θ ρW μ q‖ ≤ σ / 4 ∧ ‖cepsRootMinus D θ ρW μ q‖ ≤ σ / 4 :=
  ⟨(dom.shrink σ hσ hσc).norm_rootPlus_le hW hθ hD hμ hq,
    (dom.shrink σ hσ hσc).norm_rootMinus_le hW hθ hD hμ hq⟩

/-! ### Abscissa independence -/

/-- One step: from the line `a` to a line `b ∈ [a, 2a]`, `σ ≤ a`, `b ≤ 2 c₀`. -/
theorem cepsCanonL_eq_of_abscissa_step {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {a b : ℝ}
    (ha : σ ≤ a) (hab : a ≤ b) (hb : b ≤ 2 * a) (hb' : b ≤ 2 * dom.c₀) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ (dom.shrink σ hσ hσc).μ₀) (hμη : μ.im = 0)
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < a) :
    cepsCanonL D θ ρW γ a μ q ζ = cepsCanonL D θ ρW γ b μ q ζ := by
  set a' := min a dom.c₀ with ha'
  have ha'σ : σ ≤ a' := le_min ha hσc
  have ha'0 : 0 < a' := lt_of_lt_of_le hσ ha'σ
  have ha'c : a' ≤ dom.c₀ := min_le_right _ _
  have ha'a : a' ≤ a := min_le_left _ _
  have hb2 : b ≤ 2 * a' := by
    rcases le_total a dom.c₀ with h | h
    · rw [ha', min_eq_left h]; exact hb
    · rw [ha', min_eq_right h]; exact hb'
  exact (dom.shrink a' ha'0 ha'c).cepsCanonL_eq_of_abscissa hW hθ hD hγ1 hγ2
    (by rw [shrink_c₀]; exact ha'a) hab (by rw [shrink_c₀]; exact hb2)
    (hμ.trans (dom.shrink_μ₀_mono hσ hσc ha'0 ha'c ha'σ)) hμη
    (hq.trans (dom.shrink_q₀_mono hσ hσc ha'0 ha'c ha'σ)) hζ

/-- **Abscissa independence (X9, item 1).** For `(μ, q)` in the range of `dom.shrink σ` (real
`μ`), the contour integrals on the lines `Re s = c` and `Re s = c'`, `σ ≤ c ≤ c' ≤ 2 c₀`, agree
for `Re ζ < c`. -/
theorem cepsCanonL_eq_of_abscissa_shrink {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {c c' : ℝ}
    (hc : σ ≤ c) (hcc : c ≤ c') (hc' : c' ≤ 2 * dom.c₀) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ (dom.shrink σ hσ hσc).μ₀) (hμη : μ.im = 0)
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < c) :
    cepsCanonL D θ ρW γ c μ q ζ = cepsCanonL D θ ρW γ c' μ q ζ := by
  have hc0 : 0 < c := lt_of_lt_of_le hσ hc
  have key : ∀ n : ℕ, ∀ x : ℝ, c ≤ x → x ≤ 2 * dom.c₀ → x ≤ 2 ^ n * c →
      cepsCanonL D θ ρW γ c μ q ζ = cepsCanonL D θ ρW γ x μ q ζ := by
    intro n
    induction n with
    | zero =>
      intro x hx1 _ hx3
      rw [pow_zero, one_mul] at hx3
      rw [le_antisymm hx3 hx1]
    | succ n ih =>
      intro x hx1 hx2 hx3
      set a := max c (x / 2) with ha
      have ha1 : c ≤ a := le_max_left _ _
      have hax : a ≤ x := max_le hx1 (by linarith)
      have hxa : x ≤ 2 * a := by have := le_max_right c (x / 2); linarith
      have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have ha3 : a ≤ 2 ^ n * c := by
        refine max_le (le_mul_of_one_le_left hc0.le h2n) ?_
        rw [pow_succ] at hx3; linarith
      rw [ih a ha1 (hax.trans hx2) ha3]
      exact dom.cepsCanonL_eq_of_abscissa_step hW hθ hD hσ hσc hγ1 hγ2 (hc.trans ha1) hax hxa hx2
        hμ hμη hq (lt_of_lt_of_le hζ ha1)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (c' / c) (by norm_num : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hc0] at hn
  exact key n c' hcc hc' hn.le

/-- The line `Re s = c ∈ [σ, 2c₀]` gives `dom.canonL` for `Re ζ < min c c₀`. -/
theorem cepsCanonL_eq_canonL_of_shrink {c : ℝ} (hc : σ ≤ c) (hc' : c ≤ 2 * dom.c₀) {μ : ℝ}
    (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀) {q ζ : ℂ} (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀)
    (hζ : ζ.re < min c dom.c₀) :
    cepsCanonL D θ ρW 1 c μ q ζ = dom.canonL ρW μ q ζ := by
  have hμ' : ‖(μ : ℂ)‖ ≤ (dom.shrink σ hσ hσc).μ₀ := by rwa [norm_real, Real.norm_eq_abs]
  have hμi : (μ : ℂ).im = 0 := ofReal_im μ
  have hc0 := dom.c₀_pos
  unfold canonL
  rcases le_total c dom.c₀ with h | h
  · rw [min_eq_left h] at hζ
    exact dom.cepsCanonL_eq_of_abscissa_shrink hW hθ hD hσ hσc (γ := 1) (by norm_num) le_rfl
      hc h (by linarith) hμ' hμi hq hζ
  · rw [min_eq_right h] at hζ
    exact (dom.cepsCanonL_eq_of_abscissa_shrink hW hθ hD hσ hσc (γ := 1) (by norm_num) le_rfl
      hσc h hc' hμ' hμi hq hζ).symm

/-- The canonical factor of the shrunk domain is `dom.canonL` on its range. -/
theorem shrink_canonL_eq {μ : ℝ} (hμ : |μ| ≤ (dom.shrink σ hσ hσc).μ₀) {q ζ : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < σ) :
    (dom.shrink σ hσ hσc).canonL ρW μ q ζ = dom.canonL ρW μ q ζ := by
  have hc0 := dom.c₀_pos
  show cepsCanonL D θ ρW 1 σ μ q ζ = dom.canonL ρW μ q ζ
  exact dom.cepsCanonL_eq_canonL_of_shrink hW hθ hD hσ hσc le_rfl (by linarith) hμ hq
    (lt_min hζ (lt_of_lt_of_le hζ hσc))

end Strip

/-! ### The admissible abscissa for a Sobolev weight `η` -/

/-- The canonical domain moved to the abscissa `min c₀ (η/2)`. -/
def contour (η : ℝ) (hη : 0 < η) : CepsCanonDomain D θ v :=
  dom.shrink (min dom.c₀ (η / 2)) (lt_min dom.c₀_pos (half_pos hη)) (min_le_left _ _)

section Contour

variable {η : ℝ} (hη : 0 < η)

theorem contour_eq : dom.contour η hη =
    dom.shrink (min dom.c₀ (η / 2)) (lt_min dom.c₀_pos (half_pos hη)) (min_le_left _ _) := rfl

theorem contour_c₀ : (dom.contour η hη).c₀ = min dom.c₀ (η / 2) := rfl

theorem two_contour_c₀_le : 2 * (dom.contour η hη).c₀ ≤ η := by
  rw [contour_c₀]; have := min_le_right dom.c₀ (η / 2); linarith

theorem contour_c₀_le : (dom.contour η hη).c₀ ≤ dom.c₀ := min_le_left _ _

theorem contour_μ₀_le : (dom.contour η hη).μ₀ ≤ dom.μ₀ := dom.shrink_μ₀_le _ _

theorem contour_q₀_le : (dom.contour η hη).q₀ ≤ dom.q₀ := dom.shrink_q₀_le _ _

theorem contour_d₀ : (dom.contour η hη).d₀ = dom.d₀ := rfl

theorem contour_CF : (dom.contour η hη).CF = dom.CF := rfl

theorem contour_CL : (dom.contour η hη).CL = dom.CL := rfl

theorem contour_η : (dom.contour η hη).η = dom.η := rfl

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

/-- `L` on the line `Re s = min c₀ (η/2)` is `dom.canonL`. -/
theorem contour_canonL_eq {μ : ℝ} (hμ : |μ| ≤ (dom.contour η hη).μ₀) {q ζ : ℂ}
    (hq : ‖q‖ ≤ (dom.contour η hη).q₀) (hζ : ζ.re < (dom.contour η hη).c₀) :
    (dom.contour η hη).canonL ρW μ q ζ = dom.canonL ρW μ q ζ :=
  dom.shrink_canonL_eq hW hθ hD _ _ hμ hq hζ

end Contour

end CepsCanonDomain

end PGM
