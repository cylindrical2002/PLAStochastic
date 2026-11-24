import PLAStochastic.Index.CEPS.Canonical.LineZones

/-!
# CEPS WP3, lemma C-1: zeros in the strip and separation on vertical lines

Blueprint §4.2, C-1. For a domain `dom : CepsCanonDomain D θ v` (whose existence is
`cepsCanonDomain_exists`), a step law in the class, real `γ ∈ [1/2, 1]` and admissible parameters
`‖μ‖ ≤ μ₀` (complex), `|Im μ| |Im ζ| ≤ η`, `‖q‖ ≤ q₀`:

* `CepsCanonDomain.cepsD_eq_zero_iff`: on the strip `|Re ζ| ≤ 2 c₀` the zeros of
  `d(·; μ, q)` are exactly `β₊, β₋`; near zero `d = (β₊ - ζ)(ζ - β₋) Q_A` with `Q_A` holomorphic
  and zero-free (`…cepsQuotA_ne_zero`, `…differentiableOn_cepsQuotA`), so the roots are counted
  with multiplicity;
* `CepsCanonDomain.re_cepsF_ge`: `Re F(ζ) ≥ d₀ = min (v₋/32) (g/4)` on `c₀ ≤ |Re ζ| ≤ 2 c₀`;
* `CepsCanonDomain.norm_cepsF_le`: `‖F‖ ≤ CF = max (2v) (8/ρA²)`;
* `CepsCanonDomain.norm_cepsD_ge`: `‖d‖ ≥ dd₀` on the lines;
* `CepsCanonDomain.norm_cepsF_sub_one_le`: `‖F - 1‖ ≤ (12/ρA²) ‖M₀(ζ)‖ + 3/(ρA ‖ζ‖)` for
  `‖ζ‖ ≥ ρA`;
* `CepsCanonDomain.norm_log_cepsF_le`: `‖log F(ζ)‖ ≤ CL (‖M₀(ζ)‖ + 1/‖ζ‖)` on the lines;
* `CepsCanonDomain.log_cepsF_eq_add`: for `‖ζ‖ ≥ ρA`, `log F = log (1 - A) + log R`;
* the line `L²` bound for `M₀` is `lintegral_norm_sq_stepTransform_le` (`Canonical.LineBounds`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf

namespace PGM

/-- `‖log z‖ ≤ |log d| + |log C| + π` when `d ≤ Re z` and `‖z‖ ≤ C`. -/
theorem norm_log_le_of_re_ge {z : ℂ} {d C : ℝ} (hd : 0 < d) (h1 : d ≤ z.re) (h2 : ‖z‖ ≤ C) :
    ‖Complex.log z‖ ≤ |Real.log d| + |Real.log C| + Real.pi := by
  have hz : 0 < ‖z‖ := lt_of_lt_of_le hd (h1.trans (re_le_norm z))
  have hdz : d ≤ ‖z‖ := h1.trans (re_le_norm z)
  have hre : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
  have him : (Complex.log z).im = Complex.arg z := Complex.log_im z
  have hl1 : Real.log d ≤ Real.log ‖z‖ := Real.log_le_log hd hdz
  have hl2 : Real.log ‖z‖ ≤ Real.log C := Real.log_le_log hz h2
  have habs : |Real.log ‖z‖| ≤ |Real.log d| + |Real.log C| := by
    rw [abs_le]; constructor
    · linarith [neg_abs_le (Real.log d), abs_nonneg (Real.log C)]
    · linarith [le_abs_self (Real.log C), abs_nonneg (Real.log d)]
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (|Real.log d| + |Real.log C|) + Real.pi := by
        rw [hre, him]
        exact add_le_add habs (Complex.abs_arg_le_pi z)

theorem re_mul_ge_aux {Q w : ℂ} {a b e f : ℝ} (ha : a ≤ Q.re) (hb : b ≤ w.re) (ha0 : 0 ≤ a)
    (hb0 : 0 ≤ b) (he : |Q.im| ≤ e) (hf : |w.im| ≤ f) (he0 : 0 ≤ e) :
    a * b - e * f ≤ (Q * w).re := by
  rw [mul_re]
  have e1 : a * b ≤ Q.re * w.re := mul_le_mul ha hb hb0 (ha0.trans ha)
  have e2 : Q.im * w.im ≤ e * f := by
    calc Q.im * w.im ≤ |Q.im * w.im| := le_abs_self _
      _ = |Q.im| * |w.im| := abs_mul _ _
      _ ≤ e * f := mul_le_mul he hf (abs_nonneg _) he0
  linarith

theorem zoneA_factor_bounds {γ c₀ ρ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {ζ : ℂ}
    (hc0 : 0 ≤ c₀) (hc : c₀ ≤ 1 / 1000) (h3 : |ζ.re| ≤ 2 * c₀) (hz : ‖ζ‖ ≤ ρ) (hρ1 : ρ ≤ 1) :
    1 / 8 ≤ ((γ : ℂ) ^ 2 - ζ ^ 2).re ∧ |((γ : ℂ) ^ 2 - ζ ^ 2).im| ≤ 4 * c₀ ∧
      ‖(γ : ℂ) ^ 2 - ζ ^ 2‖ ≤ 2 := by
  have hwre : ((γ : ℂ) ^ 2 - ζ ^ 2).re = γ ^ 2 - (ζ.re ^ 2 - ζ.im ^ 2) := by
    rw [sub_re, ← ofReal_pow, ofReal_re, sq ζ, mul_re]; ring
  have hwim : ((γ : ℂ) ^ 2 - ζ ^ 2).im = -(2 * ζ.re * ζ.im) := by
    rw [sub_im, ← ofReal_pow, ofReal_im, sq ζ, mul_im]; ring
  have hy : |ζ.im| ≤ 1 := (abs_im_le_norm ζ).trans (hz.trans hρ1)
  have hre2 : ζ.re ^ 2 ≤ 4 * c₀ ^ 2 := by
    rw [← sq_abs]
    calc |ζ.re| ^ 2 ≤ (2 * c₀) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      _ = 4 * c₀ ^ 2 := by ring
  have hγ2' : 1 / 4 ≤ γ ^ 2 := by
    calc (1 : ℝ) / 4 = (1 / 2) ^ 2 := by norm_num
      _ ≤ γ ^ 2 := pow_le_pow_left₀ (by norm_num) hγ1 2
  have hc2 : 4 * c₀ ^ 2 ≤ 1 / 8 := by
    have : c₀ ^ 2 ≤ (1 / 1000) ^ 2 := pow_le_pow_left₀ hc0 hc 2
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hwre]; linarith [sq_nonneg ζ.im]
  · rw [hwim, abs_neg, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * |ζ.re| * |ζ.im| ≤ 2 * (2 * c₀) * 1 := by gcongr
      _ = 4 * c₀ := by ring
  · have hz1 : ‖ζ‖ ^ 2 ≤ 1 := by
      calc ‖ζ‖ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hz.trans hρ1) 2
        _ = 1 := one_pow 2
    have hγ1' : γ ^ 2 ≤ 1 := by
      calc γ ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (by linarith) hγ2 2
        _ = 1 := one_pow 2
    calc ‖(γ : ℂ) ^ 2 - ζ ^ 2‖ ≤ ‖(γ : ℂ) ^ 2‖ + ‖ζ ^ 2‖ := norm_sub_le _ _
      _ = γ ^ 2 + ‖ζ‖ ^ 2 := by
          rw [norm_pow, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      _ ≤ 2 := by linarith

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

/-- `d₀ = min (v₋/32) (g/4)`. -/
def d₀ : ℝ := min (cepsVarLo D / 32) (dom.g / 4)

/-- `CF = max (2v) (8/ρA²)`. -/
def CF : ℝ := max (2 * v) (8 / dom.ρA ^ 2)

theorem d₀_pos (hD : 0 < D) : 0 < dom.d₀ :=
  lt_min (by have := cepsVarLo_pos hD; positivity) (by have := dom.g_pos; positivity)

section Line

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem cepsQuad_ne_zero {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : dom.c₀ / 2 ≤ ‖ζ‖) : cepsQuad D θ ρW μ q ζ ≠ 0 := by
  have hp := dom.norm_rootPlus_le hW hθ hD hμ hq
  have hm := dom.norm_rootMinus_le hW hθ hD hμ hq
  have hc := dom.c₀_pos
  rw [cepsQuad]
  refine mul_ne_zero ?_ ?_ <;> intro h <;> rw [sub_eq_zero] at h
  · rw [h] at hζ; linarith
  · rw [h] at hζ; linarith

theorem cepsQuotA_ne_zero {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀)
    (hζ : ‖ζ‖ ≤ dom.ρA) : cepsQuotA D θ ρW μ q ζ ≠ 0 := by
  intro h
  have := dom.norm_cepsQuotA_sub_le hW hθ hD hμ hq hζ
  rw [h, zero_sub, norm_neg, norm_div, norm_real, Real.norm_eq_abs,
    abs_of_pos (cepsStepVar_pos hW hθ hD)] at this
  have hv := cepsVarLo_le hW hθ hD
  have hv0 := cepsVarLo_pos hD
  norm_num at this
  linarith

theorem differentiableOn_cepsQuotA {μ q : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hq : ‖q‖ ≤ dom.q₀) :
    DifferentiableOn ℂ (cepsQuotA D θ ρW μ q) (ball 0 (cepsCgfRadius D θ)) := by
  have hH := differentiableOn_cepsRootQuot hW hθ hD (dom.μ_lt_chart hμ)
    (dom.norm_cepsRootR_lt hW hθ hD hμ hq)
  have hΦ := differentiableOn_cepsRootEq hW hθ hD (D := D) (θ := θ) μ q
  have hφ : Differentiable ℂ (dslope cexp 0) := by
    intro x
    have h := (differentiableOn_dslope (f := cexp) (s := univ) (c := 0) univ_mem).mpr
      Complex.differentiable_exp.differentiableOn
    exact (h x (mem_univ x)).differentiableAt univ_mem
  intro ζ hζ
  exact (hH ζ hζ).mul ((hφ _).comp_differentiableWithinAt ζ (hΦ ζ hζ))

/-- **C-1, zeros.** On the strip `|Re ζ| ≤ 2 c₀` the zeros of `d` are exactly `β±`. -/
theorem cepsD_eq_zero_iff {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    cepsD ρW μ q ζ = 0 ↔
      ζ = cepsRootPlus D θ ρW μ q ∨ ζ = cepsRootMinus D θ ρW μ q := by
  have hρA := dom.ρA_pos
  constructor
  · intro h0
    rcases lt_or_ge ‖ζ‖ dom.ρA with hz | hz
    · rw [dom.cepsD_eq_zoneA hW hθ hD hμ hq hz.le, neg_eq_zero] at h0
      rcases mul_eq_zero.mp h0 with h | h
      · rw [cepsQuad] at h
        rcases mul_eq_zero.mp h with h' | h'
        · exact Or.inl (sub_eq_zero.mp h')
        · exact Or.inr (sub_eq_zero.mp h')
      · exact absurd h (dom.cepsQuotA_ne_zero hW hθ hD hμ hq hz.le)
    · have hA := dom.norm_cepsA_offA hW hθ hD hμ hμη hq hz h3
      rw [cepsD_eq_one_sub_cepsA, sub_eq_zero] at h0
      rw [← h0, norm_one] at hA
      linarith [dom.g_pos]
  · intro h
    have hb : ‖ζ‖ ≤ dom.ρA := by
      rcases h with h | h <;> rw [h]
      · exact (dom.norm_rootPlus_le hW hθ hD hμ hq).trans (by linarith [dom.c₀_le, dom.c₀_pos])
      · exact (dom.norm_rootMinus_le hW hθ hD hμ hq).trans (by linarith [dom.c₀_le, dom.c₀_pos])
    rw [dom.cepsD_eq_zoneA hW hθ hD hμ hq hb, cepsQuad]
    rcases h with h | h <;> rw [h] <;> ring

/-- **C-1, line separation.** `Re F ≥ d₀` on the lines `c₀ ≤ |Re ζ| ≤ 2 c₀`. -/
theorem re_cepsF_ge {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀)
    (hμη : |μ.im| * |ζ.im| ≤ dom.η) (hq : ‖q‖ ≤ dom.q₀) (h2 : dom.c₀ ≤ |ζ.re|)
    (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    dom.d₀ ≤ (cepsF D θ ρW γ μ q ζ).re ∧ ‖cepsF D θ ρW γ μ q ζ‖ ≤ dom.CF := by
  have hρA := dom.ρA_pos
  have hρ1 := dom.ρA_one
  have hc := dom.c₀_le
  have hc0 := dom.c₀_pos
  have hζre : dom.c₀ ≤ ‖ζ‖ := h2.trans (abs_re_le_norm ζ)
  have hv := v_pos hW hθ hD
  have hvl := varLo_le_v hW hθ hD
  have hvl0 := cepsVarLo_pos hD
  have hvW := cepsVarLo_le hW hθ hD
  have hvWv := cepsStepVar_le hW
  rcases lt_or_ge ‖ζ‖ dom.ρA with hz | hz
  · -- zone A
    have hne := dom.cepsQuad_ne_zero hW hθ hD hμ hq (ζ := ζ) (by linarith)
    rw [dom.cepsF_eq_zoneA hW hθ hD hμ hq hz.le hne]
    have hQ := dom.norm_cepsQuotA_sub_le hW hθ hD hμ hq hz.le
    set Q := cepsQuotA D θ ρW μ q ζ
    have hc2 : ((cepsStepVar ρW : ℂ) / 2) = ((cepsStepVar ρW / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hc2] at hQ
    have hQre : 7 * cepsVarLo D / 16 ≤ Q.re := by
      have := (abs_re_le_norm _).trans hQ
      rw [sub_re, ofReal_re] at this
      linarith [neg_abs_le (Q.re - cepsStepVar ρW / 2)]
    have hQim : |Q.im| ≤ cepsVarLo D / 16 := by
      have := (abs_im_le_norm _).trans hQ
      rwa [sub_im, ofReal_im, sub_zero] at this
    have hQn : ‖Q‖ ≤ v := by
      calc ‖Q‖ = ‖(Q - ((cepsStepVar ρW / 2 : ℝ) : ℂ)) + ((cepsStepVar ρW / 2 : ℝ) : ℂ)‖ := by
            ring_nf
        _ ≤ cepsVarLo D / 16 + cepsStepVar ρW / 2 := by
            refine (norm_add_le _ _).trans (add_le_add hQ (le_of_eq ?_))
            rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
        _ ≤ v := by linarith
    obtain ⟨hwre_ge, hwim_le, hwn⟩ := zoneA_factor_bounds (ζ := ζ) hγ1 hγ2 hc0.le
      (by linarith [dom.ρA_one]) h3 hz.le hρ1
    constructor
    · have e1 := re_mul_ge_aux hQre hwre_ge (by positivity) (by norm_num) hQim hwim_le
        (by positivity)
      have e3 : cepsVarLo D / 16 * (4 * dom.c₀) ≤ cepsVarLo D / 4000 := by
        have : dom.c₀ ≤ 1 / 1000 := by linarith
        have : cepsVarLo D / 16 * (4 * dom.c₀) ≤ cepsVarLo D / 16 * (4 * (1 / 1000)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      have : dom.d₀ ≤ cepsVarLo D / 32 := min_le_left _ _
      linarith
    · rw [norm_mul]
      calc ‖Q‖ * ‖(γ : ℂ) ^ 2 - ζ ^ 2‖ ≤ v * 2 := mul_le_mul hQn hwn (norm_nonneg _) hv.le
        _ = 2 * v := by ring
        _ ≤ dom.CF := le_max_left _ _
  · -- zones B and C
    rw [cepsF_eq_mul_ratR, cepsD_eq_one_sub_cepsA]
    have hA := dom.norm_cepsA_offA hW hθ hD hμ hμη hq hz h3
    obtain ⟨hR1, hR2, hR3, -⟩ := dom.cepsRatR_bounds hW hθ hD hγ1 hγ2 hμ hq hz h3
    set A := cepsA ρW μ q ζ
    set R := cepsRatR D θ ρW (γ : ℂ) μ q ζ
    have hg := dom.g_pos
    have hg1 := dom.g_le_one
    have hdre : dom.g ≤ (1 - A).re := by
      rw [sub_re, one_re]; linarith [re_le_norm A]
    have hdim : |(1 - A).im| ≤ 1 := by
      rw [sub_im, one_im, zero_sub, abs_neg]; linarith [abs_im_le_norm A]
    have hκ : 34 * dom.c₀ / dom.ρA ≤ dom.g / 2 := by
      rw [div_le_iff₀ hρA]; have := dom.c₀_g; nlinarith
    constructor
    · rw [mul_re]
      have e1 : dom.g * R.re ≤ (1 - A).re * R.re :=
        mul_le_mul_of_nonneg_right hdre (by linarith)
      have e2 : (1 - A).im * R.im ≤ dom.g / 2 * R.re := by
        calc (1 - A).im * R.im ≤ |(1 - A).im * R.im| := le_abs_self _
          _ = |(1 - A).im| * |R.im| := abs_mul _ _
          _ ≤ 1 * (34 * dom.c₀ / dom.ρA * R.re) :=
              mul_le_mul hdim hR2 (abs_nonneg _) zero_le_one
          _ ≤ dom.g / 2 * R.re := by
              rw [one_mul]; exact mul_le_mul_of_nonneg_right hκ (by linarith)
      have : dom.d₀ ≤ dom.g / 4 := min_le_right _ _
      have e3 : dom.g / 2 * (1 / 2) ≤ dom.g / 2 * R.re :=
        mul_le_mul_of_nonneg_left hR1 (by linarith)
      linarith
    · rw [norm_mul]
      have hdn : ‖1 - A‖ ≤ 2 := by
        calc ‖1 - A‖ ≤ ‖(1 : ℂ)‖ + ‖A‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [norm_one]; linarith
      calc ‖1 - A‖ * ‖R‖ ≤ 2 * (4 / dom.ρA ^ 2) := mul_le_mul hdn hR3 (norm_nonneg _) (by norm_num)
        _ = 8 / dom.ρA ^ 2 := by ring
        _ ≤ dom.CF := le_max_right _ _

/-- `‖F - 1‖ ≤ (12/ρA²) ‖M₀(ζ)‖ + 3/(ρA ‖ζ‖)` off the root zone. -/
theorem norm_cepsF_sub_one_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η) (hq : ‖q‖ ≤ dom.q₀)
    (hz : dom.ρA ≤ ‖ζ‖) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖cepsF D θ ρW γ μ q ζ - 1‖ ≤
      12 / dom.ρA ^ 2 * ‖stepTransform ρW ζ‖ + 3 / (dom.ρA * ‖ζ‖) := by
  rw [cepsF_eq_mul_ratR, cepsD_eq_one_sub_cepsA]
  obtain ⟨-, -, hR3, hR4⟩ := dom.cepsRatR_bounds hW hθ hD hγ1 hγ2 hμ hq hz h3
  have hA3 := dom.norm_cepsA_le_three_mul (ρW := ρW) hμ hμη hq h3
  set A := cepsA ρW μ q ζ
  set R := cepsRatR D θ ρW (γ : ℂ) μ q ζ
  have e : (1 - A) * R - 1 = (R - 1) - A * R := by ring
  rw [e]
  calc ‖(R - 1) - A * R‖ ≤ ‖R - 1‖ + ‖A‖ * ‖R‖ := by
        refine (norm_sub_le _ _).trans ?_; rw [norm_mul]
    _ ≤ 3 / (dom.ρA * ‖ζ‖) + (3 * ‖stepTransform ρW ζ‖) * (4 / dom.ρA ^ 2) := by
        gcongr
    _ = 12 / dom.ρA ^ 2 * ‖stepTransform ρW ζ‖ + 3 / (dom.ρA * ‖ζ‖) := by ring

/-- `‖d‖ ≥ dd₀ = min (g) (v₋ c₀²/32)` on the lines. -/
theorem norm_cepsD_ge {μ q ζ : ℂ} (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η)
    (hq : ‖q‖ ≤ dom.q₀) (h2 : dom.c₀ ≤ |ζ.re|) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    min dom.g (cepsVarLo D * dom.c₀ ^ 2 / 32) ≤ ‖cepsD ρW μ q ζ‖ := by
  have hζre : dom.c₀ ≤ ‖ζ‖ := h2.trans (abs_re_le_norm ζ)
  rcases lt_or_ge ‖ζ‖ dom.ρA with hz | hz
  · rw [dom.cepsD_eq_zoneA hW hθ hD hμ hq hz.le, norm_neg, norm_mul, cepsQuad, norm_mul]
    have hp := dom.norm_rootPlus_le hW hθ hD hμ hq
    have hm := dom.norm_rootMinus_le hW hθ hD hμ hq
    have h1 : 3 * dom.c₀ / 4 ≤ ‖ζ - cepsRootPlus D θ ρW μ q‖ := by
      have := norm_sub_norm_le ζ (cepsRootPlus D θ ρW μ q); linarith
    have h1' : 3 * dom.c₀ / 4 ≤ ‖ζ - cepsRootMinus D θ ρW μ q‖ := by
      have := norm_sub_norm_le ζ (cepsRootMinus D θ ρW μ q); linarith
    have hQ := dom.norm_cepsQuotA_sub_le hW hθ hD hμ hq hz.le
    have hQn : cepsVarLo D / 4 ≤ ‖cepsQuotA D θ ρW μ q ζ‖ := by
      have := norm_sub_norm_le ((cepsStepVar ρW : ℂ) / 2) (cepsQuotA D θ ρW μ q ζ)
      rw [norm_sub_rev] at this
      have hc : ‖(cepsStepVar ρW : ℂ) / 2‖ = cepsStepVar ρW / 2 := by
        rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos (cepsStepVar_pos hW hθ hD)]; simp
      rw [hc] at this
      have := cepsVarLo_le hW hθ hD
      have := cepsVarLo_pos hD
      linarith
    have hc0 := dom.c₀_pos
    have hv0 := cepsVarLo_pos hD
    refine (min_le_right _ _).trans ?_
    calc cepsVarLo D * dom.c₀ ^ 2 / 32 ≤ (3 * dom.c₀ / 4) * (3 * dom.c₀ / 4) * (cepsVarLo D / 4) := by
          nlinarith [sq_nonneg dom.c₀]
      _ ≤ _ := by gcongr
  · have hA := dom.norm_cepsA_offA hW hθ hD hμ hμη hq hz h3
    rw [cepsD_eq_one_sub_cepsA]
    refine (min_le_left _ _).trans ?_
    have := norm_sub_norm_le (1 : ℂ) (cepsA ρW μ q ζ)
    rw [norm_one] at this
    linarith

/-- Off the root zone, `log F = log (1 - A) + log R` (both factors in the right half-plane). -/
theorem log_cepsF_eq_add {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η) (hq : ‖q‖ ≤ dom.q₀)
    (hz : dom.ρA ≤ ‖ζ‖) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    Complex.log (cepsF D θ ρW γ μ q ζ) =
      Complex.log (1 - cepsA ρW μ q ζ) + Complex.log (cepsRatR D θ ρW γ μ q ζ) := by
  rw [cepsF_eq_mul_ratR, cepsD_eq_one_sub_cepsA]
  have hA := dom.norm_cepsA_offA hW hθ hD hμ hμη hq hz h3
  obtain ⟨hR1, -, -, -⟩ := dom.cepsRatR_bounds hW hθ hD hγ1 hγ2 hμ hq hz h3
  have hg := dom.g_pos
  have hdre : 0 < (1 - cepsA ρW μ q ζ).re := by
    rw [sub_re, one_re]; linarith [re_le_norm (cepsA ρW μ q ζ)]
  have hRre : 0 < (cepsRatR D θ ρW γ μ q ζ).re := by linarith
  have ha1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hdre)
  have ha2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hRre)
  have hne1 : (1 - cepsA ρW μ q ζ) ≠ 0 := by
    intro h; rw [h, zero_re] at hdre; linarith
  have hne2 : cepsRatR D θ ρW γ μ q ζ ≠ 0 := by
    intro h; rw [h, zero_re] at hRre; linarith
  refine Complex.log_mul hne1 hne2 ⟨?_, ?_⟩
  · have := neg_abs_le (arg (1 - cepsA ρW μ q ζ))
    have := neg_abs_le (arg (cepsRatR D θ ρW γ μ q ζ))
    linarith
  · have := le_abs_self (arg (1 - cepsA ρW μ q ζ))
    have := le_abs_self (arg (cepsRatR D θ ρW γ μ q ζ))
    linarith [Real.pi_pos]

/-- The class constant `L∞ = |log d₀| + |log CF| + π`. -/
def Linf : ℝ := |Real.log dom.d₀| + |Real.log dom.CF| + Real.pi

/-- `CL = max (3/2) (2 L∞) · max (12/ρA²) (3/ρA) + L∞ ρA`. -/
def CL : ℝ := max (3 / 2) (2 * dom.Linf) * max (12 / dom.ρA ^ 2) (3 / dom.ρA) + dom.Linf * dom.ρA

/-- **C-1, logarithm bound.** On the lines, `‖log F(ζ)‖ ≤ CL (‖M₀(ζ)‖ + 1/‖ζ‖)`. -/
theorem norm_log_cepsF_le {γ : ℝ} (hγ1 : 1 / 2 ≤ γ) (hγ2 : γ ≤ 1) {μ q ζ : ℂ}
    (hμ : ‖μ‖ ≤ dom.μ₀) (hμη : |μ.im| * |ζ.im| ≤ dom.η) (hq : ‖q‖ ≤ dom.q₀)
    (h2 : dom.c₀ ≤ |ζ.re|) (h3 : |ζ.re| ≤ 2 * dom.c₀) :
    ‖Complex.log (cepsF D θ ρW γ μ q ζ)‖ ≤
      dom.CL * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by
  obtain ⟨hre, hn⟩ := dom.re_cepsF_ge hW hθ hD hγ1 hγ2 hμ hμη hq h2 h3
  have hd0 := dom.d₀_pos hD
  have hL := norm_log_le_of_re_ge hd0 hre hn
  have hρA := dom.ρA_pos
  have hζ : dom.c₀ ≤ ‖ζ‖ := h2.trans (abs_re_le_norm ζ)
  have hζ0 : 0 < ‖ζ‖ := lt_of_lt_of_le dom.c₀_pos hζ
  have hLinf : 0 ≤ dom.Linf := by unfold Linf; positivity
  have hM := norm_nonneg (stepTransform ρW ζ)
  have hmax1 : 0 ≤ max (3 / 2 : ℝ) (2 * dom.Linf) := le_max_of_le_left (by norm_num)
  have hmax2 : 0 ≤ max (12 / dom.ρA ^ 2) (3 / dom.ρA) := le_max_of_le_left (by positivity)
  have hinv : 0 ≤ 1 / ‖ζ‖ := by positivity
  rcases lt_or_ge ‖ζ‖ dom.ρA with hz | hz
  · -- zone A: the bounded estimate suffices
    have h1 : dom.Linf ≤ dom.Linf * dom.ρA * (1 / ‖ζ‖) := by
      rw [mul_assoc, ← div_eq_mul_one_div]
      have : 1 ≤ dom.ρA / ‖ζ‖ := by rw [le_div_iff₀ hζ0]; linarith
      nlinarith
    calc ‖Complex.log (cepsF D θ ρW γ μ q ζ)‖ ≤ dom.Linf := hL
      _ ≤ dom.Linf * dom.ρA * (1 / ‖ζ‖) := h1
      _ ≤ dom.CL * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by
          have e : dom.CL * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) =
              max (3 / 2) (2 * dom.Linf) * max (12 / dom.ρA ^ 2) (3 / dom.ρA) *
                (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) + dom.Linf * dom.ρA * ‖stepTransform ρW ζ‖ +
                dom.Linf * dom.ρA * (1 / ‖ζ‖) := by unfold CL; ring
          have h0 : 0 ≤ max (3 / 2) (2 * dom.Linf) * max (12 / dom.ρA ^ 2) (3 / dom.ρA) *
            (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by positivity
          have h0' : 0 ≤ dom.Linf * dom.ρA * ‖stepTransform ρW ζ‖ := by positivity
          linarith
  · have hF1 := dom.norm_cepsF_sub_one_le hW hθ hD hγ1 hγ2 hμ hμη hq hz h3
    set E := ‖cepsF D θ ρW γ μ q ζ - 1‖
    have hE : E ≤ max (12 / dom.ρA ^ 2) (3 / dom.ρA) * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by
      refine hF1.trans ?_
      have a1 : 12 / dom.ρA ^ 2 * ‖stepTransform ρW ζ‖ ≤
          max (12 / dom.ρA ^ 2) (3 / dom.ρA) * ‖stepTransform ρW ζ‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hM
      have a2 : 3 / (dom.ρA * ‖ζ‖) ≤ max (12 / dom.ρA ^ 2) (3 / dom.ρA) * (1 / ‖ζ‖) := by
        rw [show 3 / (dom.ρA * ‖ζ‖) = 3 / dom.ρA * (1 / ‖ζ‖) by field_simp]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hinv
      nlinarith
    have hlogE : ‖Complex.log (cepsF D θ ρW γ μ q ζ)‖ ≤ max (3 / 2) (2 * dom.Linf) * E := by
      rcases le_or_gt E (1 / 2) with hE2 | hE2
      · have := Complex.norm_log_one_add_half_le_self (z := cepsF D θ ρW γ μ q ζ - 1) hE2
        rw [add_sub_cancel] at this
        exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
      · calc ‖Complex.log (cepsF D θ ρW γ μ q ζ)‖ ≤ dom.Linf := hL
          _ ≤ 2 * dom.Linf * E := by nlinarith
          _ ≤ max (3 / 2) (2 * dom.Linf) * E :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    calc ‖Complex.log (cepsF D θ ρW γ μ q ζ)‖ ≤ max (3 / 2) (2 * dom.Linf) * E := hlogE
      _ ≤ max (3 / 2) (2 * dom.Linf) *
          (max (12 / dom.ρA ^ 2) (3 / dom.ρA) * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖)) :=
          mul_le_mul_of_nonneg_left hE hmax1
      _ ≤ dom.CL * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by
          have e : dom.CL * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) =
              max (3 / 2) (2 * dom.Linf) *
                (max (12 / dom.ρA ^ 2) (3 / dom.ρA) * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖)) +
                dom.Linf * dom.ρA * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by unfold CL; ring
          have : 0 ≤ dom.Linf * dom.ρA * (‖stepTransform ρW ζ‖ + 1 / ‖ζ‖) := by positivity
          linarith

end Line

end CepsCanonDomain

end PGM
