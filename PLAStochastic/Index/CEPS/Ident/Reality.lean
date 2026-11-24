import PLAStochastic.Index.CEPS.Canonical.Main
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# CEPS WP4: real structure of the root chart and the location of the two roots

Blueprint §3.1 ("the roots cannot cross the imaginary axis"), needed for C-5. For a real drift
`μ` (`|μ| ≤ μ₀`):

* conjugation symmetry: `stepTransform_conj`, `cepsCgf_conj` and its first two derivatives,
  `conj_cepsMorseCenter` (`β*` is real), `conj_cepsMorseMin`, `re_cepsMorseMin_nonpos`
  (`Re m(μ) ≤ 0`, from `ψ_μ(0) = 0 = m + β*² k`), `cepsMorseG_conj`, `conj_cepsMorseRoot`
  (`Θ(r, μ)` is real for real `r`);
* real discount `0 < q ≤ q₀`: `CepsCanonDomain.rootPlus_real` / `rootMinus_real` — both roots
  are real and `β₋ < 0 < β₊` (the chart is increasing on the real axis and `ζ = 0` has chart
  value `±√(-m)` with `√(-m) < r₊ = √(q - m)`);
* `cepsD_ne_zero_of_re_eq_zero`: for `Re q > 0`, `d` has no zero on the imaginary axis;
* `CepsCanonDomain.re_rootPlus_pos`, `re_rootMinus_neg`: for `Re q > 0`, `Re β₊ > 0 > Re β₋`
  (continuity of `q ↦ β±` along the segment from `q₀` and the intermediate value theorem).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Complex Filter Topology
open PGM.WienerHopf
open scoped ComplexConjugate

namespace PGM

theorem stepTransform_conj (ρ : Measure ℝ) (z : ℂ) :
    stepTransform ρ (conj z) = conj (stepTransform ρ z) := by
  unfold stepTransform
  rw [← integral_conj]
  congr 1
  funext y
  rw [← Complex.exp_conj, map_mul, conj_ofReal]

/-- A function that commutes with conjugation near `z` has `f'(z̄) = conj f'(z)`. -/
theorem deriv_conj_of_eventually {f : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z, f (conj w) = conj (f w)) :
    deriv f (conj z) = conj (deriv f z) := by
  have h1 : (conj ∘ f ∘ conj) =ᶠ[𝓝 z] f := hf.mono fun w hw => by
    simp only [Function.comp_apply, hw, conj_conj]
  have h2 := h1.deriv_eq
  rw [deriv_conj_conj] at h2
  simp only [Function.comp_apply] at h2
  rw [← h2, conj_conj]

/-- `√(conj k) = conj √k` on the slit plane. -/
theorem sqrt_conj_of_mem_slitPlane {k : ℂ} (hk : k ∈ slitPlane) :
    Complex.sqrt (conj k) = conj (Complex.sqrt k) := by
  have hk' : conj k ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hk ⊢
    simpa using hk
  have h := cpow_conj (conj k) 2⁻¹ (mem_slitPlane_iff_arg.mp hk').1
  rw [conj_conj] at h
  have h2 : conj (2⁻¹ : ℂ) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [h2] at h
  unfold Complex.sqrt
  exact h

/-- `‖M(ζ)‖ ≤ 1` on the imaginary axis. -/
theorem norm_stepTransform_le_one_of_re_eq_zero (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    {ζ : ℂ} (hζ : ζ.re = 0) : ‖stepTransform ρ ζ‖ ≤ 1 := by
  unfold stepTransform
  calc ‖∫ y, cexp (ζ * y) ∂ρ‖ ≤ ∫ y, ‖cexp (ζ * y)‖ ∂ρ := norm_integral_le_integral_norm _
    _ = ∫ _y, (1 : ℝ) ∂ρ := by
        congr 1; funext y; rw [norm_cexp_mul_ofReal, hζ, zero_mul, Real.exp_zero]
    _ = 1 := by simp

/-- For `Re q > 0` and real `μ`, `d(ζ; μ, q) ≠ 0` on the imaginary axis. -/
theorem cepsD_ne_zero_of_re_eq_zero (ρW : Measure ℝ) [IsProbabilityMeasure ρW] (μ : ℝ)
    {q ζ : ℂ} (hq : 0 < q.re) (hζ : ζ.re = 0) : cepsD ρW μ q ζ ≠ 0 := by
  intro h0
  rw [cepsD, sub_eq_zero] at h0
  have hn : ‖cexp (-q) * cexp ((μ : ℂ) * ζ) * stepTransform ρW ζ‖ < 1 := by
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : ((μ : ℂ) * ζ).re = 0 := by rw [re_ofReal_mul, hζ, mul_zero]
    rw [h1, Real.exp_zero, mul_one, neg_re]
    have h2 := norm_stepTransform_le_one_of_re_eq_zero ρW hζ
    have h3 : Real.exp (-q.re) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    calc Real.exp (-q.re) * ‖stepTransform ρW ζ‖ ≤ Real.exp (-q.re) * 1 :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ < 1 := by rw [mul_one]; exact h3
  rw [← h0, norm_one] at hn
  exact lt_irrefl 1 hn

variable {ρW : Measure ℝ} {fW : ℝ → ℝ} {D θ v : ℝ}

section Conj

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

theorem cepsCgf_conj {ζ : ℂ} (hζ : ‖ζ‖ ≤ cepsCgfRadius D θ) :
    cepsCgf ρW (conj ζ) = conj (cepsCgf ρW ζ) := by
  have hM := stepTransform_mem_slitPlane hW hθ hD hζ
  rw [cepsCgf, cepsCgf, stepTransform_conj, log_conj _ (mem_slitPlane_iff_arg.mp hM).1]

theorem deriv_cepsCgf_conj {ζ : ℂ} (hζ : ‖ζ‖ < cepsCgfRadius D θ) :
    deriv (cepsCgf ρW) (conj ζ) = conj (deriv (cepsCgf ρW) ζ) := by
  refine deriv_conj_of_eventually ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hζ)] with w hw
  exact cepsCgf_conj hW hθ hD (mem_ball_zero_iff.mp hw).le

theorem deriv2_cepsCgf_conj {ζ : ℂ} (hζ : ‖ζ‖ < cepsCgfRadius D θ) :
    deriv (deriv (cepsCgf ρW)) (conj ζ) = conj (deriv (deriv (cepsCgf ρW)) ζ) := by
  refine deriv_conj_of_eventually ?_
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hζ)] with w hw
  exact deriv_cepsCgf_conj hW hθ hD (mem_ball_zero_iff.mp hw)

/-- For real `μ`, the centre `β*(μ)` is real. -/
theorem conj_cepsMorseCenter {μ : ℝ} (hμ : ‖(μ : ℂ)‖ < cepsChartMu D θ) :
    conj (cepsMorseCenter D θ ρW μ) = cepsMorseCenter D θ ρW μ := by
  have hyp := cepsCenter_hyp hW hθ hD
  have hw := norm_neg_lt_center hW hθ hD hμ
  obtain ⟨hmem, hval⟩ := hyp.paramInv_spec (mem_univ (0 : ℂ)) hw
  have hz := mem_ball_zero_iff.mp hmem
  have hR : cepsCenterRadius D θ ≤ cepsCgfRadius D θ / 2 := min_le_left _ _
  have hr0 := cepsCgfRadius_pos hD hθ
  have hc : conj (paramInv (fun _ z => deriv (cepsCgf ρW) z) (cepsCenterRadius D θ) 0 (-(μ : ℂ)))
      ∈ ball (0 : ℂ) (cepsCenterRadius D θ) := by
    rw [mem_ball_zero_iff, Complex.norm_conj]; exact hz
  have hval' : (fun _ z => deriv (cepsCgf ρW) z) (0 : ℂ)
      (conj (paramInv (fun _ z => deriv (cepsCgf ρW) z) (cepsCenterRadius D θ) 0 (-(μ : ℂ)))) =
        -(μ : ℂ) := by
    simp only at hval ⊢
    rw [deriv_cepsCgf_conj hW hθ hD (by linarith), hval, map_neg, conj_ofReal]
  have key := hyp.paramInv_eq (mem_univ (0 : ℂ)) hc hval'
  rw [cepsMorseCenter]
  exact key.symm

/-- For real `μ`, the minimum `m(μ)` is real. -/
theorem conj_cepsMorseMin {μ : ℝ} (hμ : ‖(μ : ℂ)‖ < cepsChartMu D θ) :
    conj (cepsMorseMin D θ ρW μ) = cepsMorseMin D θ ρW μ := by
  have hb := conj_cepsMorseCenter hW hθ hD hμ
  have hbn := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  rw [cepsMorseMin, cepsCgfShift, map_add, map_mul,
    ← cepsCgf_conj hW hθ hD (by linarith), hb, conj_ofReal]

/-- For real `μ`, `Re m(μ) ≤ 0`: `0 = ψ_μ(0) = m + β*² k(β*, -β*)` with `β*` real, `Re k > 0`. -/
theorem re_cepsMorseMin_nonpos {μ : ℝ} (hμ : ‖(μ : ℂ)‖ < cepsChartMu D θ) :
    (cepsMorseMin D θ ρW μ).re ≤ 0 := by
  set b := cepsMorseCenter D θ ρW μ with hbdef
  have hb := conj_cepsMorseCenter hW hθ hD hμ
  have hbn := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hR0 := cepsChartRadius_pos hD hθ
  have hr0 := cepsCgfRadius_pos hD hθ
  have h := cepsCgfShift_center_add hW hθ hD hμ (u := -b) (by rw [norm_neg]; linarith)
  rw [add_neg_cancel, cepsCgfShift, cepsCgf_zero hW, mul_zero, add_zero] at h
  have hk := cepsMorseK_re_pos hW hθ hD hbn (u := -b) (by rw [norm_neg]; linarith)
  have hbre : (b.re : ℂ) = b := conj_eq_iff_re.mp hb
  have hsq : (-b) ^ 2 = ((b.re ^ 2 : ℝ) : ℂ) := by
    rw [neg_sq]; conv_lhs => rw [← hbre]
    push_cast; ring
  have hm : cepsMorseMin D θ ρW μ = -((-b) ^ 2 * cepsMorseK ρW b (-b)) := by
    linear_combination -h
  rw [hm, neg_re, hsq, re_ofReal_mul]
  have := sq_nonneg b.re
  nlinarith

theorem cepsMorseK_conj {b u : ℂ} (hb : conj b = b) (hbu : ‖b‖ + ‖u‖ < cepsCgfRadius D θ) :
    cepsMorseK ρW b (conj u) = conj (cepsMorseK ρW b u) := by
  rw [cepsMorseK, cepsMorseK, hadamard2, hadamard2,
    intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    ← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have hseg : ‖b + t * u‖ < cepsCgfRadius D θ := by
    calc ‖b + t * u‖ ≤ ‖b‖ + ‖(t : ℂ)‖ * ‖u‖ := by rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖b‖ + 1 * ‖u‖ := by
          gcongr
          rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1.le]; exact ht.2
      _ < cepsCgfRadius D θ := by linarith
  rw [map_mul, conj_ofReal, ← deriv2_cepsCgf_conj hW hθ hD hseg, map_add, hb, map_mul,
    conj_ofReal]

/-- For real `μ`, the chart map commutes with conjugation. -/
theorem cepsMorseG_conj {μ : ℝ} (hμ : ‖(μ : ℂ)‖ < cepsChartMu D θ) {u : ℂ}
    (hu : ‖u‖ < 2 * cepsChartRadius D θ) :
    cepsMorseG D θ ρW μ (conj u) = conj (cepsMorseG D θ ρW μ u) := by
  have hb := conj_cepsMorseCenter hW hθ hD hμ
  have hbn := norm_cepsMorseCenter_lt hW hθ hD hμ
  have hR := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  rw [cepsMorseG, cepsMorseG, cepsMorseK_conj hW hθ hD hb (by linarith), map_mul,
    sqrt_conj_of_mem_slitPlane (cepsMorseK_mem_slitPlane hW hθ hD hbn hu)]

/-- For real `μ` and real `r`, the root chart `Θ(r, μ)` is real. -/
theorem conj_cepsMorseRoot {μ : ℝ} (hμ : ‖(μ : ℂ)‖ < cepsChartMu D θ) {r : ℝ}
    (hr : ‖(r : ℂ)‖ < cepsChartRho D θ) :
    conj (cepsMorseRoot D θ ρW μ r) = cepsMorseRoot D θ ρW μ r := by
  have hb := conj_cepsMorseCenter hW hθ hD hμ
  obtain ⟨hu, hg⟩ := cepsMorseRoot_sub_center hW hθ hD hμ hr
  set u := cepsMorseRoot D θ ρW μ r - cepsMorseCenter D θ ρW μ with hudef
  have hμ' : (μ : ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) := mem_ball_zero_iff.mpr hμ
  have hun : ‖u‖ < cepsChartRadius D θ := mem_ball_zero_iff.mp hu
  have hR0 := cepsChartRadius_pos hD hθ
  have hcu : conj u ∈ ball (0 : ℂ) (cepsChartRadius D θ) := by
    rw [mem_ball_zero_iff, Complex.norm_conj]; exact hun
  have hgc : cepsMorseG D θ ρW μ (conj u) = r := by
    rw [cepsMorseG_conj hW hθ hD hμ (by linarith), hg, conj_ofReal]
  have h1 := (cepsChart_hyp hW hθ hD).paramInv_eq hμ' hcu hgc
  have h2 := (cepsChart_hyp hW hθ hD).paramInv_eq hμ' hu hg
  have hreal : conj u = u := h1.symm.trans h2
  have hΘ : cepsMorseRoot D θ ρW μ r = cepsMorseCenter D θ ρW μ + u := by rw [hudef]; ring
  rw [hΘ, map_add, hb, hreal]

/-- Monotonicity of the chart on the real axis: for real chart points `u₁ ≤ u₂`,
`Re g(u₁) ≤ Re g(u₂)` (the chart derivative lies in the disc `B(a, a/2)`, `a > 0`). -/
theorem re_cepsMorseG_le {μ : ℝ} (hμ : ‖(μ : ℂ)‖ < cepsChartMu D θ) {u₁ u₂ : ℂ}
    (h₁ : ‖u₁‖ < cepsChartRadius D θ) (h₂ : ‖u₂‖ < cepsChartRadius D θ)
    (hr₁ : conj u₁ = u₁) (hr₂ : conj u₂ = u₂) (h12 : u₁.re ≤ u₂.re) :
    (cepsMorseG D θ ρW μ u₁).re ≤ (cepsMorseG D θ ρW μ u₂).re := by
  have hμ' : (μ : ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) := mem_ball_zero_iff.mpr hμ
  have key := (cepsChart_hyp hW hθ hD).norm_sub_sub_le hμ' (mem_ball_zero_iff.mpr h₂)
    (mem_ball_zero_iff.mpr h₁)
  set a := cepsChartSlope ρW with ha
  have hav : 0 < Real.sqrt (cepsStepVar ρW / 2) :=
    Real.sqrt_pos.mpr (by have := cepsStepVar_pos hW hθ hD; linarith)
  have hare : a.re = Real.sqrt (cepsStepVar ρW / 2) := by rw [ha, cepsChartSlope, ofReal_re]
  have haim : a.im = 0 := by rw [ha, cepsChartSlope, ofReal_im]
  have han : ‖a‖ = Real.sqrt (cepsStepVar ρW / 2) := norm_cepsChartSlope
  have hu1 : u₁.im = 0 := by
    have := congrArg im hr₁; rw [conj_im] at this; linarith
  have hu2 : u₂.im = 0 := by
    have := congrArg im hr₂; rw [conj_im] at this; linarith
  have hd : ‖u₂ - u₁‖ = u₂.re - u₁.re := by
    have e : u₂ - u₁ = ((u₂.re - u₁.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hu1, hu2]
    rw [e, norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hre := (neg_le_abs _).trans ((abs_re_le_norm _).trans key)
  rw [hd, han] at hre
  simp only [sub_re, mul_re, haim, hu1, hu2, mul_zero, sub_zero, hare] at hre
  nlinarith

end Conj

namespace CepsCanonDomain

variable (dom : CepsCanonDomain D θ v)

section Roots

variable (hW : IsStepLaw ρW fW D θ v) (hθ : 0 < θ) (hD : 0 < D)
include hW hθ hD

omit hW hθ hD in
theorem norm_ofReal_le_μ₀ {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) : ‖(μ : ℂ)‖ ≤ dom.μ₀ := by
  rwa [norm_real, Real.norm_eq_abs]

/-- `d(β±) = 0`. -/
theorem cepsD_rootPlus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) :
    cepsD ρW μ q (cepsRootPlus D θ ρW μ q) = 0 := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hb := dom.norm_rootPlus_le hW hθ hD hμ' hq
  have hc := dom.c₀_pos
  refine (dom.cepsD_eq_zero_iff hW hθ hD hμ' (by simp; exact dom.η_pos.le) hq ?_).mpr (Or.inl rfl)
  have := abs_re_le_norm (cepsRootPlus D θ ρW μ q)
  linarith

theorem cepsD_rootMinus {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀) :
    cepsD ρW μ q (cepsRootMinus D θ ρW μ q) = 0 := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hb := dom.norm_rootMinus_le hW hθ hD hμ' hq
  have hc := dom.c₀_pos
  refine (dom.cepsD_eq_zero_iff hW hθ hD hμ' (by simp; exact dom.η_pos.le) hq ?_).mpr (Or.inr rfl)
  have := abs_re_le_norm (cepsRootMinus D θ ρW μ q)
  linarith

/-- **Real discount.** For real `μ` and `0 < q ≤ q₀`, both roots are real and `β₋ < 0 < β₊`. -/
theorem roots_real {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℝ} (hq : 0 < q) (hq₀ : q ≤ dom.q₀) :
    conj (cepsRootPlus D θ ρW μ q) = cepsRootPlus D θ ρW μ q ∧
      conj (cepsRootMinus D θ ρW μ q) = cepsRootMinus D θ ρW μ q ∧
      0 < (cepsRootPlus D θ ρW μ q).re ∧ (cepsRootMinus D θ ρW μ q).re < 0 := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hμc := dom.μ_lt_chart hμ'
  have hqn : ‖(q : ℂ)‖ ≤ dom.q₀ := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hq]; exact hq₀
  set m := cepsMorseMin D θ ρW μ with hmdef
  set b := cepsMorseCenter D θ ρW μ with hbdef
  have hmr : (m.re : ℂ) = m := conj_eq_iff_re.mp (conj_cepsMorseMin hW hθ hD hμc)
  have hm0 : m.re ≤ 0 := re_cepsMorseMin_nonpos hW hθ hD hμc
  have hbr : conj b = b := conj_cepsMorseCenter hW hθ hD hμc
  -- `r₊ = √(q - m)` is a positive real
  set R : ℝ := Real.sqrt (q - m.re) with hRdef
  have hR0 : 0 < R := Real.sqrt_pos.mpr (by linarith)
  have hRsq : R ^ 2 = q - m.re := Real.sq_sqrt (by linarith)
  have hr : cepsRootR D θ ρW μ q = (R : ℂ) := by
    rw [cepsRootR, ← hmdef, ← hmr, show (q : ℂ) - (m.re : ℂ) = ((q - m.re : ℝ) : ℂ) by push_cast; ring,
      Complex.sqrt_of_nonneg (by rw [Complex.zero_le_real]; linarith), ofReal_re]
  have hrn := dom.norm_cepsRootR_lt hW hθ hD hμ' hqn
  rw [hr] at hrn
  have hrn' : ‖((-R : ℝ) : ℂ)‖ < cepsChartRho D θ := by rwa [norm_real, Real.norm_eq_abs,
    abs_neg, ← Real.norm_eq_abs, ← norm_real]
  have hplus : cepsRootPlus D θ ρW μ q = cepsMorseRoot D θ ρW μ R := by rw [cepsRootPlus, hr]
  have hminus : cepsRootMinus D θ ρW μ q = cepsMorseRoot D θ ρW μ ((-R : ℝ) : ℂ) := by
    rw [cepsRootMinus, hr, ofReal_neg]
  have hcp := conj_cepsMorseRoot hW hθ hD hμc hrn
  have hcm := conj_cepsMorseRoot hW hθ hD hμc hrn'
  have hR0' := cepsChartRadius_pos hD hθ
  have hRle := cepsChartRadius_le_r0 (D := D) (θ := θ)
  have hr0 := cepsCgfRadius_pos hD hθ
  have hbn := norm_cepsMorseCenter_lt hW hθ hD hμc
  -- the point `ζ = 0`: chart value `x` with `x² = -m`
  set u₀ : ℂ := -b with hu₀
  have hu₀n : ‖u₀‖ < cepsChartRadius D θ := by rw [hu₀, norm_neg]; exact hbn
  have hu₀r : conj u₀ = u₀ := by rw [hu₀, map_neg, hbr]
  have hg0r : conj (cepsMorseG D θ ρW μ u₀) = cepsMorseG D θ ρW μ u₀ := by
    rw [← cepsMorseG_conj hW hθ hD hμc (by linarith), hu₀r]
  have hg0sq : (cepsMorseG D θ ρW μ u₀) ^ 2 = -m := by
    have h := cepsCgfShift_center_add hW hθ hD hμc (u := u₀) (by rw [hu₀, norm_neg]; linarith)
    rw [hu₀, add_neg_cancel, cepsCgfShift, cepsCgf_zero hW, mul_zero, add_zero] at h
    have hk2 : (Complex.sqrt (cepsMorseK ρW b u₀)) ^ 2 = cepsMorseK ρW b u₀ := by
      rw [Complex.sqrt]; exact cpow_ofNat_inv_pow _ 2
    rw [cepsMorseG, ← hbdef, mul_pow, hk2]
    linear_combination -h
  set x := (cepsMorseG D θ ρW μ u₀).re with hx
  have hxr : (x : ℂ) = cepsMorseG D θ ρW μ u₀ := conj_eq_iff_re.mp hg0r
  have hx2 : x ^ 2 = -m.re := by
    have := congrArg re hg0sq
    rw [← hxr, ← ofReal_pow, ofReal_re, neg_re] at this
    exact this
  have hxR : |x| < R := by
    have : x ^ 2 < R ^ 2 := by rw [hx2, hRsq]; linarith
    exact abs_lt_of_sq_lt_sq this hR0.le
  refine ⟨by rw [hplus]; exact hcp, by rw [hminus]; exact hcm, ?_, ?_⟩
  · -- `β₊ > 0`
    obtain ⟨hu, hg⟩ := cepsMorseRoot_sub_center hW hθ hD hμc hrn
    set u := cepsMorseRoot D θ ρW μ R - b with hudef
    have hun : ‖u‖ < cepsChartRadius D θ := mem_ball_zero_iff.mp hu
    have hur : conj u = u := by rw [hudef, map_sub, hcp, hbr]
    by_contra hneg
    push Not at hneg
    have hle : u.re ≤ u₀.re := by
      have e1 : (cepsRootPlus D θ ρW μ q).re = b.re + u.re := by
        rw [hplus, hudef]; simp
      rw [hu₀, neg_re]; linarith
    have := re_cepsMorseG_le hW hθ hD hμc hun hu₀n hur hu₀r hle
    rw [hg, ofReal_re] at this
    have := (abs_lt.mp hxR).2
    linarith
  · -- `β₋ < 0`
    obtain ⟨hu, hg⟩ := cepsMorseRoot_sub_center hW hθ hD hμc hrn'
    set u := cepsMorseRoot D θ ρW μ ((-R : ℝ) : ℂ) - b with hudef
    have hun : ‖u‖ < cepsChartRadius D θ := mem_ball_zero_iff.mp hu
    have hur : conj u = u := by rw [hudef, map_sub, hcm, hbr]
    by_contra hpos
    push Not at hpos
    have hle : u₀.re ≤ u.re := by
      have e1 : (cepsRootMinus D θ ρW μ q).re = b.re + u.re := by
        rw [hminus, hudef]; simp
      rw [hu₀, neg_re]; linarith
    have := re_cepsMorseG_le hW hθ hD hμc hu₀n hun hu₀r hur hle
    rw [hg, ofReal_re] at this
    have := (abs_lt.mp hxR).1
    linarith

/-- Continuity of `q ↦ β±(μ, q)` at `q` with `Re (q - m(μ)) ≥ 0`. -/
theorem continuousAt_roots {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq : ‖q‖ ≤ dom.q₀)
    (hre : 0 ≤ (q - cepsMorseMin D θ ρW μ).re) :
    ContinuousAt (fun q => cepsRootPlus D θ ρW μ q) q ∧
      ContinuousAt (fun q => cepsRootMinus D θ ρW μ q) q := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hμc := dom.μ_lt_chart hμ'
  have hμb : (μ : ℂ) ∈ ball (0 : ℂ) (cepsChartMu D θ) := mem_ball_zero_iff.mpr hμc
  have hrn := dom.norm_cepsRootR_lt hW hθ hD hμ' hq
  have hsq : ContinuousAt (fun q => cepsRootR D θ ρW μ q) q := by
    have h1 : ContinuousAt (fun q : ℂ => q - cepsMorseMin D θ ρW μ) q :=
      continuousAt_id.sub continuousAt_const
    exact ContinuousAt.comp (g := Complex.sqrt) (Complex.continuousAt_sqrt (Or.inl hre)) h1
  have hΘ : ∀ r : ℂ, ‖r‖ < cepsChartRho D θ → ContinuousAt (cepsMorseRoot D θ ρW μ) r := by
    intro r hr
    have hrb : r ∈ ball (0 : ℂ) (cepsChartRho D θ) := mem_ball_zero_iff.mpr hr
    have h := (differentiableOn_cepsMorseRoot hW hθ hD ((μ : ℂ), r) ⟨hμb, hrb⟩).differentiableAt
      ((isOpen_ball.prod isOpen_ball).mem_nhds ⟨hμb, hrb⟩)
    exact (h.comp r ((differentiableAt_const _).prodMk differentiableAt_id)).continuousAt
  refine ⟨?_, ?_⟩
  · exact ContinuousAt.comp (g := cepsMorseRoot D θ ρW μ) (hΘ _ hrn) hsq
  · exact ContinuousAt.comp (g := cepsMorseRoot D θ ρW μ) (hΘ _ (by rwa [norm_neg]))
      hsq.neg

/-- **Location of the roots.** For real `μ` and `Re q > 0`, `‖q‖ ≤ q₀`:
`Re β₊ > 0` and `Re β₋ < 0`. -/
theorem re_roots {μ : ℝ} (hμ : |μ| ≤ dom.μ₀) {q : ℂ} (hq0 : 0 < q.re) (hq : ‖q‖ ≤ dom.q₀) :
    0 < (cepsRootPlus D θ ρW μ q).re ∧ (cepsRootMinus D θ ρW μ q).re < 0 := by
  have hμ' := dom.norm_ofReal_le_μ₀ hμ
  have hμc := dom.μ_lt_chart hμ'
  have hm0 := re_cepsMorseMin_nonpos hW hθ hD hμc
  have hq₀ := dom.q₀_pos
  have := hW.isProbabilityMeasure
  -- the segment from `q₀` to `q`
  set P : ℝ → ℂ := fun t => ((1 - t : ℝ) : ℂ) * (dom.q₀ : ℂ) + (t : ℂ) * q with hP
  have hPn : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t‖ ≤ dom.q₀ := by
    intro t ht
    calc ‖P t‖ ≤ ‖((1 - t : ℝ) : ℂ) * (dom.q₀ : ℂ)‖ + ‖(t : ℂ) * q‖ := norm_add_le _ _
      _ = (1 - t) * dom.q₀ + t * ‖q‖ := by
          rw [norm_mul, norm_mul, norm_real, norm_real, norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2]),
            abs_of_nonneg ht.1, abs_of_pos hq₀]
      _ ≤ (1 - t) * dom.q₀ + t * dom.q₀ := by gcongr; exact ht.1
      _ = dom.q₀ := by ring
  have hPre : ∀ t ∈ Icc (0 : ℝ) 1, 0 < (P t).re := by
    intro t ht
    simp only [hP, add_re, re_ofReal_mul, ofReal_re]
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; simp; exact hq₀
    · have : 0 ≤ (1 - t) * dom.q₀ := mul_nonneg (by linarith [ht.2]) hq₀.le
      nlinarith
  have hcont : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt (fun q => cepsRootPlus D θ ρW μ q) (P t) ∧
      ContinuousAt (fun q => cepsRootMinus D θ ρW μ q) (P t) := by
    intro t ht
    refine dom.continuousAt_roots hW hθ hD hμ (hPn t ht) ?_
    rw [sub_re]; linarith [hPre t ht]
  have hPc : Continuous P := by simp only [hP]; fun_prop
  have hne : ∀ t ∈ Icc (0 : ℝ) 1, (cepsRootPlus D θ ρW μ (P t)).re ≠ 0 ∧
      (cepsRootMinus D θ ρW μ (P t)).re ≠ 0 := by
    intro t ht
    constructor
    · intro h0
      exact cepsD_ne_zero_of_re_eq_zero ρW μ (hPre t ht) h0
        (dom.cepsD_rootPlus hW hθ hD hμ (hPn t ht))
    · intro h0
      exact cepsD_ne_zero_of_re_eq_zero ρW μ (hPre t ht) h0
        (dom.cepsD_rootMinus hW hθ hD hμ (hPn t ht))
  have hP0 : P 0 = ((dom.q₀ : ℝ) : ℂ) := by simp [hP]
  have hP1 : P 1 = q := by simp [hP]
  obtain ⟨-, -, h0p, h0m⟩ := dom.roots_real hW hθ hD hμ hq₀ le_rfl
  have hfp : ContinuousOn (fun t => (cepsRootPlus D θ ρW μ (P t)).re) (Icc 0 1) := fun t ht =>
    (continuous_re.continuousAt.comp ((hcont t ht).1.comp hPc.continuousAt)).continuousWithinAt
  have hfm : ContinuousOn (fun t => (cepsRootMinus D θ ρW μ (P t)).re) (Icc 0 1) := fun t ht =>
    (continuous_re.continuousAt.comp ((hcont t ht).2.comp hPc.continuousAt)).continuousWithinAt
  constructor
  · by_contra hc
    push Not at hc
    have hsub := intermediate_value_Icc' (zero_le_one (α := ℝ)) hfp
    have h0mem : (0 : ℝ) ∈ Icc (cepsRootPlus D θ ρW μ (P 1)).re
        (cepsRootPlus D θ ρW μ (P 0)).re := by
      rw [hP1, hP0]; exact ⟨hc, h0p.le⟩
    obtain ⟨t, ht, hft⟩ := hsub h0mem
    exact (hne t ht).1 hft
  · by_contra hc
    push Not at hc
    have hsub := intermediate_value_Icc (zero_le_one (α := ℝ)) hfm
    have h0mem : (0 : ℝ) ∈ Icc (cepsRootMinus D θ ρW μ (P 0)).re
        (cepsRootMinus D θ ρW μ (P 1)).re := by
      rw [hP1, hP0]; exact ⟨h0m.le, hc⟩
    obtain ⟨t, ht, hft⟩ := hsub h0mem
    exact (hne t ht).2 hft

end Roots

end CepsCanonDomain

end PGM
