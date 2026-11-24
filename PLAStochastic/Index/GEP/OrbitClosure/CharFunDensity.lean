import PLAStochastic.Index.GEP.OrbitClosure.Defs
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# WP2: density bounds from characteristic functions (the Mathlib gap)

Mathlib v4.33.1 has Fourier inversion only at continuity points of an integrable function
with integrable transform (`MeasureTheory.Integrable.fourierInv_fourier_eq`), and Plancherel
only as an abstract isometry of `L²` (`MeasureTheory.Lp.norm_fourier_eq`), not linked to the
integral transform of an `L¹ ∩ L²` density.  Neither is used here.  Both facts needed by
`lem:sumdensity` (`research/2026-09-25-kep-proof/tex/main.tex` L246–270) follow from one
Gaussian smoothing identity (Fubini plus `integral_cexp_quadratic`):

`∫ φ_δ(y - x) dμ(y) = (2π)⁻¹ ∫ e^{-itx} ψ_μ(t) e^{-δt²/2} dt`, `φ_δ` the `N(0, δ)` density.

* `locBd_of_integrable_charFun` (inversion replaced): an integrable characteristic function
  gives `LocBd ((2π)⁻¹ ‖ψ‖₁) μ`.  Route: the identity bounds the density of `μ ∗ N(0, δ)` by
  `(2π)⁻¹ ‖ψ‖₁`; Fatou as `δ → 0` on open sets; outer regularity of Lebesgue measure.
* `integral_norm_charFun_sq_le` (Plancherel replaced): `LocBd D μ` gives
  `∫ ‖ψ‖² ≤ 2π D`.  Route: `‖ψ‖²` is the characteristic function of `symmConv μ`, the law of
  `X - X'`, which has `LocBd D`; the identity at `x = 0` gives `∫ ‖ψ‖² e^{-δt²/2} ≤ 2π D`;
  monotone convergence as `δ → 0`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal Real

/-! ## Convolution and local bounds -/

/-- Convolution with a probability measure keeps a local bound. -/
theorem LocBd.conv_left {D : ℝ} {μ : Measure ℝ} (hμ : LocBd D μ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] [SFinite μ] : LocBd D (ν ∗ μ) := by
  intro A hA
  have hm : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) := measurable_add hA
  rw [Measure.conv, Measure.map_apply measurable_add hA, Measure.prod_apply hm]
  calc ∫⁻ x, μ (Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A)) ∂ν
      ≤ ∫⁻ _, ENNReal.ofReal D * volume A ∂ν := by
        refine lintegral_mono fun x => ?_
        have hx : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) = (fun y => x + y) ⁻¹' A :=
          rfl
        rw [hx]
        calc μ ((fun y => x + y) ⁻¹' A) ≤ ENNReal.ofReal D * volume ((fun y => x + y) ⁻¹' A) :=
              hμ _ (measurable_const_add x hA)
          _ = ENNReal.ofReal D * volume A := by rw [measure_preimage_add]
    _ = ENNReal.ofReal D * volume A := by simp

/-- Every convolution power `n ≥ 1` keeps a local bound. -/
theorem LocBd.convPow {D : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : LocBd D μ)
    {n : ℕ} (hn : 1 ≤ n) : LocBd D (convPow μ n) := by
  induction n, hn using Nat.le_induction with
  | base => rw [convPow_one]; exact hμ
  | succ n _ _ => rw [convPow_succ]; exact hμ.conv_left _

/-- The characteristic function of a convolution power is the power. -/
theorem charFun_convPow (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = charFun μ t ^ n := by
  induction n with
  | zero => simp [convPow_zero]
  | succ n ih => rw [convPow_succ, charFun_conv, ih, pow_succ]

/-- The symmetrisation `μ ∗ μ⁻`: the law of `X - X'` for independent `X, X' ∼ μ`. -/
def symmConv (μ : Measure ℝ) : Measure ℝ := μ ∗ μ.map (fun x => -x)

instance (μ : Measure ℝ) [IsProbabilityMeasure μ] : IsProbabilityMeasure (symmConv μ) := by
  unfold symmConv
  have : IsProbabilityMeasure (μ.map fun x : ℝ => -x) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  infer_instance

/-- `ψ_{-X} = conj ψ_X`. -/
theorem charFun_map_neg_real (μ : Measure ℝ) (t : ℝ) :
    charFun (μ.map (fun x => -x)) t = (starRingEnd ℂ) (charFun μ t) := by
  have h : (fun x : ℝ => -x) = fun x => (-1) * x := by funext x; ring
  rw [h, charFun_map_mul, neg_one_mul, charFun_neg]

/-- `ψ_{X - X'} = |ψ_X|²`. -/
theorem charFun_symmConv (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    charFun (symmConv μ) t = ((‖charFun μ t‖ ^ 2 : ℝ) : ℂ) := by
  have : IsProbabilityMeasure (μ.map fun x : ℝ => -x) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  rw [symmConv, charFun_conv, charFun_map_neg_real, mul_conj, normSq_eq_norm_sq]

theorem LocBd.symmConv {D : ℝ} {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : LocBd D μ) :
    LocBd D (symmConv μ) := by
  have : IsProbabilityMeasure (μ.map fun x : ℝ => -x) :=
    Measure.isProbabilityMeasure_map measurable_neg.aemeasurable
  rw [PGM.symmConv, Measure.conv_comm]
  exact hμ.conv_left _

/-! ## The Gaussian smoothing identity -/

/-- The inner Gaussian integral: `∫ e^{it(y - x)} e^{-δt²/2} dt = 2π φ_δ(y - x)`. -/
theorem integral_gauss_inner {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    ∫ t : ℝ, cexp (-(↑(t * x) * I)) * cexp (↑t * ↑y * I) *
        ((Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) =
      (2 * π : ℂ) * ((gaussianPDFReal x (Real.toNNReal δ) y : ℝ) : ℂ) := by
  have h1 : ∀ t : ℝ, cexp (-(↑(t * x) * I)) * cexp (↑t * ↑y * I) *
      ((Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) =
      cexp (-((δ : ℂ) / 2) * (t : ℂ) ^ 2 + (((y - x : ℝ) : ℂ) * I) * t + 0) := by
    intro t
    rw [ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [h1]
  have hb : (-((δ : ℂ) / 2)).re < 0 := by simp [hδ]
  rw [integral_cexp_quadratic hb]
  have h2 : ((π : ℂ) / -(-((δ : ℂ) / 2))) = ((2 * π / δ : ℝ) : ℂ) := by
    push_cast
    field_simp
  have h3 : ((2 * π / δ : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((√(2 * π / δ) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have h4 : (0 - (((y - x : ℝ) : ℂ) * I) ^ 2 / (4 * -((δ : ℂ) / 2))) =
      ((-(y - x) ^ 2 / (2 * δ) : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, I_sq]
    field_simp
    ring
  rw [h2, h3, h4, ← ofReal_exp]
  have h5 : √(2 * π / δ) = 2 * π * (√(2 * π * δ))⁻¹ := by
    have hs : 0 < √(2 * π * δ) := Real.sqrt_pos.2 (by positivity)
    rw [eq_mul_inv_iff_mul_eq₀ hs.ne', ← Real.sqrt_mul (by positivity),
      show 2 * π / δ * (2 * π * δ) = (2 * π) ^ 2 by field_simp,
      Real.sqrt_sq (by positivity)]
  rw [gaussianPDFReal, Real.coe_toNNReal δ hδ.le, h5]
  push_cast
  ring

/-- **Gaussian smoothing identity.**  For a finite measure `μ`, `δ > 0` and `x`,
`∫ φ_δ(y - x) dμ(y) = (2π)⁻¹ ∫ e^{-itx} ψ_μ(t) e^{-δt²/2} dt`, where
`φ_δ = gaussianPDFReal x δ`.  Proof: `integral_cexp_quadratic` for the inner Gaussian
integral and `integral_integral_swap` (the integrand is bounded by `e^{-δt²/2}`). -/
theorem integral_gaussianPDFReal_eq_charFun {μ : Measure ℝ} [IsFiniteMeasure μ] {δ : ℝ}
    (hδ : 0 < δ) (x : ℝ) :
    ((∫ y, gaussianPDFReal x (Real.toNNReal δ) y ∂μ : ℝ) : ℂ) =
      ((2 * π)⁻¹ : ℂ) * ∫ t : ℝ, cexp (-(↑(t * x) * I)) * charFun μ t *
        ((Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) := by
  set G : ℝ → ℝ → ℂ := fun t y => cexp (-(↑(t * x) * I)) * cexp (↑t * ↑y * I) *
    ((Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) with hG
  have hF : ∀ t : ℝ, cexp (-(↑(t * x) * I)) * charFun μ t *
      ((Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) = ∫ y, G t y ∂μ := by
    intro t
    rw [charFun_apply_real, ← integral_const_mul, ← integral_mul_const]
  have hnorm : ∀ t y, ‖G t y‖ = Real.exp (-(δ / 2) * t ^ 2) := by
    intro t y
    simp only [hG, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
      Real.abs_exp]
    simp only [neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      neg_zero, Real.exp_zero, one_mul, mul_im, add_zero, zero_mul]
    congr 1
    ring
  have hint : Integrable (Function.uncurry G) (volume.prod μ) := by
    refine Integrable.mono' ((integrable_exp_neg_mul_sq (by positivity : 0 < δ / 2)).mul_prod
      (integrable_const (1 : ℝ))) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hG]
      fun_prop
    · refine Filter.Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, mul_one]
      exact (hnorm p.1 p.2).le
  simp_rw [hF]
  rw [integral_integral_swap hint]
  simp_rw [hG, integral_gauss_inner hδ x]
  rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_mul]
  exact integral_complex_ofReal.symm

/-! ## The two consequences -/

open Filter Topology

/-- The Gaussian density is symmetric in its mean and its argument. -/
theorem gaussianPDFReal_symm (x y : ℝ) (v : NNReal) :
    gaussianPDFReal x v y = gaussianPDFReal y v x := by
  simp only [gaussianPDFReal]
  ring_nf

/-- The Gaussian density is bounded by its value at the mean. -/
theorem gaussianPDFReal_le_inv_sqrt (x y : ℝ) (v : NNReal) :
    gaussianPDFReal x v y ≤ (√(2 * π * v))⁻¹ := by
  rw [gaussianPDFReal]
  refine mul_le_of_le_one_right (inv_nonneg.2 (Real.sqrt_nonneg _)) (Real.exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- The Gaussian density is integrable against every finite measure. -/
theorem integrable_gaussianPDFReal_of_finite (μ : Measure ℝ) [IsFiniteMeasure μ] (x : ℝ)
    (v : NNReal) : Integrable (fun y => gaussianPDFReal x v y) μ := by
  refine Integrable.mono' (integrable_const (√(2 * π * v))⁻¹)
    (measurable_gaussianPDFReal x v).aestronglyMeasurable (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  exact gaussianPDFReal_le_inv_sqrt x y v

/-- Chebyshev for `N(y, v)`: the ball `B(y, r)` has mass at least `1 - v / r²`. -/
theorem gaussianReal_ball_ge (y : ℝ) (v : NNReal) {r : ℝ} (hr : 0 < r) :
    1 - ENNReal.ofReal (v / r ^ 2) ≤ gaussianReal y v (Metric.ball y r) := by
  have hcheb := meas_ge_le_variance_div_sq (μ := gaussianReal y v) (X := id)
    (memLp_id_gaussianReal' 2 (by simp)) hr
  rw [variance_id_gaussianReal] at hcheb
  have hmean : (gaussianReal y v)[id] = y := integral_id_gaussianReal
  rw [hmean] at hcheb
  have hsub : (Metric.ball y r)ᶜ ⊆ {ω | r ≤ |id ω - y|} := by
    intro ω hω
    simp only [mem_compl_iff, Metric.mem_ball, not_lt, Real.dist_eq] at hω
    simpa using hω
  have hsum := measure_add_measure_compl (μ := gaussianReal y v) (s := Metric.ball y r)
    Metric.isOpen_ball.measurableSet
  rw [measure_univ] at hsum
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0∞) = gaussianReal y v (Metric.ball y r) + gaussianReal y v (Metric.ball y r)ᶜ :=
        hsum.symm
    _ ≤ gaussianReal y v (Metric.ball y r) + ENNReal.ofReal (v / r ^ 2) :=
        add_le_add_right ((measure_mono hsub).trans hcheb) _


/-- **Density bound from an integrable characteristic function** (replaces Fourier inversion
in `lem:sumdensity`): `μ A ≤ (2π)⁻¹ ‖ψ_μ‖₁ |A|`. -/
theorem locBd_of_integrable_charFun {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : Integrable (charFun μ)) :
    LocBd ((2 * π)⁻¹ * ∫ t, ‖charFun μ t‖) μ := by
  set C := (2 * π)⁻¹ * ∫ t, ‖charFun μ t‖ with hC
  -- Step 1: the smoothed density is bounded by `C`.
  have hbd : ∀ {δ : ℝ}, 0 < δ → ∀ x, ∫ y, gaussianPDFReal x (Real.toNNReal δ) y ∂μ ≤ C := by
    intro δ hδ x
    have hid := integral_gaussianPDFReal_eq_charFun (μ := μ) hδ x
    have h1 : ∫ y, gaussianPDFReal x (Real.toNNReal δ) y ∂μ ≤
        ‖((∫ y, gaussianPDFReal x (Real.toNNReal δ) y ∂μ : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact le_abs_self _
    refine h1.trans ?_
    rw [hid, norm_mul, hC]
    have h2pi : ‖((2 * π)⁻¹ : ℂ)‖ = (2 * π)⁻¹ := by
      have : ((2 * π)⁻¹ : ℂ) = (((2 * π)⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h2pi]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) h.norm
      (Eventually.of_forall fun t => ?_)
    simp only [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp]
    simp only [neg_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      neg_zero, Real.exp_zero, one_mul]
    refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ δ * t ^ 2 / 2 := by positivity
    linarith
  -- Step 2: open sets, by Fatou as `δ → 0`.
  have hopen : ∀ U : Set ℝ, IsOpen U → μ U ≤ ENNReal.ofReal C * volume U := by
    intro U hU
    set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
    have hδpos : ∀ n, 0 < δ n := fun n => by positivity
    set f : ℕ → ℝ → ℝ≥0∞ := fun n y =>
      ∫⁻ x in U, ENNReal.ofReal (gaussianPDFReal x (Real.toNNReal (δ n)) y) with hf
    have hjoint : ∀ n, Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (gaussianPDFReal p.2 (Real.toNNReal (δ n)) p.1) := by
      intro n
      refine ENNReal.measurable_ofReal.comp ?_
      unfold gaussianPDFReal
      fun_prop
    have hmeas : ∀ n, Measurable (f n) := fun n => (hjoint n).lintegral_prod_right'
    have hlow : ∀ y, U.indicator 1 y ≤ liminf (fun n => f n y) atTop := by
      intro y
      by_cases hy : y ∈ U
      · rw [indicator_of_mem hy, Pi.one_apply]
        obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU y hy
        have hge : ∀ n, 1 - ENNReal.ofReal (δ n / r ^ 2) ≤ f n y := by
          intro n
          have hv : Real.toNNReal (δ n) ≠ 0 := by
            simpa [Real.toNNReal_eq_zero, not_le] using hδpos n
          calc 1 - ENNReal.ofReal (δ n / r ^ 2)
              = 1 - ENNReal.ofReal ((Real.toNNReal (δ n) : ℝ) / r ^ 2) := by
                rw [Real.coe_toNNReal _ (hδpos n).le]
            _ ≤ gaussianReal y (Real.toNNReal (δ n)) (Metric.ball y r) :=
                gaussianReal_ball_ge y _ hr
            _ ≤ gaussianReal y (Real.toNNReal (δ n)) U := measure_mono hball
            _ = f n y := by
                rw [gaussianReal_apply _ hv]
                simp only [hf, gaussianPDF, gaussianPDFReal_symm y]
        have htend : Tendsto (fun n => 1 - ENNReal.ofReal (δ n / r ^ 2)) atTop (𝓝 1) := by
          have h0 : Tendsto (fun n => δ n / r ^ 2) atTop (𝓝 0) := by
            have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const (r ^ 2)
            rw [zero_div] at this
            exact this
          have := ENNReal.Tendsto.sub tendsto_const_nhds (ENNReal.tendsto_ofReal h0)
            (Or.inl ENNReal.one_ne_top)
          simpa using this
        calc (1 : ℝ≥0∞) = liminf (fun n => 1 - ENNReal.ofReal (δ n / r ^ 2)) atTop :=
              htend.liminf_eq.symm
          _ ≤ liminf (fun n => f n y) atTop := liminf_le_liminf (Eventually.of_forall hge)
      · rw [indicator_of_notMem hy]
        exact zero_le
    have hupper : ∀ n, ∫⁻ y, f n y ∂μ ≤ ENNReal.ofReal C * volume U := by
      intro n
      rw [lintegral_lintegral_swap (hjoint n).aemeasurable]
      calc ∫⁻ x in U, ∫⁻ y, ENNReal.ofReal (gaussianPDFReal x (Real.toNNReal (δ n)) y) ∂μ
          ≤ ∫⁻ _ in U, ENNReal.ofReal C := by
            refine lintegral_mono fun x => ?_
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrable_gaussianPDFReal_of_finite μ x _)
              (ae_of_all _ fun y => gaussianPDFReal_nonneg _ _ _)]
            exact ENNReal.ofReal_le_ofReal (hbd (hδpos n) x)
        _ = ENNReal.ofReal C * volume U := by rw [setLIntegral_const]
    calc μ U = ∫⁻ y, U.indicator 1 y ∂μ := (lintegral_indicator_one hU.measurableSet).symm
      _ ≤ ∫⁻ y, liminf (fun n => f n y) atTop ∂μ := lintegral_mono hlow
      _ ≤ liminf (fun n => ∫⁻ y, f n y ∂μ) atTop := lintegral_liminf_le hmeas
      _ ≤ ENNReal.ofReal C * volume U :=
          liminf_le_of_frequently_le' (Frequently.of_forall hupper)
  -- Step 3: outer regularity of Lebesgue measure.
  intro A _
  have : (ENNReal.ofReal C • volume : Measure ℝ).OuterRegular :=
    Measure.OuterRegular.smul volume ENNReal.ofReal_ne_top
  calc μ A ≤ ⨅ (U) (_ : A ⊆ U) (_ : IsOpen U), (ENNReal.ofReal C • volume : Measure ℝ) U := by
        refine le_iInf₂ fun U hAU => le_iInf fun hU => ?_
        rw [Measure.smul_apply, smul_eq_mul]
        exact (measure_mono hAU).trans (hopen U hU)
    _ = (ENNReal.ofReal C • volume : Measure ℝ) A := (A.measure_eq_iInf_isOpen _).symm
    _ = ENNReal.ofReal C * volume A := by rw [Measure.smul_apply, smul_eq_mul]

/-- **`L²` bound of the characteristic function** (replaces Plancherel in `lem:sumdensity`):
a local bound `D` gives `∫ ‖ψ_μ‖² ≤ 2π D`. -/
theorem integral_norm_charFun_sq_le {μ : Measure ℝ} [IsProbabilityMeasure μ] {D : ℝ}
    (hD : LocBd D μ) :
    Integrable (fun t => ‖charFun μ t‖ ^ 2) ∧ ∫ t, ‖charFun μ t‖ ^ 2 ≤ 2 * π * D := by
  have hD0 : 0 ≤ D := by
    by_contra hneg
    have h1 := hD univ MeasurableSet.univ
    rw [measure_univ, ENNReal.ofReal_of_nonpos (not_le.1 hneg).le, zero_mul] at h1
    exact one_ne_zero (le_zero_iff.1 h1)
  have hν : LocBd D (symmConv μ) := hD.symmConv
  have hmle : symmConv μ ≤ ENNReal.ofReal D • volume := by
    rw [Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, smul_eq_mul]
    exact hν s hs
  set g : ℝ → ℝ := fun t => ‖charFun μ t‖ ^ 2 with hg
  have hg1 : ∀ t, g t ≤ 1 := fun t => by
    simp only [hg]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one t)
  have hg0 : ∀ t, 0 ≤ g t := fun t => by positivity
  have hgm : Measurable g := (measurable_charFun (μ := μ)).norm.pow_const 2
  -- Step 1: for each `δ > 0`, `∫ g e^{-δt²/2} ≤ 2πD`.
  have hstep : ∀ {δ : ℝ}, 0 < δ → ∫ t, g t * Real.exp (-(δ * t ^ 2 / 2)) ≤ 2 * π * D := by
    intro δ hδ
    have hv : Real.toNNReal δ ≠ 0 := by simpa [Real.toNNReal_eq_zero, not_le] using hδ
    have hid := integral_gaussianPDFReal_eq_charFun (μ := symmConv μ) hδ 0
    simp_rw [charFun_symmConv] at hid
    have hrhs : ∫ t : ℝ, cexp (-(↑(t * 0) * I)) * ((‖charFun μ t‖ ^ 2 : ℝ) : ℂ) *
        ((Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) =
        ((∫ t, g t * Real.exp (-(δ * t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext t
      simp [hg]
    rw [hrhs] at hid
    have hreal : ∫ y, gaussianPDFReal 0 (Real.toNNReal δ) y ∂(symmConv μ) =
        (2 * π)⁻¹ * ∫ t, g t * Real.exp (-(δ * t ^ 2 / 2)) := by
      exact_mod_cast hid
    have hle : ∫ y, gaussianPDFReal 0 (Real.toNNReal δ) y ∂(symmConv μ) ≤ D := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (gaussianPDFReal_nonneg _ _))
        (measurable_gaussianPDFReal _ _).aestronglyMeasurable]
      have hl : ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal δ) y) ∂(symmConv μ) ≤
          ENNReal.ofReal D := by
        calc _ ≤ ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal δ) y)
              ∂(ENNReal.ofReal D • volume) := lintegral_mono' hmle le_rfl
          _ = ENNReal.ofReal D := by
              rw [lintegral_smul_measure, lintegral_gaussianPDFReal_eq_one 0 hv, smul_eq_mul,
                mul_one]
      calc _ ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
        _ = D := ENNReal.toReal_ofReal hD0
    have h2pi : 0 < 2 * π := by positivity
    calc ∫ t, g t * Real.exp (-(δ * t ^ 2 / 2))
        = 2 * π * ((2 * π)⁻¹ * ∫ t, g t * Real.exp (-(δ * t ^ 2 / 2))) := by
          field_simp
      _ = 2 * π * ∫ y, gaussianPDFReal 0 (Real.toNNReal δ) y ∂(symmConv μ) := by rw [hreal]
      _ ≤ 2 * π * D := mul_le_mul_of_nonneg_left hle h2pi.le
  -- Step 2: Fatou as `δ → 0`.
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hδdef
  have hδpos : ∀ n, 0 < δ n := fun n => by positivity
  set F : ℕ → ℝ → ℝ≥0∞ := fun n t => ENNReal.ofReal (g t * Real.exp (-(δ n * t ^ 2 / 2)))
    with hF
  have hFint : ∀ n, Integrable (fun t => g t * Real.exp (-(δ n * t ^ 2 / 2))) := by
    intro n
    refine Integrable.mono' (integrable_exp_neg_mul_sq (b := δ n / 2) (by linarith [hδpos n]))
      (hgm.mul (by fun_prop)).aestronglyMeasurable (ae_of_all _ fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg0 t) (Real.exp_pos _).le)]
    calc g t * Real.exp (-(δ n * t ^ 2 / 2)) ≤ 1 * Real.exp (-(δ n * t ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right (hg1 t) (Real.exp_pos _).le
      _ = Real.exp (-(δ n / 2) * t ^ 2) := by rw [one_mul]; congr 1; ring
  have hFle : ∀ n, ∫⁻ t, F n t ≤ ENNReal.ofReal (2 * π * D) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hFint n)
      (ae_of_all _ fun t => mul_nonneg (hg0 t) (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal (hstep (hδpos n))
  have hlim : ∀ t, liminf (fun n => F n t) atTop = ENNReal.ofReal (g t) := by
    intro t
    refine Tendsto.liminf_eq (ENNReal.tendsto_ofReal ?_)
    have hc : Continuous fun s : ℝ => g t * Real.exp (-(s * t ^ 2 / 2)) := by fun_prop
    have h0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := (hc.tendsto 0).comp h0
    simp only [zero_mul, zero_div, neg_zero, Real.exp_zero, mul_one] at h1
    exact h1
  have hFmeas : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp (hgm.mul (by fun_prop))
  have hlint : ∫⁻ t, ENNReal.ofReal (g t) ≤ ENNReal.ofReal (2 * π * D) := by
    calc ∫⁻ t, ENNReal.ofReal (g t) = ∫⁻ t, liminf (fun n => F n t) atTop := by
          simp_rw [hlim]
      _ ≤ liminf (fun n => ∫⁻ t, F n t) atTop := lintegral_liminf_le hFmeas
      _ ≤ _ := liminf_le_of_frequently_le' (Frequently.of_forall hFle)
  have hgint : Integrable g := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hgint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable]
  calc _ ≤ (ENNReal.ofReal (2 * π * D)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = 2 * π * D := ENNReal.toReal_ofReal (by positivity)

end

end PGM
