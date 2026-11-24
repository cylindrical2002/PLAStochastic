import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# A Plancherel inequality for integrable functions

For `f : ℝ → ℂ` integrable, `lineFourier f t = ∫ e^{i t x} f(x) dx`, and

  `∫ |f̂(t)|² dt ≤ 2π ∫ |f(x)|² dx`   (`lintegral_norm_sq_lineFourier_le`).

The proof does not use the `L²` Fourier transform: for a Gaussian weight `e^{-ε t²}`, Fubini
turns `∫ |f̂|² e^{-ε t²}` into `∫∫ f(x) f̄(y) k_ε(x - y)` with the positive kernel
`k_ε(z) = √(π/ε) e^{-z²/(4ε)}` of total mass `2π`; then `|f(x) f(y)| ≤ (|f(x)|² + |f(y)|²)/2`
bounds it by `2π ∫ |f|²`, and Fatou's lemma removes the weight.
-/

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped ENNReal

namespace PGM.WienerHopf

/-- The Fourier transform along the imaginary axis, `t ↦ ∫ e^{i t x} f(x) dx`. -/
def lineFourier (f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ x : ℝ, cexp (I * t * x) * f x

theorem norm_cexp_I_mul_mul (t x : ℝ) : ‖cexp (I * t * x)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_lineFourier_le (f : ℝ → ℂ) (t : ℝ) : ‖lineFourier f t‖ ≤ ∫ x, ‖f x‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; funext x
  rw [norm_mul, norm_cexp_I_mul_mul, one_mul]

theorem continuous_lineFourier {f : ℝ → ℂ} (hf : Integrable f) : Continuous (lineFourier f) := by
  refine continuous_of_dominated (bound := fun x => ‖f x‖) (fun t => ?_) (fun t => ?_) hf.norm ?_
  · exact ((by fun_prop : Continuous fun x : ℝ => cexp (I * t * x)).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_cexp_I_mul_mul, one_mul]
  · exact Filter.Eventually.of_forall fun x => by fun_prop

/-! ### The Gaussian kernel -/

/-- `k_ε(z) = √(π/ε) e^{-z²/(4ε)}`. -/
def gaussKernel (ε z : ℝ) : ℝ := √(Real.pi / ε) * Real.exp (-z ^ 2 / (4 * ε))

theorem gaussKernel_nonneg (ε z : ℝ) : 0 ≤ gaussKernel ε z :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le

theorem integral_gauss_exp {ε : ℝ} (hε : 0 < ε) (z : ℝ) :
    ∫ t : ℝ, cexp (I * z * t) * cexp (-(ε : ℂ) * t ^ 2) = (gaussKernel ε z : ℂ) := by
  have h := fourierIntegral_gaussian (b := (ε : ℂ)) (by simpa using hε) (z : ℂ)
  rw [h, gaussKernel, Complex.ofReal_mul]
  congr 1
  · rw [show (Real.pi : ℂ) / ε = ((Real.pi / ε : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]
  · rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring

theorem integral_gaussKernel {ε : ℝ} (hε : 0 < ε) : ∫ z, gaussKernel ε z = 2 * Real.pi := by
  unfold gaussKernel
  rw [integral_const_mul]
  have h := integral_gaussian (1 / (4 * ε))
  have hfun : (fun z : ℝ => Real.exp (-z ^ 2 / (4 * ε))) =
      fun z => Real.exp (-(1 / (4 * ε)) * z ^ 2) := by
    funext z; congr 1; field_simp
  rw [hfun, h, ← Real.sqrt_mul (by positivity)]
  rw [show Real.pi / ε * (Real.pi / (1 / (4 * ε))) = (2 * Real.pi) ^ 2 by field_simp; ring]
  exact Real.sqrt_sq (by positivity)

theorem integrable_gaussKernel {ε : ℝ} (hε : 0 < ε) : Integrable (gaussKernel ε) := by
  unfold gaussKernel
  refine ((integrable_exp_neg_mul_sq (b := 1 / (4 * ε)) (by positivity)).const_mul
    (√(Real.pi / ε))).congr ?_
  exact Filter.Eventually.of_forall fun z => by
    simp only
    congr 2; field_simp

theorem lintegral_gaussKernel_sub {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∫⁻ y, ENNReal.ofReal (gaussKernel ε (x - y)) = ENNReal.ofReal (2 * Real.pi) := by
  rw [← integral_gaussKernel hε, ofReal_integral_eq_lintegral_ofReal (integrable_gaussKernel hε)
    (Filter.Eventually.of_forall fun z => gaussKernel_nonneg ε z)]
  exact lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (gaussKernel ε z)) x

/-! ### The Plancherel inequality -/

variable {f : ℝ → ℂ}

theorem sq_norm_lineFourier_eq (t : ℝ) :
    ((‖lineFourier f t‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, cexp (I * t * ((p.1 - p.2 : ℝ) : ℂ)) * (f p.1 * (starRingEnd ℂ) (f p.2))
        ∂(volume.prod volume) := by
  have h1 : ((‖lineFourier f t‖ ^ 2 : ℝ) : ℂ) =
      lineFourier f t * (starRingEnd ℂ) (lineFourier f t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1, lineFourier, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [map_mul, ← Complex.exp_conj, Complex.conj_I, Complex.conj_ofReal]
  rw [Complex.ofReal_sub, show I * t * ((p.1 : ℂ) - p.2) = I * t * p.1 + -I * t * p.2 by ring,
    Complex.exp_add]
  ring

theorem lintegral_norm_sq_lineFourier_mul_gauss_le (hf : Integrable f) (hfm : Measurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ t, ENNReal.ofReal (‖lineFourier f t‖ ^ 2 * Real.exp (-ε * t ^ 2)) ≤
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
  set Φ : ℝ → ℝ × ℝ → ℂ := fun t p =>
    cexp (-(ε : ℂ) * t ^ 2) * (cexp (I * t * ((p.1 - p.2 : ℝ) : ℂ)) *
      (f p.1 * (starRingEnd ℂ) (f p.2)))
  set Ψ : ℝ × ℝ → ℂ := fun p => f p.1 * (starRingEnd ℂ) (f p.2) * (gaussKernel ε (p.1 - p.2) : ℂ)
  have hgauss : Integrable fun t : ℝ => Real.exp (-ε * t ^ 2) := integrable_exp_neg_mul_sq hε
  have hΦm : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun q : ℝ × (ℝ × ℝ) => f q.2.1 :=
      hfm.comp (measurable_fst.comp measurable_snd)
    have h2 : Measurable fun q : ℝ × (ℝ × ℝ) => (starRingEnd ℂ) (f q.2.2) :=
      Complex.continuous_conj.measurable.comp (hfm.comp (measurable_snd.comp measurable_snd))
    have h3 : Measurable fun q : ℝ × (ℝ × ℝ) => cexp (-(ε : ℂ) * q.1 ^ 2) := by fun_prop
    have h4 : Measurable fun q : ℝ × (ℝ × ℝ) => cexp (I * q.1 * ((q.2.1 - q.2.2 : ℝ) : ℂ)) := by
      fun_prop
    exact h3.mul (h4.mul (h1.mul h2))
  have hΦi : Integrable (Function.uncurry Φ) (volume.prod (volume.prod volume)) := by
    have hdom : Integrable (fun q : ℝ × (ℝ × ℝ) => Real.exp (-ε * q.1 ^ 2) *
        (‖f q.2.1‖ * ‖f q.2.2‖)) (volume.prod (volume.prod volume)) :=
      hgauss.mul_prod (hf.norm.mul_prod hf.norm)
    refine hdom.mono' hΦm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    simp only [Φ, Function.uncurry_def, norm_mul, norm_cexp_I_mul_mul, Complex.norm_conj, one_mul]
    rw [Complex.norm_exp]
    apply le_of_eq
    congr 2
    simp only [neg_mul, Complex.neg_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  have hΦΨ : ∀ p : ℝ × ℝ, ∫ t, Φ t p = Ψ p := by
    intro p
    simp only [Φ, Ψ]
    rw [← integral_gauss_exp hε (p.1 - p.2), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [show I * (t : ℂ) * ((p.1 - p.2 : ℝ) : ℂ) = I * ((p.1 - p.2 : ℝ) : ℂ) * t by ring]
    ring
  have hswap := integral_integral_swap hΦi
  have hleft : ∫ t, ∫ p, Φ t p ∂(volume.prod volume) =
      ((∫ t, ‖lineFourier f t‖ ^ 2 * Real.exp (-ε * t ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Φ]
    rw [integral_const_mul, ← sq_norm_lineFourier_eq t, Complex.ofReal_mul, mul_comm,
      Complex.ofReal_exp]
    push_cast; ring_nf
  have hright : ∫ p, (∫ t, Φ t p) ∂(volume.prod volume) = ∫ p, Ψ p ∂(volume.prod volume) :=
    integral_congr_ae (Filter.Eventually.of_forall hΦΨ)
  have hΨi : Integrable Ψ (volume.prod volume) :=
    hΦi.integral_prod_right.congr (Filter.Eventually.of_forall fun p => hΦΨ p)
  have hreal : ∫ t, ‖lineFourier f t‖ ^ 2 * Real.exp (-ε * t ^ 2) ≤
      ∫ p, ‖Ψ p‖ ∂(volume.prod volume) := by
    have h := hswap
    rw [hleft, hright] at h
    have := norm_integral_le_integral_norm (μ := volume.prod volume) Ψ
    rw [← h, Complex.norm_real, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hI0 : 0 ≤ ∫ t, ‖lineFourier f t‖ ^ 2 * Real.exp (-ε * t ^ 2) :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hint : Integrable fun t => ‖lineFourier f t‖ ^ 2 * Real.exp (-ε * t ^ 2) := by
    refine (hgauss.const_mul ((∫ x, ‖f x‖) ^ 2)).mono'
      (((continuous_lineFourier hf).norm.pow 2).aestronglyMeasurable.mul
        hgauss.aestronglyMeasurable) (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
      (norm_lineFourier_le f t) 2) (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun t =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  calc ENNReal.ofReal (∫ t, ‖lineFourier f t‖ ^ 2 * Real.exp (-ε * t ^ 2))
      ≤ ENNReal.ofReal (∫ p, ‖Ψ p‖ ∂(volume.prod volume)) := ENNReal.ofReal_le_ofReal hreal
    _ = ∫⁻ p, ENNReal.ofReal ‖Ψ p‖ ∂(volume.prod volume) :=
        ofReal_integral_eq_lintegral_ofReal hΨi.norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    _ ≤ ∫⁻ p, (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (‖f p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2)) +
          ENNReal.ofReal (1 / 2) * ENNReal.ofReal (‖f p.2‖ ^ 2 * gaussKernel ε (p.1 - p.2)))
          ∂(volume.prod volume) := by
        refine lintegral_mono fun p => ?_
        have hk := gaussKernel_nonneg ε (p.1 - p.2)
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        simp only [Ψ, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hk]
        nlinarith [mul_nonneg hk (sq_nonneg (‖f p.1‖ - ‖f p.2‖))]
    _ = ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) +
          ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (2 * Real.pi) *
            ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2)) := by
        have hm1 : Measurable fun p : ℝ × ℝ =>
            ENNReal.ofReal (‖f p.1‖ ^ 2 * gaussKernel ε (p.1 - p.2)) :=
          ENNReal.measurable_ofReal.comp (((hfm.comp measurable_fst).norm.pow_const 2).mul
            (by unfold gaussKernel; fun_prop))
        have hm2 : Measurable fun p : ℝ × ℝ =>
            ENNReal.ofReal (‖f p.2‖ ^ 2 * gaussKernel ε (p.1 - p.2)) :=
          ENNReal.measurable_ofReal.comp (((hfm.comp measurable_snd).norm.pow_const 2).mul
            (by unfold gaussKernel; fun_prop))
        rw [lintegral_add_left (hm1.const_mul _), lintegral_const_mul _ hm1,
          lintegral_const_mul _ hm2]
        congr 2
        · rw [lintegral_prod _ hm1.aemeasurable, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun x => ?_
          simp only
          simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
          rw [lintegral_const_mul _ (by unfold gaussKernel; fun_prop), lintegral_gaussKernel_sub hε,
            mul_comm]
        · rw [lintegral_prod_symm _ hm2.aemeasurable,
            ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          simp only
          simp_rw [ENNReal.ofReal_mul (sq_nonneg _)]
          rw [lintegral_const_mul _ (by unfold gaussKernel; fun_prop), mul_comm]
          congr 1
          have h1 := lintegral_sub_right_eq_self (μ := volume)
            (fun z => ENNReal.ofReal (gaussKernel ε z)) y
          have h2 := lintegral_gaussKernel_sub hε 0
          simp only [zero_sub] at h2
          rw [lintegral_neg_eq_self (μ := volume) (fun z => ENNReal.ofReal (gaussKernel ε z))] at h2
          rw [h1, h2]
    _ = ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
        rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
          show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, ENNReal.ofReal_one, one_mul]

/-- **Plancherel inequality**: `∫ |f̂|² ≤ 2π ∫ |f|²` for integrable measurable `f`. -/
theorem lintegral_norm_sq_lineFourier_le (hf : Integrable f) (hfm : Measurable f) :
    ∫⁻ t, ENNReal.ofReal (‖lineFourier f t‖ ^ 2) ≤
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) := by
  set F : ℕ → ℝ → ℝ≥0∞ := fun n t =>
    ENNReal.ofReal (‖lineFourier f t‖ ^ 2 * Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2))
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ENNReal.measurable_ofReal.comp ((((continuous_lineFourier hf).norm.pow 2).mul
      (by fun_prop)).measurable)
  have hlim : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (ENNReal.ofReal (‖lineFourier f t‖ ^ 2))) := by
    intro t
    refine ENNReal.tendsto_ofReal ?_
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 : Tendsto (fun n : ℕ => Real.exp (-(1 / ((n : ℝ) + 1)) * t ^ 2)) atTop (𝓝 1) := by
      have := ((h0.neg.mul_const (t ^ 2)).rexp)
      simpa using this
    simpa using h1.const_mul (‖lineFourier f t‖ ^ 2)
  calc ∫⁻ t, ENNReal.ofReal (‖lineFourier f t‖ ^ 2)
      = ∫⁻ t, liminf (fun n => F n t) atTop :=
        lintegral_congr fun t => ((hlim t).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ t, F n t) atTop := lintegral_liminf_le hFm
    _ ≤ ENNReal.ofReal (2 * Real.pi) * ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ 2) :=
        liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun n =>
          lintegral_norm_sq_lineFourier_mul_gauss_le hf hfm (by positivity))

end PGM.WienerHopf
