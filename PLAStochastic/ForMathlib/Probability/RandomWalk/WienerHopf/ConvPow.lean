import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.Plancherel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Convolution powers of a complex density with an exponential envelope

`IsExpDensity g D θ`: `g : ℝ → ℂ` is measurable, vanishes on `(-∞, 0]` and `|g(x)| ≤ D e^{-θ x}`.

* `convC f h x = ∫ f(y) h(x - y) dy`; `convPow g n = g^{*(n+1)}`;
  `renewalDensity g = ∑_{n ≥ 1} g^{*n}`.
* `norm_convPow_le`: `|g^{*(n+1)}(x)| ≤ D^{n+1} xⁿ/n! e^{-θ x}` (and `0` on `x ≤ 0`), so the
  renewal series converges absolutely everywhere.
* `lintegral_weight_convC_le`: `∫ e^{-c x}|f ⋆ h| ≤ (∫ e^{-c x}|f|)(∫ e^{-c x}|h|)`.
* `laplaceC_convC`: on a vertical line where both are weighted-integrable, the Laplace transform
  `A_f(ζ) = ∫ e^{ζ x} f(x) dx` is multiplicative.
-/

noncomputable section

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal Nat

namespace PGM.WienerHopf

/-- `(f ⋆ h)(x) = ∫ f(y) h(x - y) dy`. -/
def convC (f h : ℝ → ℂ) (x : ℝ) : ℂ := ∫ y, f y * h (x - y)

/-- `convPow g n = g^{*(n+1)}`. -/
def convPow (g : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => g
  | n + 1 => convC g (convPow g n)

/-- The renewal density `u = ∑_{n ≥ 1} g^{*n}`. -/
def renewalDensity (g : ℝ → ℂ) (x : ℝ) : ℂ := ∑' n, convPow g n x

/-- The Laplace transform `A(ζ) = ∫ e^{ζ x} g(x) dx`. -/
def laplaceC (g : ℝ → ℂ) (ζ : ℂ) : ℂ := ∫ x : ℝ, cexp (ζ * x) * g x

/-- A complex density on `(0, ∞)` with the envelope `D e^{-θ x}`. -/
structure IsExpDensity (g : ℝ → ℂ) (D θ : ℝ) : Prop where
  measurable : Measurable g
  eq_zero_of_nonpos : ∀ x, x ≤ 0 → g x = 0
  norm_le : ∀ x, ‖g x‖ ≤ D * Real.exp (-θ * x)

variable {g : ℝ → ℂ} {D θ : ℝ}

theorem IsExpDensity.nonneg_D (hg : IsExpDensity g D θ) : 0 ≤ D := by
  have := (norm_nonneg _).trans (hg.norm_le 0)
  simpa using this

theorem measurable_convC {f h : ℝ → ℂ} (hf : Measurable f) (hh : Measurable h) :
    Measurable (convC f h) := by
  have : StronglyMeasurable (Function.uncurry fun x y : ℝ => f y * h (x - y)) :=
    ((hf.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact this.integral_prod_right.measurable

theorem convC_eq_zero_of_nonpos {f h : ℝ → ℂ} (hf : ∀ y, y ≤ 0 → f y = 0)
    (hh : ∀ z, z ≤ 0 → h z = 0) {x : ℝ} (hx : x ≤ 0) : convC f h x = 0 := by
  unfold convC
  have : (fun y => f y * h (x - y)) = fun _ => 0 := by
    funext y
    rcases le_or_gt y 0 with hy | hy
    · rw [hf y hy, zero_mul]
    · rw [hh (x - y) (by linarith), mul_zero]
  rw [this, integral_zero]

theorem measurable_convPow (hg : IsExpDensity g D θ) (n : ℕ) : Measurable (convPow g n) := by
  induction n with
  | zero => exact hg.measurable
  | succ n ih => exact measurable_convC hg.measurable ih

theorem convPow_eq_zero_of_nonpos (hg : IsExpDensity g D θ) (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    convPow g n x = 0 := by
  induction n generalizing x with
  | zero => exact hg.eq_zero_of_nonpos x hx
  | succ n ih => exact convC_eq_zero_of_nonpos hg.eq_zero_of_nonpos (fun z hz => ih hz) hx

theorem integral_Ioo_sub_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    ∫ y in Ioo 0 x, (x - y) ^ n = x ^ (n + 1) / (n + 1) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    intervalIntegral.integral_comp_sub_left (fun y => y ^ n) x, integral_pow]
  simp

/-- `|g^{*(n+1)}(x)| ≤ D^{n+1} xⁿ/n! e^{-θ x}` for `x > 0`. -/
theorem norm_convPow_le (hg : IsExpDensity g D θ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖convPow g n x‖ ≤ D ^ (n + 1) * x ^ n / n ! * Real.exp (-θ * x) := by
  have hD := hg.nonneg_D
  induction n generalizing x with
  | zero => simpa [convPow] using hg.norm_le x
  | succ n ih =>
    set B : ℝ → ℝ := (Ioo 0 x).indicator fun y =>
      D ^ (n + 2) / n ! * Real.exp (-θ * x) * (x - y) ^ n
    have hB0 : ∀ y, 0 ≤ B y := fun y => Set.indicator_nonneg (fun y hy => by
      have : 0 ≤ x - y := by simp only [mem_Ioo] at hy; linarith
      positivity) y
    have hpt : ∀ y, ‖g y‖ * ‖convPow g n (x - y)‖ ≤ B y := by
      intro y
      by_cases hy : y ∈ Ioo 0 x
      · obtain ⟨hy0, hyx⟩ := hy
        rw [show B y = D ^ (n + 2) / n ! * Real.exp (-θ * x) * (x - y) ^ n from
          indicator_of_mem (show y ∈ Ioo 0 x from ⟨hy0, hyx⟩) _]
        calc ‖g y‖ * ‖convPow g n (x - y)‖
            ≤ (D * Real.exp (-θ * y)) * (D ^ (n + 1) * (x - y) ^ n / n ! *
                Real.exp (-θ * (x - y))) :=
              mul_le_mul (hg.norm_le y) (ih (by linarith)) (norm_nonneg _) (by positivity)
          _ = D ^ (n + 2) / n ! * Real.exp (-θ * x) * (x - y) ^ n := by
              rw [show -θ * x = -θ * y + -θ * (x - y) by ring, Real.exp_add]; ring
      · rw [show B y = 0 from indicator_of_notMem hy _]
        simp only [mem_Ioo, not_and_or, not_lt] at hy
        rcases hy with hy | hy
        · rw [hg.eq_zero_of_nonpos y hy, norm_zero, zero_mul]
        · rw [convPow_eq_zero_of_nonpos hg n (by linarith), norm_zero, mul_zero]
    have hBi : Integrable B := by
      refine (IntegrableOn.integrable_indicator ?_ measurableSet_Ioo)
      exact ((by fun_prop : Continuous fun y : ℝ =>
        D ^ (n + 2) / n ! * Real.exp (-θ * x) * (x - y) ^ n).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self
    calc ‖convPow g (n + 1) x‖ = ‖∫ y, g y * convPow g n (x - y)‖ := rfl
      _ ≤ ∫ y, ‖g y * convPow g n (x - y)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, B y := integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          hBi (Filter.Eventually.of_forall fun y => by
            show ‖g y * convPow g n (x - y)‖ ≤ B y
            rw [norm_mul]; exact hpt y)
      _ = D ^ (n + 2) / n ! * Real.exp (-θ * x) * (x ^ (n + 1) / (n + 1)) := by
          rw [integral_indicator measurableSet_Ioo, integral_const_mul,
            integral_Ioo_sub_pow x hx.le n]
      _ = D ^ (n + 1 + 1) * x ^ (n + 1) / (n + 1)! * Real.exp (-θ * x) := by
          rw [Nat.factorial_succ]; push_cast; field_simp

/-- The renewal series converges absolutely at every point. -/
theorem summable_norm_convPow (hg : IsExpDensity g D θ) (x : ℝ) :
    Summable fun n => ‖convPow g n x‖ := by
  rcases le_or_gt x 0 with hx | hx
  · simp [convPow_eq_zero_of_nonpos hg _ hx]
  · refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_convPow_le hg n hx) ?_
    have := (Real.summable_pow_div_factorial (D * x)).mul_left (D * Real.exp (-θ * x))
    refine this.congr fun n => ?_
    rw [mul_pow]; ring

/-- On `(-∞, X]` the terms are bounded by `D^{n+1} Xⁿ/n!` (`θ ≥ 0`). -/
theorem norm_convPow_le_of_le (hg : IsExpDensity g D θ) (hθ : 0 ≤ θ) (n : ℕ) {x X : ℝ}
    (hxX : x ≤ X) : ‖convPow g n x‖ ≤ D ^ (n + 1) * (max X 0) ^ n / n ! := by
  have hD := hg.nonneg_D
  rcases le_or_gt x 0 with hx | hx
  · rw [convPow_eq_zero_of_nonpos hg n hx, norm_zero]; positivity
  · calc ‖convPow g n x‖ ≤ D ^ (n + 1) * x ^ n / n ! * Real.exp (-θ * x) := norm_convPow_le hg n hx
      _ ≤ D ^ (n + 1) * (max X 0) ^ n / n ! * 1 := by
          gcongr
          · exact le_max_of_le_left hxX
          · exact Real.exp_le_one_iff.mpr (by nlinarith)
      _ = _ := mul_one _

/-! ### Weighted `L¹` norms and transforms -/

theorem ofReal_mul_norm_integral_le (c x : ℝ) (F : ℝ → ℂ) :
    ENNReal.ofReal (Real.exp (-c * x) * ‖∫ y, F y‖) ≤
      ∫⁻ y, ENNReal.ofReal (Real.exp (-c * x) * ‖F y‖) := by
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc ENNReal.ofReal (Real.exp (-c * x)) * ENNReal.ofReal ‖∫ y, F y‖
      ≤ ENNReal.ofReal (Real.exp (-c * x)) * ∫⁻ y, ENNReal.ofReal ‖F y‖ := by
        gcongr
        rw [ofReal_norm]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        simp_rw [ofReal_norm]
    _ = ∫⁻ y, ENNReal.ofReal (Real.exp (-c * x) * ‖F y‖) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine lintegral_congr fun y => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- `∫ e^{-c x}|f ⋆ h| ≤ (∫ e^{-c x}|f|)(∫ e^{-c x}|h|)`. -/
theorem lintegral_weight_convC_le {f h : ℝ → ℂ} (hf : Measurable f) (hh : Measurable h) (c : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖convC f h x‖) ≤
      (∫⁻ y, ENNReal.ofReal (Real.exp (-c * y) * ‖f y‖)) *
        ∫⁻ z, ENNReal.ofReal (Real.exp (-c * z) * ‖h z‖) := by
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-c * p.1) * ‖f p.2 * h (p.1 - p.2)‖) := by
    refine ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      Real.exp (-c * p.1)).mul ?_)
    exact ((hf.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))).norm
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖convC f h x‖)
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-c * x) * ‖f y * h (x - y)‖) :=
        lintegral_mono fun x => ofReal_mul_norm_integral_le c x _
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖f y * h (x - y)‖) :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (Real.exp (-c * y) * ‖f y‖) *
          ∫⁻ z, ENNReal.ofReal (Real.exp (-c * z) * ‖h z‖) := by
        refine lintegral_congr fun y => ?_
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [← lintegral_sub_right_eq_self (μ := volume)
          (fun z => ENNReal.ofReal (Real.exp (-c * y) * ‖f y‖) *
            ENNReal.ofReal (Real.exp (-c * z) * ‖h z‖)) y]
        refine lintegral_congr fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity), norm_mul]
        congr 1
        rw [show -c * x = -c * y + -c * (x - y) by ring, Real.exp_add]; ring
    _ = _ := lintegral_mul_const _ (ENNReal.measurable_ofReal.comp
        ((by fun_prop : Measurable fun y : ℝ => Real.exp (-c * y)).mul hf.norm))

theorem norm_cexp_mul_ofReal' (ζ : ℂ) (x : ℝ) : ‖cexp (ζ * x)‖ = Real.exp (-(-ζ.re) * x) := by
  rw [Complex.norm_exp]; simp

/-- The weighted lower integral of `|e^{ζ x} f(y) h(x - y)|` over the plane factorizes. -/
theorem lintegral_prod_weight_eq {f h : ℝ → ℂ} (hf : Measurable f) (hh : Measurable h) (c : ℝ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (-c * p.1) * ‖f p.2 * h (p.1 - p.2)‖) ∂(volume.prod volume) =
      (∫⁻ y, ENNReal.ofReal (Real.exp (-c * y) * ‖f y‖)) *
        ∫⁻ z, ENNReal.ofReal (Real.exp (-c * z) * ‖h z‖) := by
  have hm : Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-c * p.1) * ‖f p.2 * h (p.1 - p.2)‖) := by
    refine ENNReal.measurable_ofReal.comp ((by fun_prop : Measurable fun p : ℝ × ℝ =>
      Real.exp (-c * p.1)).mul ?_)
    exact ((hf.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd))).norm
  have hfw' : Measurable fun y : ℝ => ENNReal.ofReal (Real.exp (-c * y) * ‖f y‖) :=
    ENNReal.measurable_ofReal.comp
      ((by fun_prop : Measurable fun y : ℝ => Real.exp (-c * y)).mul hf.norm)
  rw [lintegral_prod_symm _ hm.aemeasurable, ← lintegral_mul_const _ hfw']
  refine lintegral_congr fun y => ?_
  simp only
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [← lintegral_sub_right_eq_self (μ := volume)
    (fun z => ENNReal.ofReal (Real.exp (-c * y) * ‖f y‖) *
      ENNReal.ofReal (Real.exp (-c * z) * ‖h z‖)) y]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity), norm_mul]
  congr 1
  rw [show -c * x = -c * y + -c * (x - y) by ring, Real.exp_add]; ring

/-- The Laplace transform is multiplicative under convolution on a line `Re ζ = -c` where both
factors are weighted-integrable. -/
theorem laplaceC_convC {f h : ℝ → ℂ} (hf : Measurable f) (hh : Measurable h) {ζ : ℂ}
    (hfw : ∫⁻ y, ENNReal.ofReal (Real.exp (-(-ζ.re) * y) * ‖f y‖) ≠ ⊤)
    (hhw : ∫⁻ z, ENNReal.ofReal (Real.exp (-(-ζ.re) * z) * ‖h z‖) ≠ ⊤) :
    laplaceC (convC f h) ζ = laplaceC f ζ * laplaceC h ζ := by
  set c := -ζ.re
  set Φ : ℝ → ℝ → ℂ := fun x y => cexp (ζ * x) * (f y * h (x - y))
  have hΦm : Measurable (Function.uncurry Φ) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => cexp (ζ * p.1)).mul
      ((hf.comp measurable_snd).mul (hh.comp (measurable_fst.sub measurable_snd)))
  have hΦi : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    refine ⟨hΦm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    have : ∀ p : ℝ × ℝ, ‖Function.uncurry Φ p‖ =
        Real.exp (-c * p.1) * ‖f p.2 * h (p.1 - p.2)‖ := by
      intro p
      simp only [Φ, Function.uncurry_def, norm_mul, norm_cexp_mul_ofReal']
      rfl
    simp_rw [this]
    rw [lintegral_prod_weight_eq hf hh c]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hfw) (lt_top_iff_ne_top.mpr hhw)
  have hinner : ∀ y : ℝ, ∫ x : ℝ, cexp (ζ * x) * h (x - y) = cexp (ζ * y) * laplaceC h ζ := by
    intro y
    rw [laplaceC, ← integral_const_mul]
    rw [← integral_sub_right_eq_self (μ := volume)
      (fun z : ℝ => cexp (ζ * y) * (cexp (ζ * z) * h z)) y]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← mul_assoc, ← Complex.exp_add, sub_eq_add_neg]
    congr 2
    push_cast; ring
  calc laplaceC (convC f h) ζ = ∫ x, ∫ y, Φ x y := by
        unfold laplaceC convC
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => (integral_const_mul _ _).symm)
    _ = ∫ y, ∫ x, Φ x y := integral_integral_swap hΦi
    _ = ∫ y : ℝ, cexp (ζ * y) * f y * laplaceC h ζ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [Φ]
        rw [show (fun x : ℝ => cexp (ζ * x) * (f y * h (x - y))) =
          fun x : ℝ => f y * (cexp (ζ * x) * h (x - y)) by funext x; ring, integral_const_mul,
          hinner y]
        ring
    _ = laplaceC f ζ * laplaceC h ζ := by rw [integral_mul_const]; rfl

theorem lintegral_weight_convPow_le (hg : IsExpDensity g D θ) (c : ℝ) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖convPow g n x‖) ≤
      (∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖g x‖)) ^ (n + 1) := by
  induction n with
  | zero => simp only [convPow, zero_add, pow_one, le_refl]
  | succ n ih =>
    calc ∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖convPow g (n + 1) x‖)
        ≤ (∫⁻ y, ENNReal.ofReal (Real.exp (-c * y) * ‖g y‖)) *
            ∫⁻ z, ENNReal.ofReal (Real.exp (-c * z) * ‖convPow g n z‖) :=
          lintegral_weight_convC_le hg.measurable (measurable_convPow hg n) c
      _ ≤ (∫⁻ y, ENNReal.ofReal (Real.exp (-c * y) * ‖g y‖)) *
            (∫⁻ x, ENNReal.ofReal (Real.exp (-c * x) * ‖g x‖)) ^ (n + 1) := by gcongr
      _ = _ := by rw [pow_succ' _ (n + 1)]

theorem laplaceC_convPow (hg : IsExpDensity g D θ) {ζ : ℂ}
    (hw : ∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖g x‖) ≠ ⊤) (n : ℕ) :
    laplaceC (convPow g n) ζ = laplaceC g ζ ^ (n + 1) := by
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    rw [convPow, laplaceC_convC hg.measurable (measurable_convPow hg n) hw
      (ne_top_of_le_ne_top (ENNReal.pow_ne_top hw) (lintegral_weight_convPow_le hg _ n)), ih,
      pow_succ' (laplaceC g ζ) (n + 1)]

theorem norm_laplaceC_le {f : ℝ → ℂ} (ζ : ℂ) :
    ‖laplaceC f ζ‖ ≤ (∫⁻ x, ENNReal.ofReal (Real.exp (-(-ζ.re) * x) * ‖f x‖)).toReal := by
  unfold laplaceC
  refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
  congr 1
  refine lintegral_congr fun x => ?_
  rw [norm_mul, norm_cexp_mul_ofReal']

end PGM.WienerHopf
