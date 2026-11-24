import PLAStochastic.ForMathlib.Analysis.Fourier.PlancherelIntegrable
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# WP4 `SurvivalBound`: the measure convolution `v y = ∫ u(y + β - a x) dρ(x)`

For a finite measure `ρ` on `ℝ`, reals `β, a` and `u : ℝ → ℂ` define the measure convolution
`kConv ρ β a u y = ∫ u(y + β - a x) dρ(x)`; the killed step of `PLAStochastic/Index/GEP/SurvivalBound/KilledRow/Defs.lean` is
`kStep J ρ β a u = 1_J · kConv ρ β a u`.

* Measurability (`measurable_kConv`), `L¹` (`integrable_kConv`) and `L²` (`memLp_two_kConv`) for
  `u` measurable in `L¹ ∩ L²`.  The `L²` bound is Cauchy–Schwarz in `x` for a.e. `y`
  (`kill_sq_integral_le`) and Tonelli: `∫ ‖v‖² ≤ ρ(ℝ)² ∫ ‖u‖²`.
* **Fourier transform** (`fourier_kConv`): with Mathlib's `𝓕 u ξ = ∫ e^{-2πiξy} u(y) dy` and
  `charFun ρ t = ∫ e^{itx} dρ(x)`,

  `𝓕 v ξ = e^{2πiξβ} · charFun ρ (-2πaξ) · 𝓕 u ξ`.

  Proof: Fubini on `(y, x) ↦ e^{-2πiξy} u(y + β - ax)` (integrable on `volume × ρ`,
  `kill_integrable_prod_shift`), and in `y` the translation `y ↦ y + (β - ax)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory FourierTransform Complex
open scoped Real

/-- The measure convolution `v y = ∫ u(y + β - a x) dρ(x)`. -/
def kConv (ρ : Measure ℝ) (β a : ℝ) (u : ℝ → ℂ) (y : ℝ) : ℂ := ∫ x, u (y + β - a * x) ∂ρ

/-- **Cauchy–Schwarz against a finite measure**: `(∫ N)² ≤ μ(univ) ∫ N²`. -/
theorem kill_sq_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {N : α → ℝ} (h1 : Integrable N μ) (h2 : Integrable (fun x => N x ^ 2) μ) :
    (∫ x, N x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, N x ^ 2 ∂μ := by
  set M := μ.real Set.univ with hM
  set m := ∫ x, N x ∂μ with hm
  have hM0 : 0 ≤ M := measureReal_nonneg
  have hexp : ∫ x, (M * N x - m) ^ 2 ∂μ = M * (M * ∫ x, N x ^ 2 ∂μ - m ^ 2) := by
    have e : (fun x => (M * N x - m) ^ 2) =
        fun x => (M ^ 2 * N x ^ 2 - (2 * M * m) * N x) + m ^ 2 := by
      funext x; ring
    have i1 : Integrable (fun x => M ^ 2 * N x ^ 2 - (2 * M * m) * N x) μ :=
      (h2.const_mul _).sub (h1.const_mul _)
    have i2 : Integrable (fun x => M ^ 2 * N x ^ 2) μ := h2.const_mul _
    have i3 : Integrable (fun x => (2 * M * m) * N x) μ := h1.const_mul _
    rw [e, integral_add i1 (integrable_const _), integral_sub i2 i3, integral_const_mul,
      integral_const_mul, integral_const, smul_eq_mul, ← hm, ← hM]
    ring
  have hnn : 0 ≤ ∫ x, (M * N x - m) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  rw [hexp] at hnn
  rcases hM0.lt_or_eq with hpos | hzero
  · by_contra hc
    rw [not_le] at hc
    have := mul_neg_of_pos_of_neg hpos (by linarith : M * ∫ x, N x ^ 2 ∂μ - m ^ 2 < 0)
    linarith
  · have hμ : μ = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      have : μ.real Set.univ = 0 := by rw [← hM, ← hzero]
      rwa [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)] at this
    have hm0 : m = 0 := by rw [hm, hμ, integral_zero_measure]
    rw [hm0, ← hzero]; simp

variable {E : Type*} [NormedAddCommGroup E]

/-- Integrability of `(y, x) ↦ f(y + β - a x)` on `volume × ρ`, `ρ` finite. -/
theorem kill_integrable_prod_shift {ρ : Measure ℝ} [IsFiniteMeasure ρ] {f : ℝ → E}
    (hfm : StronglyMeasurable f) (hf : Integrable f) (β a : ℝ) :
    Integrable (fun p : ℝ × ℝ => f (p.1 + β - a * p.2)) ((volume : Measure ℝ).prod ρ) := by
  have hmeas : StronglyMeasurable (fun p : ℝ × ℝ => f (p.1 + β - a * p.2)) :=
    hfm.comp_measurable (by fun_prop)
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall fun x => ?_
    have h := hf.comp_add_right (β - a * x)
    simp only [add_sub_assoc] at h ⊢
    exact h
  · have hc : ∀ x : ℝ, ∫ y, ‖f (y + β - a * x)‖ = ∫ y, ‖f y‖ := by
      intro x
      simp only [add_sub_assoc]
      exact integral_add_right_eq_self (fun y => ‖f y‖) (β - a * x)
    simp only [hc]
    exact integrable_const _

theorem kill_measurable_uncurry_shift {u : ℝ → ℂ} (hu : Measurable u) (β a : ℝ) :
    Measurable (fun p : ℝ × ℝ => u (p.1 + β - a * p.2)) :=
  hu.comp (by fun_prop)

/-- The measure convolution of a measurable function is strongly measurable. -/
theorem stronglyMeasurable_kConv (ρ : Measure ℝ) [SFinite ρ] {u : ℝ → ℂ} (hu : Measurable u)
    (β a : ℝ) : StronglyMeasurable (kConv ρ β a u) := by
  have h : StronglyMeasurable (Function.uncurry fun (y x : ℝ) => u (y + β - a * x)) :=
    (kill_measurable_uncurry_shift hu β a).stronglyMeasurable
  exact h.integral_prod_right

theorem measurable_kConv (ρ : Measure ℝ) [SFinite ρ] {u : ℝ → ℂ} (hu : Measurable u)
    (β a : ℝ) : Measurable (kConv ρ β a u) :=
  (stronglyMeasurable_kConv ρ hu β a).measurable

/-- The measure convolution of an integrable function is integrable. -/
theorem integrable_kConv (ρ : Measure ℝ) [IsFiniteMeasure ρ] {u : ℝ → ℂ} (hu : Measurable u)
    (h1 : Integrable u) (β a : ℝ) : Integrable (kConv ρ β a u) :=
  (kill_integrable_prod_shift hu.stronglyMeasurable h1 β a).integral_prod_left

/-- **`L²` bound for the measure convolution.**  For `u` measurable in `L¹ ∩ L²`,
`v = kConv ρ β a u` is in `L²` and `∫ ‖v‖² ≤ ρ(ℝ)² ∫ ‖u‖²`. -/
theorem memLp_two_kConv (ρ : Measure ℝ) [IsFiniteMeasure ρ] {u : ℝ → ℂ} (hu : Measurable u)
    (h1 : Integrable u) (h2 : MemLp u 2) (β a : ℝ) :
    MemLp (kConv ρ β a u) 2 ∧
      ∫ y, ‖kConv ρ β a u y‖ ^ 2 ≤ ρ.real Set.univ ^ 2 * ∫ y, ‖u y‖ ^ 2 := by
  set M := ρ.real Set.univ with hM
  have hsq : Integrable (fun y => ‖u y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).1 h2
  have hsqm : StronglyMeasurable (fun y => ‖u y‖ ^ 2) :=
    (hu.norm.pow_const 2).stronglyMeasurable
  have hΦ := kill_integrable_prod_shift (ρ := ρ) hsqm hsq β a
  have hF := kill_integrable_prod_shift (ρ := ρ) hu.stronglyMeasurable h1 β a
  -- the majorant `H y = M ∫ ‖u (y + β - a x)‖² dρ`
  set H : ℝ → ℝ := fun y => M * ∫ x, ‖u (y + β - a * x)‖ ^ 2 ∂ρ with hH
  have hHi : Integrable H := hΦ.integral_prod_left.const_mul M
  have hHint : ∫ y, H y = M ^ 2 * ∫ y, ‖u y‖ ^ 2 := by
    rw [hH, integral_const_mul]
    have := integral_prod_symm (fun p : ℝ × ℝ => ‖u (p.1 + β - a * p.2)‖ ^ 2) hΦ
    rw [integral_prod _ hΦ] at this
    simp only at this
    rw [this]
    have hc : ∀ x : ℝ, ∫ y, ‖u (y + β - a * x)‖ ^ 2 = ∫ y, ‖u y‖ ^ 2 := by
      intro x
      simp only [add_sub_assoc]
      exact integral_add_right_eq_self (fun y => ‖u y‖ ^ 2) (β - a * x)
    simp only [hc, integral_const, smul_eq_mul, ← hM]
    ring
  have hbound : ∀ᵐ y ∂(volume : Measure ℝ), ‖kConv ρ β a u y‖ ^ 2 ≤ H y := by
    filter_upwards [hΦ.prod_right_ae, hF.prod_right_ae] with y hy2 hy1
    have hn1 : Integrable (fun x => ‖u (y + β - a * x)‖) ρ := hy1.norm
    have hcs := kill_sq_integral_le hn1 hy2
    have hle : ‖kConv ρ β a u y‖ ≤ ∫ x, ‖u (y + β - a * x)‖ ∂ρ :=
      norm_integral_le_integral_norm _
    calc ‖kConv ρ β a u y‖ ^ 2 ≤ (∫ x, ‖u (y + β - a * x)‖ ∂ρ) ^ 2 := by gcongr
      _ ≤ H y := hcs
  have hvm := measurable_kConv ρ hu β a
  have hvi : Integrable (fun y => ‖kConv ρ β a u y‖ ^ 2) := by
    refine hHi.mono' (hvm.norm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hbound] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hy
  refine ⟨(memLp_two_iff_integrable_sq_norm hvm.aestronglyMeasurable).2 hvi, ?_⟩
  rw [← hHint]
  exact integral_mono_ae hvi hHi hbound

/-- **Fourier transform of the measure convolution.**  For `ρ` finite and `u` measurable and
integrable, `𝓕 (kConv ρ β a u) ξ = e^{2πiξβ} · charFun ρ (-2πaξ) · 𝓕 u ξ`. -/
theorem fourier_kConv (ρ : Measure ℝ) [IsFiniteMeasure ρ] {u : ℝ → ℂ} (hu : Measurable u)
    (h1 : Integrable u) (β a ξ : ℝ) :
    𝓕 (kConv ρ β a u) ξ =
      Complex.exp (↑(2 * π * ξ * β) * I) * charFun ρ (-(2 * π * a * ξ)) * 𝓕 u ξ := by
  have hF := kill_integrable_prod_shift (ρ := ρ) hu.stronglyMeasurable h1 β a
  set e : ℝ → ℂ := fun y => Complex.exp (↑(-2 * π * y * ξ) * I) with he
  have hen : ∀ y, ‖e y‖ = 1 := fun y => by rw [he]; exact Complex.norm_exp_ofReal_mul_I _
  have hG : Integrable (fun p : ℝ × ℝ => e p.1 * u (p.1 + β - a * p.2))
      ((volume : Measure ℝ).prod ρ) := by
    refine hF.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine (Continuous.aestronglyMeasurable ?_).mul hF.aestronglyMeasurable
      rw [he]; fun_prop
    · rw [norm_mul, hen, one_mul]
  rw [Real.fourier_real_eq_integral_exp_smul]
  have h1' : ∀ y, Complex.exp (↑(-2 * π * y * ξ) * I) • kConv ρ β a u y =
      ∫ x, e y * u (y + β - a * x) ∂ρ := by
    intro y
    rw [kConv, smul_eq_mul, ← integral_const_mul]
  simp only [h1']
  rw [integral_integral_swap hG]
  -- the inner integral in `y`
  have hinner : ∀ x : ℝ, ∫ y, e y * u (y + β - a * x) =
      Complex.exp (↑(2 * π * ξ * β) * I) * Complex.exp (↑(-(2 * π * a * ξ)) * x * I) *
        𝓕 u ξ := by
    intro x
    set c := β - a * x with hc
    have hsh : ∀ y, e y * u (y + β - a * x) = e (y + c - c) * u (y + c) := by
      intro y
      rw [hc]
      congr 2 <;> ring
    simp only [hsh]
    have htr := integral_add_right_eq_self (μ := volume) (fun s => e (s - c) * u s) c
    rw [htr]
    rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1
    funext s
    rw [he, smul_eq_mul, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    rw [hc]
    push_cast
    ring_nf
  simp only [hinner]
  rw [integral_mul_const, integral_const_mul, charFun_apply_real]

end

end PGM
