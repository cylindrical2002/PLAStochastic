import PLAStochastic.Index.GEP.DirectTerm.Defs

/-!
# WP4 leaf `DirectTerm`, part 2: positive direction laws for a bump

`positive-direction-response.md` (PD) §1 and §5.  For `x > 0` and `0 < h < x`, `h ≤ 1`, let
`β = unif[x-h, x+h]` (mean `x`), `b₀ = unif[1/4, 3/4]` (mean `1/2`), `b₁ = unif[3/2, 5/2]`
(mean `2`), and `A(x) = 2(2-x)/3`, `B(x) = (2x-1)/3`, so that `A + B = 1` and `A/2 + 2B = x`.
The signed bump `μ_{x,h} = β - A(x) b₀ - B(x) b₁` has mass and mean zero.

With `c(x) = e^{-θσ(x+1)} / (2(1+x))` (`dirC`) the two laws

* `σ₋ = (2/3) b₀ + (1/3) b₁` (independent of `x, h`),
* `σ₊ = c β + u₀ b₀ + u₁ b₁`, `u₀ = (2 - 4c + 2cx)/3`, `u₁ = (1 + c - 2cx)/3`,

are probability laws (`c ≤ 1/2`, `2cx ≤ 1`), absolutely continuous, supported on `(0,∞)`, of
mean one, with `∫ e^{θσ y} dσ± ≤ 1 + e^{5θσ/2}`; they satisfy `σ₊ - σ₋ = c(x) μ_{x,h}`
(`exists_sigmaPair`).  So they are admissible directions of `RawDisc` with the constant
`A = 1 + e^{5θσ/2}`, independent of `x` and `h`, while `1/c(x) = 2(1+x) e^{θσ(x+1)}`.

Uniform laws are normalized restrictions of Lebesgue measure (`unifM`), so their integrals are
set averages `⨍` (`integral_unifM`), which is the form used by the Lebesgue differentiation
theorem.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

/-! ## Normalized Lebesgue measure on a set -/

/-- The normalized Lebesgue measure `volume(s)⁻¹ • volume|_s`. -/
def unifM (s : Set ℝ) : Measure ℝ := (volume s)⁻¹ • volume.restrict s

theorem integral_unifM (s : Set ℝ) (f : ℝ → ℝ) :
    ∫ y, f y ∂(unifM s) = ⨍ y in s, f y := by
  rw [average, Measure.restrict_apply_univ]
  rfl

theorem volume_Icc_ne_zero {a b : ℝ} (hab : a < b) : volume (Icc a b) ≠ 0 := by
  rw [Real.volume_Icc]
  exact (ENNReal.ofReal_pos.2 (by linarith)).ne'

theorem volume_Icc_ne_top (a b : ℝ) : volume (Icc a b) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

theorem isProbabilityMeasure_unifM {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (unifM (Icc a b)) :=
  ⟨by rw [unifM, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
    ENNReal.inv_mul_cancel (volume_Icc_ne_zero hab) (volume_Icc_ne_top a b)]⟩

theorem unifM_Iic_zero {a b : ℝ} (ha : 0 < a) : unifM (Icc a b) (Iic 0) = 0 := by
  rw [unifM, Measure.smul_apply, Measure.restrict_apply measurableSet_Iic]
  have : Iic (0 : ℝ) ∩ Icc a b = ∅ := by
    ext y
    simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    linarith
  rw [this, measure_empty, smul_zero]

theorem unifM_ac (s : Set ℝ) : unifM s ≪ volume :=
  (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _

theorem ae_unifM_mem {s : Set ℝ} (hs : MeasurableSet s) : ∀ᵐ y ∂(unifM s), y ∈ s :=
  Measure.ae_smul_measure (ae_restrict_mem hs) _

theorem integrable_unifM {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : IntegrableOn f (Icc a b)) :
    Integrable f (unifM (Icc a b)) :=
  hf.smul_measure (ENNReal.inv_ne_top.2 (volume_Icc_ne_zero hab))

theorem integral_unifM_le {a b C : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Icc a b)) (hC : ∀ y ∈ Icc a b, f y ≤ C) :
    ∫ y, f y ∂(unifM (Icc a b)) ≤ C := by
  have := isProbabilityMeasure_unifM hab
  have h := integral_mono_ae (integrable_unifM hab hf) (integrable_const C)
    (by filter_upwards [ae_unifM_mem measurableSet_Icc] with y hy using hC y hy)
  simpa using h

theorem integral_id_unifM {a b : ℝ} (hab : a < b) :
    ∫ y, y ∂(unifM (Icc a b)) = (a + b) / 2 := by
  rw [integral_unifM, setAverage_eq, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le, integral_id,
    smul_eq_mul]
  have : b - a ≠ 0 := by linarith
  field_simp
  ring

/-! ## Mixtures of three laws -/

/-- The mixture `w₁ μ₁ + w₂ μ₂ + w₃ μ₃`. -/
def mix3 (w₁ w₂ w₃ : ℝ) (μ₁ μ₂ μ₃ : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal w₁ • μ₁ + ENNReal.ofReal w₂ • μ₂ + ENNReal.ofReal w₃ • μ₃

variable {w₁ w₂ w₃ : ℝ} {μ₁ μ₂ μ₃ : Measure ℝ}

theorem isProbabilityMeasure_mix3 [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    [IsProbabilityMeasure μ₃] (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hs : w₁ + w₂ + w₃ = 1) : IsProbabilityMeasure (mix3 w₁ w₂ w₃ μ₁ μ₂ μ₃) :=
  ⟨by
    simp only [mix3, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hw₁ hw₂, ← ENNReal.ofReal_add (by positivity) hw₃, hs,
      ENNReal.ofReal_one]⟩

theorem integrable_mix3 {f : ℝ → ℝ} (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂)
    (h₃ : Integrable f μ₃) : Integrable f (mix3 w₁ w₂ w₃ μ₁ μ₂ μ₃) :=
  ((h₁.smul_measure ENNReal.ofReal_ne_top).add_measure
    (h₂.smul_measure ENNReal.ofReal_ne_top)).add_measure (h₃.smul_measure ENNReal.ofReal_ne_top)

theorem integral_mix3 (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) {f : ℝ → ℝ}
    (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂) (h₃ : Integrable f μ₃) :
    ∫ y, f y ∂(mix3 w₁ w₂ w₃ μ₁ μ₂ μ₃) =
      w₁ * ∫ y, f y ∂μ₁ + w₂ * ∫ y, f y ∂μ₂ + w₃ * ∫ y, f y ∂μ₃ := by
  rw [mix3, integral_add_measure ((h₁.smul_measure ENNReal.ofReal_ne_top).add_measure
      (h₂.smul_measure ENNReal.ofReal_ne_top)) (h₃.smul_measure ENNReal.ofReal_ne_top),
    integral_add_measure (h₁.smul_measure ENNReal.ofReal_ne_top)
      (h₂.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal hw₁, ENNReal.toReal_ofReal hw₂, ENNReal.toReal_ofReal hw₃]
  simp only [smul_eq_mul]

/-! ## Mixtures of uniform laws are direction laws -/

/-- A mixture of three uniform laws on intervals of `(0,∞)`, with mean one and the exponential
moment bound, is a direction law of `RawDisc`. -/
theorem sigmaLaw_mix3 {A θσ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hθσ : 0 ≤ θσ)
    (ha₁ : 0 < a₁) (hab₁ : a₁ < b₁) (ha₂ : 0 < a₂) (hab₂ : a₂ < b₂) (ha₃ : 0 < a₃)
    (hab₃ : a₃ < b₃) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hmean : w₁ * ((a₁ + b₁) / 2) + w₂ * ((a₂ + b₂) / 2) + w₃ * ((a₃ + b₃) / 2) = 1)
    (hexp : w₁ * Real.exp (θσ * b₁) + w₂ * Real.exp (θσ * b₂) + w₃ * Real.exp (θσ * b₃) ≤ A)
    {σ : ProbabilityMeasure ℝ}
    (hσ : (σ : Measure ℝ) = mix3 w₁ w₂ w₃ (unifM (Icc a₁ b₁)) (unifM (Icc a₂ b₂))
      (unifM (Icc a₃ b₃))) :
    SigmaLaw A θσ σ := by
  have := isProbabilityMeasure_unifM hab₁
  have := isProbabilityMeasure_unifM hab₂
  have := isProbabilityMeasure_unifM hab₃
  have hid : ∀ {a b : ℝ}, a < b → Integrable (fun y : ℝ => y) (unifM (Icc a b)) :=
    fun hab => integrable_unifM hab (continuous_id.integrableOn_Icc)
  have hex : ∀ {a b : ℝ}, a < b → Integrable (fun y : ℝ => Real.exp (θσ * y)) (unifM (Icc a b)) :=
    fun hab => integrable_unifM hab ((by fun_prop : Continuous fun y : ℝ =>
      Real.exp (θσ * y)).integrableOn_Icc)
  have hexle : ∀ {a b : ℝ}, a < b → ∫ y, Real.exp (θσ * y) ∂(unifM (Icc a b)) ≤
      Real.exp (θσ * b) := fun hab => integral_unifM_le hab
    ((by fun_prop : Continuous fun y : ℝ => Real.exp (θσ * y)).integrableOn_Icc)
    fun y hy => Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hy.2 hθσ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hσ, mix3]
    simp only [Measure.add_apply, Measure.smul_apply, unifM_Iic_zero ha₁, unifM_Iic_zero ha₂,
      unifM_Iic_zero ha₃, smul_zero, add_zero]
  · rw [hσ, mix3]
    exact ((((unifM_ac _).smul_left _).add_left ((unifM_ac _).smul_left _)).add_left
      ((unifM_ac _).smul_left _))
  · rw [lawMean, hσ, integral_mix3 hw₁ hw₂ hw₃ (hid hab₁) (hid hab₂) (hid hab₃),
      integral_id_unifM hab₁, integral_id_unifM hab₂, integral_id_unifM hab₃]
    exact hmean
  · rw [hσ]
    exact integrable_mix3 (hex hab₁) (hex hab₂) (hex hab₃)
  · rw [hσ, integral_mix3 hw₁ hw₂ hw₃ (hex hab₁) (hex hab₂) (hex hab₃)]
    refine le_trans ?_ hexp
    gcongr
    · exact hexle hab₁
    · exact hexle hab₂
    · exact hexle hab₃

/-! ## The pair of directions for a bump -/

/-- The scale `c(x) = e^{-θσ(x+1)} / (2(1+x))` of the bump direction. -/
def dirC (θσ x : ℝ) : ℝ := Real.exp (-(θσ * (x + 1))) / (2 * (1 + x))

/-- The weight of `b₀` in the compensated bump, `A(x) = 2(2-x)/3`. -/
def dirA (x : ℝ) : ℝ := 2 * (2 - x) / 3

/-- The weight of `b₁` in the compensated bump, `B(x) = (2x-1)/3`. -/
def dirB (x : ℝ) : ℝ := (2 * x - 1) / 3

theorem dirC_pos (θσ : ℝ) {x : ℝ} (hx : 0 < x) : 0 < dirC θσ x := by
  unfold dirC; positivity

theorem one_div_dirC (θσ : ℝ) {x : ℝ} (hx : 0 < x) :
    1 / dirC θσ x = 2 * (1 + x) * Real.exp (θσ * (x + 1)) := by
  unfold dirC
  rw [one_div_div, Real.exp_neg]
  field_simp

/-- **The two positive directions of a bump** (PD §1, §5): two direction laws with the constant
`1 + e^{5θσ/2}` whose difference is `c(x) (β_{x,h} - A(x) b₀ - B(x) b₁)`. -/
theorem exists_sigmaPair {θσ x h : ℝ} (hθσ : 0 < θσ) (hx : 0 < x) (hh : 0 < h) (hhx : h < x)
    (hh1 : h ≤ 1) :
    ∃ σp σm : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (θσ * (5 / 2))) θσ σp ∧
      SigmaLaw (1 + Real.exp (θσ * (5 / 2))) θσ σm ∧
      ∀ f : ℝ → ℝ, IntegrableOn f (Icc (x - h) (x + h)) →
        IntegrableOn f (Icc (1 / 4 : ℝ) (3 / 4)) → IntegrableOn f (Icc (3 / 2 : ℝ) (5 / 2)) →
        Integrable f (σp : Measure ℝ) ∧ Integrable f (σm : Measure ℝ) ∧
        ∫ y, f y ∂(σp : Measure ℝ) - ∫ y, f y ∂(σm : Measure ℝ) =
          dirC θσ x * ((⨍ y in Metric.closedBall x h, f y) -
            dirA x * (⨍ y in Icc (1 / 4 : ℝ) (3 / 4), f y) -
            dirB x * ⨍ y in Icc (3 / 2 : ℝ) (5 / 2), f y) := by
  set c := dirC θσ x with hc
  have hc0 : 0 < c := dirC_pos θσ hx
  have hex1 : Real.exp (-(θσ * (x + 1))) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  have hc12 : c ≤ 1 / 2 := by
    rw [hc, dirC, div_le_iff₀ (by positivity)]
    nlinarith
  have hcx : 2 * c * x ≤ 1 := by
    rw [hc, dirC]
    rw [show 2 * (Real.exp (-(θσ * (x + 1))) / (2 * (1 + x))) * x =
      Real.exp (-(θσ * (x + 1))) * (x / (1 + x)) by field_simp]
    have : x / (1 + x) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    calc Real.exp (-(θσ * (x + 1))) * (x / (1 + x)) ≤ 1 * 1 :=
          mul_le_mul hex1 this (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hcexp : c * Real.exp (θσ * (x + 1)) ≤ 1 / 2 := by
    rw [hc, dirC, div_mul_eq_mul_div, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set u₀ := (2 - 4 * c + 2 * c * x) / 3 with hu₀
  set u₁ := (1 + c - 2 * c * x) / 3 with hu₁
  have hu₀0 : 0 ≤ u₀ := by rw [hu₀]; nlinarith
  have hu₁0 : 0 ≤ u₁ := by rw [hu₁]; linarith
  have hab : x - h < x + h := by linarith
  have ha : 0 < x - h := by linarith
  have h14 : (1 / 4 : ℝ) < 3 / 4 := by norm_num
  have h32 : (3 / 2 : ℝ) < 5 / 2 := by norm_num
  have := isProbabilityMeasure_unifM hab
  have := isProbabilityMeasure_unifM h14
  have := isProbabilityMeasure_unifM h32
  have hPp : IsProbabilityMeasure (mix3 c u₀ u₁ (unifM (Icc (x - h) (x + h)))
      (unifM (Icc (1 / 4 : ℝ) (3 / 4))) (unifM (Icc (3 / 2 : ℝ) (5 / 2)))) :=
    isProbabilityMeasure_mix3 hc0.le hu₀0 hu₁0 (by rw [hu₀, hu₁]; ring)
  have hPm : IsProbabilityMeasure (mix3 0 (2 / 3) (1 / 3) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
      (unifM (Icc (1 / 4 : ℝ) (3 / 4))) (unifM (Icc (3 / 2 : ℝ) (5 / 2)))) :=
    isProbabilityMeasure_mix3 le_rfl (by norm_num) (by norm_num) (by norm_num)
  have hθ0 := hθσ.le
  have he34 : Real.exp (θσ * (3 / 4)) ≤ Real.exp (θσ * (5 / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hexh : Real.exp (θσ * (x + h)) ≤ Real.exp (θσ * (x + 1)) :=
    Real.exp_le_exp.2 (by nlinarith)
  refine ⟨⟨_, hPp⟩, ⟨_, hPm⟩, ?_, ?_, ?_⟩
  · refine sigmaLaw_mix3 hθ0 ha hab (by norm_num) h14 (by norm_num) h32 hc0.le hu₀0 hu₁0 ?_ ?_ rfl
    · rw [hu₀, hu₁]; ring
    · have hp : 0 < Real.exp (θσ * (5 / 2)) := Real.exp_pos _
      calc c * Real.exp (θσ * (x + h)) + u₀ * Real.exp (θσ * (3 / 4)) +
            u₁ * Real.exp (θσ * (5 / 2))
          ≤ c * Real.exp (θσ * (x + 1)) + u₀ * Real.exp (θσ * (5 / 2)) +
            u₁ * Real.exp (θσ * (5 / 2)) := by gcongr
        _ = c * Real.exp (θσ * (x + 1)) + (1 - c) * Real.exp (θσ * (5 / 2)) := by
            rw [hu₀, hu₁]; ring
        _ ≤ 1 / 2 + 1 * Real.exp (θσ * (5 / 2)) := by
            gcongr
            linarith
        _ ≤ 1 + Real.exp (θσ * (5 / 2)) := by linarith
  · refine sigmaLaw_mix3 hθ0 (by norm_num) h14 (by norm_num) h14 (by norm_num) h32 le_rfl
      (by norm_num) (by norm_num) (by norm_num) ?_ rfl
    have hp : 0 < Real.exp (θσ * (5 / 2)) := Real.exp_pos _
    calc 0 * Real.exp (θσ * (3 / 4)) + 2 / 3 * Real.exp (θσ * (3 / 4)) +
          1 / 3 * Real.exp (θσ * (5 / 2))
        ≤ 0 + 2 / 3 * Real.exp (θσ * (5 / 2)) + 1 / 3 * Real.exp (θσ * (5 / 2)) := by
          gcongr; simp
      _ ≤ 1 + Real.exp (θσ * (5 / 2)) := by linarith
  · intro f hfβ hf₀ hf₁
    have iβ := integrable_unifM hab hfβ
    have i₀ := integrable_unifM h14 hf₀
    have i₁ := integrable_unifM h32 hf₁
    refine ⟨integrable_mix3 iβ i₀ i₁, integrable_mix3 i₀ i₀ i₁, ?_⟩
    change ∫ y, f y ∂(mix3 c u₀ u₁ _ _ _) - ∫ y, f y ∂(mix3 0 (2 / 3) (1 / 3) _ _ _) = _
    rw [integral_mix3 hc0.le hu₀0 hu₁0 iβ i₀ i₁,
      integral_mix3 le_rfl (by norm_num) (by norm_num) i₀ i₀ i₁,
      integral_unifM, integral_unifM, integral_unifM, Real.closedBall_eq_Icc, hu₀, hu₁,
      dirA, dirB]
    ring

end

end PGM
