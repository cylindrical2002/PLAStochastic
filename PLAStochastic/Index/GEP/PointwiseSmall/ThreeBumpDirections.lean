import PLAStochastic.Index.GEP.PointwiseSmall.LebesguePoints

/-!
# WP4 leaf `PointwiseSmall`: the three-bump directions of the output row

PD §6.1.  For `x > 0`, `0 < h < x`, `h ≤ 1`, let `β = unif[x-h, x+h]` and the fixed bumps
`b₀ = unif[1/4, 3/4]`, `b₁ = unif[3/2, 5/2]`, `b₂ = unif[5/2, 7/2]` (means `1/2, 2, 3`, second
moments `13/48, 49/12, 109/12`).  The weights `w_j = pwW_j x s`, `s = x² + h²/3`, reproduce the
mass, mean and second moment of `β`: `∑ w_j = 1`, `∑ w_j m_j = x`, `∑ w_j m2_j = s`
(`pw_w_sum`, `pw_w_mean`, `pw_w_sq`), and `|w_j| ≤ 3 (1 + x)²`.

With `σ₋ = (11/15) b₀ + (1/6) b₁ + (1/10) b₂` (mean one) and
`σ₊ = σ₋ + c (β - ∑ w_j b_j)`, `c = pwC3 θσ x = e^{-θσ(x+1)} / (30 (1 + x)²)`, both are direction
laws with the constant `1 + e^{7θσ/2}`, they have the **same variance**, and
`∫ f dσ₊ - ∫ f dσ₋ = c (⨍_β f - ∑ w_j ⨍_{b_j} f)` (`pw_exists_sigmaTriple`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-! ## Mixtures of four laws -/

/-- The mixture `w₀ μ₀ + w₁ μ₁ + w₂ μ₂ + w₃ μ₃`. -/
def pwMix4 (w₀ w₁ w₂ w₃ : ℝ) (μ₀ μ₁ μ₂ μ₃ : Measure ℝ) : Measure ℝ :=
  mix3 w₀ w₁ w₂ μ₀ μ₁ μ₂ + ENNReal.ofReal w₃ • μ₃

variable {w₀ w₁ w₂ w₃ : ℝ} {μ₀ μ₁ μ₂ μ₃ : Measure ℝ}

theorem isProbabilityMeasure_pwMix4 [IsProbabilityMeasure μ₀] [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure μ₃] (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃) (hs : w₀ + w₁ + w₂ + w₃ = 1) :
    IsProbabilityMeasure (pwMix4 w₀ w₁ w₂ w₃ μ₀ μ₁ μ₂ μ₃) :=
  ⟨by
    simp only [pwMix4, mix3, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
      mul_one]
    rw [← ENNReal.ofReal_add hw₀ hw₁, ← ENNReal.ofReal_add (by positivity) hw₂,
      ← ENNReal.ofReal_add (by positivity) hw₃, hs, ENNReal.ofReal_one]⟩

theorem integrable_pwMix4 {f : ℝ → ℝ} (h₀ : Integrable f μ₀) (h₁ : Integrable f μ₁)
    (h₂ : Integrable f μ₂) (h₃ : Integrable f μ₃) :
    Integrable f (pwMix4 w₀ w₁ w₂ w₃ μ₀ μ₁ μ₂ μ₃) :=
  (integrable_mix3 h₀ h₁ h₂).add_measure (h₃.smul_measure ENNReal.ofReal_ne_top)

theorem integral_pwMix4 (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    {f : ℝ → ℝ} (h₀ : Integrable f μ₀) (h₁ : Integrable f μ₁) (h₂ : Integrable f μ₂)
    (h₃ : Integrable f μ₃) :
    ∫ y, f y ∂(pwMix4 w₀ w₁ w₂ w₃ μ₀ μ₁ μ₂ μ₃) =
      w₀ * ∫ y, f y ∂μ₀ + w₁ * ∫ y, f y ∂μ₁ + w₂ * ∫ y, f y ∂μ₂ + w₃ * ∫ y, f y ∂μ₃ := by
  rw [pwMix4, integral_add_measure (integrable_mix3 h₀ h₁ h₂)
    (h₃.smul_measure ENNReal.ofReal_ne_top), integral_mix3 hw₀ hw₁ hw₂ h₀ h₁ h₂,
    integral_smul_measure, ENNReal.toReal_ofReal hw₃, smul_eq_mul]

/-- A mixture of four uniform laws on intervals of `(0,∞)`, with mean one and the exponential
moment bound, is a direction law. -/
theorem pw_sigmaLaw_mix4 {A θσ a₀ b₀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ} (hθσ : 0 ≤ θσ)
    (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀) (ha₁ : 0 < a₁) (hab₁ : a₁ < b₁) (ha₂ : 0 < a₂)
    (hab₂ : a₂ < b₂) (ha₃ : 0 < a₃) (hab₃ : a₃ < b₃) (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁)
    (hw₂ : 0 ≤ w₂) (hw₃ : 0 ≤ w₃)
    (hmean : w₀ * ((a₀ + b₀) / 2) + w₁ * ((a₁ + b₁) / 2) + w₂ * ((a₂ + b₂) / 2) +
      w₃ * ((a₃ + b₃) / 2) = 1)
    (hexp : w₀ * Real.exp (θσ * b₀) + w₁ * Real.exp (θσ * b₁) + w₂ * Real.exp (θσ * b₂) +
      w₃ * Real.exp (θσ * b₃) ≤ A)
    {σ : ProbabilityMeasure ℝ}
    (hσ : (σ : Measure ℝ) = pwMix4 w₀ w₁ w₂ w₃ (unifM (Icc a₀ b₀)) (unifM (Icc a₁ b₁))
      (unifM (Icc a₂ b₂)) (unifM (Icc a₃ b₃))) :
    SigmaLaw A θσ σ := by
  have := isProbabilityMeasure_unifM hab₀
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
  · rw [hσ, pwMix4, mix3]
    simp only [Measure.add_apply, Measure.smul_apply, unifM_Iic_zero ha₀, unifM_Iic_zero ha₁,
      unifM_Iic_zero ha₂, unifM_Iic_zero ha₃, smul_zero, add_zero]
  · rw [hσ, pwMix4, mix3]
    exact (((((unifM_ac _).smul_left _).add_left ((unifM_ac _).smul_left _)).add_left
      ((unifM_ac _).smul_left _)).add_left ((unifM_ac _).smul_left _))
  · rw [lawMean, hσ, integral_pwMix4 hw₀ hw₁ hw₂ hw₃ (hid hab₀) (hid hab₁) (hid hab₂) (hid hab₃),
      integral_id_unifM hab₀, integral_id_unifM hab₁, integral_id_unifM hab₂,
      integral_id_unifM hab₃]
    exact hmean
  · rw [hσ]
    exact integrable_pwMix4 (hex hab₀) (hex hab₁) (hex hab₂) (hex hab₃)
  · rw [hσ, integral_pwMix4 hw₀ hw₁ hw₂ hw₃ (hex hab₀) (hex hab₁) (hex hab₂) (hex hab₃)]
    refine le_trans ?_ hexp
    gcongr
    · exact hexle hab₀
    · exact hexle hab₁
    · exact hexle hab₂
    · exact hexle hab₃

/-! ## Averages of `(y - 1)²` over intervals -/

theorem pw_average_sq_sub_one {a b : ℝ} (hab : a < b) :
    ⨍ y in Icc a b, (y - 1) ^ 2 = (a ^ 2 + a * b + b ^ 2) / 3 - (a + b) + 1 := by
  rw [setAverage_eq, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_comp_sub_right (fun y : ℝ => y ^ 2) 1, integral_pow, smul_eq_mul]
  have : b - a ≠ 0 := by linarith
  push_cast
  field_simp
  ring

/-! ## The weights -/

/-- The weight of `b₀ = unif[1/4, 3/4]`. -/
def pwW0 (x s : ℝ) : ℝ := (284 - 240 * x + 48 * s) / 177

/-- The weight of `b₁ = unif[3/2, 5/2]`. -/
def pwW1 (x s : ℝ) : ℝ := (423 * x - 120 * s - 179) / 177

/-- The weight of `b₂ = unif[5/2, 7/2]`. -/
def pwW2 (x s : ℝ) : ℝ := (24 * s - 61 * x + 24) / 59

theorem pw_w_sum (x s : ℝ) : pwW0 x s + pwW1 x s + pwW2 x s = 1 := by
  unfold pwW0 pwW1 pwW2; ring

theorem pw_w_mean (x s : ℝ) : pwW0 x s * (1 / 2) + pwW1 x s * 2 + pwW2 x s * 3 = x := by
  unfold pwW0 pwW1 pwW2; ring

theorem pw_w_sq (x s : ℝ) :
    pwW0 x s * (13 / 48) + pwW1 x s * (49 / 12) + pwW2 x s * (109 / 12) = s := by
  unfold pwW0 pwW1 pwW2; ring

theorem pw_w_abs_le {x s : ℝ} (hx : 0 ≤ x) (hs1 : x ^ 2 ≤ s) (hs2 : s ≤ x ^ 2 + 1 / 3) :
    |pwW0 x s| ≤ 3 * (1 + x) ^ 2 ∧ |pwW1 x s| ≤ 3 * (1 + x) ^ 2 ∧
      |pwW2 x s| ≤ 3 * (1 + x) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pwW0, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 177), div_le_iff₀ (by norm_num),
      abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  · rw [pwW1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 177), div_le_iff₀ (by norm_num),
      abs_le]
    constructor <;> nlinarith [sq_nonneg x]
  · rw [pwW2, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 59), div_le_iff₀ (by norm_num),
      abs_le]
    constructor <;> nlinarith [sq_nonneg x]

/-- The scale `c(x) = e^{-θσ(x+1)} / (30 (1 + x)²)` of the three-bump direction. -/
def pwC3 (θσ x : ℝ) : ℝ := Real.exp (-(θσ * (x + 1))) / (30 * (1 + x) ^ 2)

theorem pwC3_pos (θσ : ℝ) {x : ℝ} (hx : 0 < x) : 0 < pwC3 θσ x := by
  unfold pwC3
  have : 0 < 1 + x := by linarith
  positivity

theorem one_div_pwC3 (θσ x : ℝ) :
    1 / pwC3 θσ x = 30 * (1 + x) ^ 2 * Real.exp (θσ * (x + 1)) := by
  unfold pwC3
  rw [one_div_div, Real.exp_neg, div_inv_eq_mul]

/-- `c(x) · 3 (1 + x)² · e^{θσ(x+1)} = 1/10`. -/
theorem pwC3_mul {θσ x : ℝ} (hx : 0 < x) :
    pwC3 θσ x * (3 * (1 + x) ^ 2) * Real.exp (θσ * (x + 1)) = 1 / 10 := by
  unfold pwC3
  rw [Real.exp_neg]
  have h1 : (1 + x) ≠ 0 := (by linarith : (0 : ℝ) < 1 + x).ne'
  have h2 : Real.exp (θσ * (x + 1)) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-! ## The pair of directions -/

/-- **The three-bump directions** (PD §6.1): two direction laws with the constant
`1 + e^{7θσ/2}`, of the same variance, whose difference is
`c(x) (β_{x,h} - w₀ b₀ - w₁ b₁ - w₂ b₂)`. -/
theorem pw_exists_sigmaTriple {θσ x h : ℝ} (hθσ : 0 < θσ) (hx : 0 < x) (hh : 0 < h)
    (hhx : h < x) (hh1 : h ≤ 1) :
    ∃ σp σm : ProbabilityMeasure ℝ, SigmaLaw (1 + Real.exp (θσ * (7 / 2))) θσ σp ∧
      SigmaLaw (1 + Real.exp (θσ * (7 / 2))) θσ σm ∧ lawVar σp = lawVar σm ∧
      ∀ f : ℝ → ℝ, IntegrableOn f (Icc (x - h) (x + h)) →
        IntegrableOn f (Icc (1 / 4 : ℝ) (3 / 4)) → IntegrableOn f (Icc (3 / 2 : ℝ) (5 / 2)) →
        IntegrableOn f (Icc (5 / 2 : ℝ) (7 / 2)) →
        Integrable f (σp : Measure ℝ) ∧ Integrable f (σm : Measure ℝ) ∧
        ∫ y, f y ∂(σp : Measure ℝ) - ∫ y, f y ∂(σm : Measure ℝ) =
          pwC3 θσ x * ((⨍ y in Metric.closedBall x h, f y) -
            pwW0 x (x ^ 2 + h ^ 2 / 3) * (⨍ y in Icc (1 / 4 : ℝ) (3 / 4), f y) -
            pwW1 x (x ^ 2 + h ^ 2 / 3) * (⨍ y in Icc (3 / 2 : ℝ) (5 / 2), f y) -
            pwW2 x (x ^ 2 + h ^ 2 / 3) * ⨍ y in Icc (5 / 2 : ℝ) (7 / 2), f y) := by
  set s := x ^ 2 + h ^ 2 / 3 with hs
  set c := pwC3 θσ x with hc
  have hc0 : 0 < c := pwC3_pos θσ hx
  have hcm := pwC3_mul (θσ := θσ) hx
  rw [← hc] at hcm
  have hex1 : 1 ≤ Real.exp (θσ * (x + 1)) := Real.one_le_exp (by positivity)
  have hcw : c * (3 * (1 + x) ^ 2) ≤ 1 / 10 := by
    rw [← hcm]
    have : 0 ≤ c * (3 * (1 + x) ^ 2) := by positivity
    nlinarith
  have hcexp : c * Real.exp (θσ * (x + 1)) ≤ 1 / 10 := by
    rw [← hcm]
    have h3 : 1 ≤ 3 * (1 + x) ^ 2 := by nlinarith
    have : 0 ≤ c * Real.exp (θσ * (x + 1)) := by positivity
    nlinarith
  obtain ⟨hw0, hw1, hw2⟩ := pw_w_abs_le (s := s) hx.le (by rw [hs]; nlinarith)
    (by rw [hs]; nlinarith)
  set w₀ := pwW0 x s with hw₀
  set w₁ := pwW1 x s with hw₁
  set w₂ := pwW2 x s with hw₂
  have hcw0 : |c * w₀| ≤ 1 / 10 := by
    rw [abs_mul, abs_of_pos hc0]
    calc c * |w₀| ≤ c * (3 * (1 + x) ^ 2) := by gcongr
      _ ≤ 1 / 10 := hcw
  have hcw1 : |c * w₁| ≤ 1 / 10 := by
    rw [abs_mul, abs_of_pos hc0]
    calc c * |w₁| ≤ c * (3 * (1 + x) ^ 2) := by gcongr
      _ ≤ 1 / 10 := hcw
  have hcw2 : |c * w₂| ≤ 1 / 10 := by
    rw [abs_mul, abs_of_pos hc0]
    calc c * |w₂| ≤ c * (3 * (1 + x) ^ 2) := by gcongr
      _ ≤ 1 / 10 := hcw
  have hu₀ : 0 ≤ 11 / 15 - c * w₀ := by linarith [(abs_le.1 hcw0).2]
  have hu₁ : 0 ≤ 1 / 6 - c * w₁ := by linarith [(abs_le.1 hcw1).2]
  have hu₂ : 0 ≤ 1 / 10 - c * w₂ := by linarith [(abs_le.1 hcw2).2]
  have hsum := pw_w_sum x s
  have hmean := pw_w_mean x s
  have hsq := pw_w_sq x s
  rw [← hw₀, ← hw₁, ← hw₂] at hsum hmean hsq
  have hab : x - h < x + h := by linarith
  have ha : 0 < x - h := by linarith
  have h14 : (1 / 4 : ℝ) < 3 / 4 := by norm_num
  have h32 : (3 / 2 : ℝ) < 5 / 2 := by norm_num
  have h52 : (5 / 2 : ℝ) < 7 / 2 := by norm_num
  have := isProbabilityMeasure_unifM hab
  have := isProbabilityMeasure_unifM h14
  have := isProbabilityMeasure_unifM h32
  have := isProbabilityMeasure_unifM h52
  have hPp : IsProbabilityMeasure (pwMix4 c (11 / 15 - c * w₀) (1 / 6 - c * w₁) (1 / 10 - c * w₂)
      (unifM (Icc (x - h) (x + h))) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
      (unifM (Icc (3 / 2 : ℝ) (5 / 2))) (unifM (Icc (5 / 2 : ℝ) (7 / 2)))) :=
    isProbabilityMeasure_pwMix4 hc0.le hu₀ hu₁ hu₂ (by linear_combination (-c) * hsum)
  have hPm : IsProbabilityMeasure (pwMix4 0 (11 / 15) (1 / 6) (1 / 10)
      (unifM (Icc (x - h) (x + h))) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
      (unifM (Icc (3 / 2 : ℝ) (5 / 2))) (unifM (Icc (5 / 2 : ℝ) (7 / 2)))) :=
    isProbabilityMeasure_pwMix4 le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hθ0 := hθσ.le
  have hexh : Real.exp (θσ * (x + h)) ≤ Real.exp (θσ * (x + 1)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have he7 : ∀ b : ℝ, b ≤ 7 / 2 → Real.exp (θσ * b) ≤ Real.exp (θσ * (7 / 2)) := fun b hb =>
    Real.exp_le_exp.2 (by nlinarith)
  have hp7 : 0 < Real.exp (θσ * (7 / 2)) := Real.exp_pos _
  -- the difference of the two laws against a test
  have hdiff : ∀ f : ℝ → ℝ, IntegrableOn f (Icc (x - h) (x + h)) →
      IntegrableOn f (Icc (1 / 4 : ℝ) (3 / 4)) → IntegrableOn f (Icc (3 / 2 : ℝ) (5 / 2)) →
      IntegrableOn f (Icc (5 / 2 : ℝ) (7 / 2)) →
      Integrable f (pwMix4 c (11 / 15 - c * w₀) (1 / 6 - c * w₁) (1 / 10 - c * w₂)
        (unifM (Icc (x - h) (x + h))) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
        (unifM (Icc (3 / 2 : ℝ) (5 / 2))) (unifM (Icc (5 / 2 : ℝ) (7 / 2)))) ∧
      Integrable f (pwMix4 0 (11 / 15) (1 / 6) (1 / 10)
        (unifM (Icc (x - h) (x + h))) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
        (unifM (Icc (3 / 2 : ℝ) (5 / 2))) (unifM (Icc (5 / 2 : ℝ) (7 / 2)))) ∧
      ∫ y, f y ∂(pwMix4 c (11 / 15 - c * w₀) (1 / 6 - c * w₁) (1 / 10 - c * w₂)
        (unifM (Icc (x - h) (x + h))) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
        (unifM (Icc (3 / 2 : ℝ) (5 / 2))) (unifM (Icc (5 / 2 : ℝ) (7 / 2)))) -
      ∫ y, f y ∂(pwMix4 0 (11 / 15) (1 / 6) (1 / 10)
        (unifM (Icc (x - h) (x + h))) (unifM (Icc (1 / 4 : ℝ) (3 / 4)))
        (unifM (Icc (3 / 2 : ℝ) (5 / 2))) (unifM (Icc (5 / 2 : ℝ) (7 / 2)))) =
        c * ((⨍ y in Metric.closedBall x h, f y) -
          w₀ * (⨍ y in Icc (1 / 4 : ℝ) (3 / 4), f y) -
          w₁ * (⨍ y in Icc (3 / 2 : ℝ) (5 / 2), f y) -
          w₂ * ⨍ y in Icc (5 / 2 : ℝ) (7 / 2), f y) := by
    intro f hfβ hf₀ hf₁ hf₂
    have iβ := integrable_unifM hab hfβ
    have i₀ := integrable_unifM h14 hf₀
    have i₁ := integrable_unifM h32 hf₁
    have i₂ := integrable_unifM h52 hf₂
    refine ⟨integrable_pwMix4 iβ i₀ i₁ i₂, integrable_pwMix4 iβ i₀ i₁ i₂, ?_⟩
    rw [integral_pwMix4 hc0.le hu₀ hu₁ hu₂ iβ i₀ i₁ i₂,
      integral_pwMix4 le_rfl (by norm_num) (by norm_num) (by norm_num) iβ i₀ i₁ i₂,
      integral_unifM, integral_unifM, integral_unifM, integral_unifM, Real.closedBall_eq_Icc]
    ring
  -- the two laws
  have hSp : SigmaLaw (1 + Real.exp (θσ * (7 / 2))) θσ ⟨_, hPp⟩ := by
    refine pw_sigmaLaw_mix4 hθ0 ha hab (by norm_num) h14 (by norm_num) h32 (by norm_num) h52
      hc0.le hu₀ hu₁ hu₂ ?_ ?_ rfl
    · linear_combination (-c) * hmean
    · have t1 := mul_le_mul_of_nonneg_left (he7 (3 / 4) (by norm_num)) hu₀
      have t2 := mul_le_mul_of_nonneg_left (he7 (5 / 2) (by norm_num)) hu₁
      have t3 := mul_le_mul_of_nonneg_left hexh hc0.le
      have t4 : (11 / 15 - c * w₀) * Real.exp (θσ * (7 / 2)) +
          (1 / 6 - c * w₁) * Real.exp (θσ * (7 / 2)) +
          (1 / 10 - c * w₂) * Real.exp (θσ * (7 / 2)) = (1 - c) * Real.exp (θσ * (7 / 2)) := by
        linear_combination (-c * Real.exp (θσ * (7 / 2))) * hsum
      have t5 : (1 - c) * Real.exp (θσ * (7 / 2)) ≤ Real.exp (θσ * (7 / 2)) := by
        have := mul_pos hc0 hp7
        linarith
      linarith
  have hSm : SigmaLaw (1 + Real.exp (θσ * (7 / 2))) θσ ⟨_, hPm⟩ := by
    refine pw_sigmaLaw_mix4 hθ0 ha hab (by norm_num) h14 (by norm_num) h32 (by norm_num) h52
      le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ rfl
    linarith [he7 (3 / 4) (by norm_num), he7 (5 / 2) (by norm_num)]
  refine ⟨⟨_, hPp⟩, ⟨_, hPm⟩, hSp, hSm, ?_, fun f hfβ hf₀ hf₁ hf₂ => hdiff f hfβ hf₀ hf₁ hf₂⟩
  -- the variances agree
  simp only [lawVar, hSp.mean, hSm.mean]
  have hcont : Continuous fun y : ℝ => (y - 1) ^ 2 := by fun_prop
  obtain ⟨-, -, heq⟩ := hdiff (fun y => (y - 1) ^ 2) hcont.integrableOn_Icc
    hcont.integrableOn_Icc hcont.integrableOn_Icc hcont.integrableOn_Icc
  rw [Real.closedBall_eq_Icc, pw_average_sq_sub_one hab, pw_average_sq_sub_one h14,
    pw_average_sq_sub_one h32, pw_average_sq_sub_one h52] at heq
  refine sub_eq_zero.1 (heq.trans ?_)
  linear_combination c * (2 * hmean - hsum - hsq - hs)

end

end PGM
