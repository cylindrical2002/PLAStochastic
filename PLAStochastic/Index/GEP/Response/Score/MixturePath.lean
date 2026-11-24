import PLAStochastic.Index.GEP.Response.OfInterfaces

/-!
# WP4 leaf 4A-S, part 2: densities along the mixture path and the score

For two laws with densities `f₀, f₁`, the mixture `ν_s = (1 - s) ν₀ + s ν₁` has density
`w_s = (1 - s) f₀ + s f₁` (`coe_mixPM_eq_withDensity`).  Fix a base point `s₀ ∈ (0,1)`.  The score
`h = (f₁ - f₀) / w_{s₀}` is bounded by `1/s₀ + 1/(1-s₀)` (`abs_mixScore_le`) and, for every
`s ∈ [0,1]`, `ν_s = (1 + (s - s₀) h) · ν_{s₀}` (`mixPM_eq_withDensity_ratio`).  This is the device
of `influence-lipschitz.md` §8 and `joint-response.md` §5: on `(0,1)` the score is bounded, even
if `f₁ / f₀` is not.

Consequences:
* `integral_mul_mixScore`: `∫ a h dν_{s₀} = ∫ a dν₁ - ∫ a dν₀`;
* `mixPM_le_smul_left`, `mixPM_le_smul_right`: `ν₀, ν₁ ≤ K ν_{s₀}`, so integrability transfers
  from the base law to the endpoints.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-- The density of the mixture, `w_s = (1 - s) f₀ + s f₁`. -/
def mixDens (f₀ f₁ : ℝ → ℝ) (s y : ℝ) : ℝ := (1 - s) * f₀ y + s * f₁ y

/-- The score of the mixture path at the base point `s₀`: `h = (f₁ - f₀) / w_{s₀}`. -/
def mixScore (f₀ f₁ : ℝ → ℝ) (s₀ y : ℝ) : ℝ := (f₁ y - f₀ y) / mixDens f₀ f₁ s₀ y

/-- The density ratio `dν_s / dν_{s₀} = 1 + (s - s₀) h`. -/
def mixRatio (f₀ f₁ : ℝ → ℝ) (s₀ s y : ℝ) : ℝ := 1 + (s - s₀) * mixScore f₀ f₁ s₀ y

/-- The bound `1/s₀ + 1/(1-s₀)` of the score. -/
def scoreBd (s₀ : ℝ) : ℝ := 1 / s₀ + 1 / (1 - s₀)

variable {f₀ f₁ : ℝ → ℝ}

theorem measurable_mixDens (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (s : ℝ) :
    Measurable (mixDens f₀ f₁ s) :=
  (hf₀.const_mul _).add (hf₁.const_mul _)

theorem measurable_mixScore (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (s₀ : ℝ) :
    Measurable (mixScore f₀ f₁ s₀) :=
  (hf₁.sub hf₀).div (measurable_mixDens hf₀ hf₁ s₀)

theorem measurable_mixRatio (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (s₀ s : ℝ) :
    Measurable (mixRatio f₀ f₁ s₀ s) :=
  measurable_const.add ((measurable_mixScore hf₀ hf₁ s₀).const_mul _)

theorem scoreBd_pos {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) : 0 < scoreBd s₀ := by
  have h1 : 0 < 1 - s₀ := by linarith [hs₀.2]
  have := hs₀.1
  unfold scoreBd; positivity

theorem mixDens_nonneg (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (y : ℝ) : 0 ≤ mixDens f₀ f₁ s y := by
  have : 0 ≤ 1 - s := by linarith [hs.2]
  have := h0 y; have := h1 y; have := hs.1
  unfold mixDens; positivity

/-- Where the base density vanishes, both densities vanish. -/
theorem eq_zero_of_mixDens_eq_zero (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {y : ℝ} (hw : mixDens f₀ f₁ s₀ y = 0) : f₀ y = 0 ∧ f₁ y = 0 := by
  have ha : 0 < 1 - s₀ := by linarith [hs₀.2]
  have hb := hs₀.1
  have h0y := h0 y; have h1y := h1 y
  unfold mixDens at hw
  constructor <;> nlinarith [mul_nonneg ha.le h0y, mul_nonneg hb.le h1y]

theorem abs_mixScore_le (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (y : ℝ) : |mixScore f₀ f₁ s₀ y| ≤ scoreBd s₀ := by
  have ha : 0 < 1 - s₀ := by linarith [hs₀.2]
  have hb := hs₀.1
  have h0y := h0 y; have h1y := h1 y
  have hw := mixDens_nonneg h0 h1 (s := s₀) ⟨hb.le, by linarith⟩ y
  rcases hw.eq_or_lt with hw0 | hwpos
  · rw [mixScore, ← hw0, div_zero, abs_zero]; exact (scoreBd_pos hs₀).le
  · rw [mixScore, abs_div, abs_of_pos hwpos, div_le_iff₀ hwpos]
    have e1 : f₁ y ≤ mixDens f₀ f₁ s₀ y / s₀ := by
      rw [le_div_iff₀ hb]; unfold mixDens; nlinarith [mul_nonneg ha.le h0y]
    have e0 : f₀ y ≤ mixDens f₀ f₁ s₀ y / (1 - s₀) := by
      rw [le_div_iff₀ ha]; unfold mixDens; nlinarith [mul_nonneg hb.le h1y]
    calc |f₁ y - f₀ y| ≤ f₁ y + f₀ y := by
          rw [abs_le]; constructor <;> linarith
      _ ≤ mixDens f₀ f₁ s₀ y / s₀ + mixDens f₀ f₁ s₀ y / (1 - s₀) := add_le_add e1 e0
      _ = scoreBd s₀ * mixDens f₀ f₁ s₀ y := by unfold scoreBd; ring

/-- `w_s = w_{s₀} (1 + (s - s₀) h)` for every `s`. -/
theorem mixDens_eq_mul (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (s y : ℝ) :
    mixDens f₀ f₁ s y = mixDens f₀ f₁ s₀ y * mixRatio f₀ f₁ s₀ s y := by
  by_cases hw : mixDens f₀ f₁ s₀ y = 0
  · obtain ⟨e0, e1⟩ := eq_zero_of_mixDens_eq_zero h0 h1 hs₀ hw
    rw [hw, zero_mul]; unfold mixDens; rw [e0, e1]; ring
  · rw [mixRatio, mixScore, mul_add, mul_one, mul_left_comm, mul_div_cancel₀ _ hw]
    unfold mixDens; ring

theorem mixRatio_nonneg (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    0 ≤ mixRatio f₀ f₁ s₀ s y := by
  by_cases hw : mixDens f₀ f₁ s₀ y = 0
  · rw [mixRatio, mixScore, hw, div_zero, mul_zero, add_zero]; exact zero_le_one
  · have hwpos : 0 < mixDens f₀ f₁ s₀ y :=
      lt_of_le_of_ne (mixDens_nonneg h0 h1 ⟨hs₀.1.le, hs₀.2.le⟩ y) (Ne.symm hw)
    have hn := mixDens_nonneg h0 h1 hs y
    rw [mixDens_eq_mul h0 h1 hs₀ s y] at hn
    exact (mul_nonneg_iff_of_pos_left hwpos).1 hn

theorem abs_mixRatio_le (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (s y : ℝ) :
    |mixRatio f₀ f₁ s₀ s y| ≤ 1 + |s - s₀| * scoreBd s₀ := by
  rw [mixRatio]
  calc |1 + (s - s₀) * mixScore f₀ f₁ s₀ y| ≤ |1| + |(s - s₀) * mixScore f₀ f₁ s₀ y| :=
        abs_add_le _ _
    _ = 1 + |s - s₀| * |mixScore f₀ f₁ s₀ y| := by rw [abs_one, abs_mul]
    _ ≤ 1 + |s - s₀| * scoreBd s₀ := by
        gcongr; exact abs_mixScore_le h0 h1 hs₀ y

/-- The mixture has density `w_s` for `s ∈ [0,1]`. -/
theorem coe_mixPM_eq_withDensity {ν₀ ν₁ : ProbabilityMeasure ℝ} (h0 : ∀ y, 0 ≤ f₀ y)
    (h1 : ∀ y, 0 ≤ f₁ y) (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hν₀ : (ν₀ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₀ x))
    (hν₁ : (ν₁ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₁ x))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (mixPM ν₀ ν₁ s : Measure ℝ) =
      volume.withDensity fun x => ENNReal.ofReal (mixDens f₀ f₁ s x) := by
  have h1s : 0 ≤ 1 - s := by linarith [hs.2]
  rw [coe_mixPM, mixParam_of_mem hs, hν₀, hν₁, ← withDensity_smul _ hf₀.ennreal_ofReal,
    ← withDensity_smul _ hf₁.ennreal_ofReal,
    ← withDensity_add_left (hf₀.ennreal_ofReal.const_smul _)]
  congr 1
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mixDens]
  rw [ENNReal.ofReal_add (mul_nonneg h1s (h0 x)) (mul_nonneg hs.1 (h1 x)),
    ENNReal.ofReal_mul h1s, ENNReal.ofReal_mul hs.1]

/-- The density ratio as an `NNReal` function. -/
def mixRatioNN (f₀ f₁ : ℝ → ℝ) (s₀ s y : ℝ) : ℝ≥0 := (mixRatio f₀ f₁ s₀ s y).toNNReal

theorem measurable_mixRatioNN (hf₀ : Measurable f₀) (hf₁ : Measurable f₁) (s₀ s : ℝ) :
    Measurable (mixRatioNN f₀ f₁ s₀ s) :=
  (measurable_mixRatio hf₀ hf₁ s₀ s).real_toNNReal

theorem coe_mixRatioNN (h0 : ∀ y, 0 ≤ f₀ y) (h1 : ∀ y, 0 ≤ f₁ y) {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (y : ℝ) :
    (mixRatioNN f₀ f₁ s₀ s y : ℝ) = mixRatio f₀ f₁ s₀ s y :=
  Real.coe_toNNReal _ (mixRatio_nonneg h0 h1 hs₀ hs y)

/-- **The mixture path relative to a base point**: `ν_s = (1 + (s - s₀) h) · ν_{s₀}`. -/
theorem mixPM_eq_withDensity_ratio {ν₀ ν₁ : ProbabilityMeasure ℝ} (h0 : ∀ y, 0 ≤ f₀ y)
    (h1 : ∀ y, 0 ≤ f₁ y) (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hν₀ : (ν₀ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₀ x))
    (hν₁ : (ν₁ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₁ x))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (mixPM ν₀ ν₁ s : Measure ℝ) = (mixPM ν₀ ν₁ s₀ : Measure ℝ).withDensity
      fun y => (mixRatioNN f₀ f₁ s₀ s y : ℝ≥0∞) := by
  rw [coe_mixPM_eq_withDensity h0 h1 hf₀ hf₁ hν₀ hν₁ hs,
    coe_mixPM_eq_withDensity h0 h1 hf₀ hf₁ hν₀ hν₁ ⟨hs₀.1.le, hs₀.2.le⟩,
    ← withDensity_mul _ (measurable_mixDens hf₀ hf₁ s₀).ennreal_ofReal
      (measurable_mixRatioNN hf₀ hf₁ s₀ s).coe_nnreal_ennreal]
  congr 1
  funext y
  simp only [Pi.mul_apply]
  rw [mixDens_eq_mul h0 h1 hs₀ s y, ENNReal.ofReal_mul (mixDens_nonneg h0 h1
    ⟨hs₀.1.le, hs₀.2.le⟩ y), mixRatioNN]
  rfl

/-! ## Consequences at the base point -/

/-- The base law dominates the left endpoint: `ν₀ ≤ (1 - s₀)⁻¹ ν_{s₀}`. -/
theorem mixPM_le_smul_left (ν₀ ν₁ : ProbabilityMeasure ℝ) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    (ν₀ : Measure ℝ) ≤ ENNReal.ofReal (1 / (1 - s₀)) • (mixPM ν₀ ν₁ s₀ : Measure ℝ) := by
  have ha : 0 < 1 - s₀ := by linarith [hs₀.2]
  rw [coe_mixPM, mixParam_of_mem ⟨hs₀.1.le, hs₀.2.le⟩, Measure.le_iff']
  intro A
  have hc : ENNReal.ofReal (1 / (1 - s₀)) * ENNReal.ofReal (1 - s₀) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ ha.ne', ENNReal.ofReal_one]
  calc (ν₀ : Measure ℝ) A
      = ENNReal.ofReal (1 / (1 - s₀)) * (ENNReal.ofReal (1 - s₀) * (ν₀ : Measure ℝ) A) := by
        rw [← mul_assoc, hc, one_mul]
    _ ≤ ENNReal.ofReal (1 / (1 - s₀)) * (ENNReal.ofReal (1 - s₀) * (ν₀ : Measure ℝ) A +
          ENNReal.ofReal s₀ * (ν₁ : Measure ℝ) A) := by gcongr; exact le_self_add
    _ = _ := by
        simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]

/-- The base law dominates the right endpoint: `ν₁ ≤ s₀⁻¹ ν_{s₀}`. -/
theorem mixPM_le_smul_right (ν₀ ν₁ : ProbabilityMeasure ℝ) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) :
    (ν₁ : Measure ℝ) ≤ ENNReal.ofReal (1 / s₀) • (mixPM ν₀ ν₁ s₀ : Measure ℝ) := by
  have hb := hs₀.1
  rw [coe_mixPM, mixParam_of_mem ⟨hs₀.1.le, hs₀.2.le⟩, Measure.le_iff']
  intro A
  have hc : ENNReal.ofReal (1 / s₀) * ENNReal.ofReal s₀ = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hb.ne', ENNReal.ofReal_one]
  calc (ν₁ : Measure ℝ) A
      = ENNReal.ofReal (1 / s₀) * (ENNReal.ofReal s₀ * (ν₁ : Measure ℝ) A) := by
        rw [← mul_assoc, hc, one_mul]
    _ ≤ ENNReal.ofReal (1 / s₀) * (ENNReal.ofReal (1 - s₀) * (ν₀ : Measure ℝ) A +
          ENNReal.ofReal s₀ * (ν₁ : Measure ℝ) A) := by gcongr; exact le_add_self
    _ = _ := by
        simp only [Measure.smul_apply, Measure.add_apply, smul_eq_mul]

theorem Integrable.of_mixPM_left {ν₀ ν₁ : ProbabilityMeasure ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {a : ℝ → ℝ} (ha : Integrable a (mixPM ν₀ ν₁ s₀ : Measure ℝ)) :
    Integrable a (ν₀ : Measure ℝ) :=
  ha.of_measure_le_smul ENNReal.ofReal_ne_top (mixPM_le_smul_left ν₀ ν₁ hs₀)

theorem Integrable.of_mixPM_right {ν₀ ν₁ : ProbabilityMeasure ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {a : ℝ → ℝ} (ha : Integrable a (mixPM ν₀ ν₁ s₀ : Measure ℝ)) :
    Integrable a (ν₁ : Measure ℝ) :=
  ha.of_measure_le_smul ENNReal.ofReal_ne_top (mixPM_le_smul_right ν₀ ν₁ hs₀)

theorem lintegral_le_of_mixPM_left {ν₀ ν₁ : ProbabilityMeasure ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (a : ℝ → ℝ≥0∞) :
    ∫⁻ y, a y ∂(ν₀ : Measure ℝ) ≤
      ENNReal.ofReal (1 / (1 - s₀)) * ∫⁻ y, a y ∂(mixPM ν₀ ν₁ s₀ : Measure ℝ) := by
  rw [← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' (mixPM_le_smul_left ν₀ ν₁ hs₀) le_rfl

theorem lintegral_le_of_mixPM_right {ν₀ ν₁ : ProbabilityMeasure ℝ} {s₀ : ℝ}
    (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) (a : ℝ → ℝ≥0∞) :
    ∫⁻ y, a y ∂(ν₁ : Measure ℝ) ≤
      ENNReal.ofReal (1 / s₀) * ∫⁻ y, a y ∂(mixPM ν₀ ν₁ s₀ : Measure ℝ) := by
  rw [← smul_eq_mul, ← lintegral_smul_measure]
  exact lintegral_mono' (mixPM_le_smul_right ν₀ ν₁ hs₀) le_rfl

/-- **The score integrates against the difference of the endpoints**:
`∫ a h dν_{s₀} = ∫ a dν₁ - ∫ a dν₀`. -/
theorem integral_mul_mixScore {ν₀ ν₁ : ProbabilityMeasure ℝ} (h0 : ∀ y, 0 ≤ f₀ y)
    (h1 : ∀ y, 0 ≤ f₁ y) (hf₀ : Measurable f₀) (hf₁ : Measurable f₁)
    (hν₀ : (ν₀ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₀ x))
    (hν₁ : (ν₁ : Measure ℝ) = volume.withDensity fun x => ENNReal.ofReal (f₁ x))
    {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo (0 : ℝ) 1) {a : ℝ → ℝ}
    (ha : Integrable a (mixPM ν₀ ν₁ s₀ : Measure ℝ)) :
    ∫ y, a y * mixScore f₀ f₁ s₀ y ∂(mixPM ν₀ ν₁ s₀ : Measure ℝ) =
      ∫ y, a y ∂(ν₁ : Measure ℝ) - ∫ y, a y ∂(ν₀ : Measure ℝ) := by
  set νb := (mixPM ν₀ ν₁ s₀ : Measure ℝ) with hνb
  have hend : ∀ s ∈ Icc (0 : ℝ) 1, ∫ y, a y ∂(mixPM ν₀ ν₁ s : Measure ℝ) =
      ∫ y, mixRatio f₀ f₁ s₀ s y * a y ∂νb := by
    intro s hs
    rw [mixPM_eq_withDensity_ratio h0 h1 hf₀ hf₁ hν₀ hν₁ hs₀ hs,
      integral_withDensity_eq_integral_smul (measurable_mixRatioNN hf₀ hf₁ s₀ s)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, smul_eq_mul, coe_mixRatioNN h0 h1 hs₀ hs y]
  have hint : ∀ s, Integrable (fun y => mixRatio f₀ f₁ s₀ s y * a y) νb := by
    intro s
    refine (ha.norm.const_mul (1 + |s - s₀| * scoreBd s₀)).mono'
      ((measurable_mixRatio hf₀ hf₁ s₀ s).aestronglyMeasurable.mul ha.1) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_mixRatio_le h0 h1 hs₀ s y) (abs_nonneg _)
  have e1 := hend 1 ⟨zero_le_one, le_rfl⟩
  have e0 := hend 0 ⟨le_rfl, zero_le_one⟩
  rw [mixPM_one] at e1
  rw [mixPM_zero] at e0
  rw [e1, e0, ← integral_sub (hint 1) (hint 0)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mixRatio]
  ring

end

end PGM
