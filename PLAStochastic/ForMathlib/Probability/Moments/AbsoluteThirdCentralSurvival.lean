import PLAStochastic.ForMathlib.Probability.Moments.AbsoluteThirdCentral
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Survival-integral reduction for the absolute third central moment

The weighted layer-cake theorem supplies the integration over level sets.
The law need not be atomless: survival uses the strict event `t < X`.
-/

open MeasureTheory Set
open scoped ENNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- The antiderivative needed by the weighted layer-cake formula. -/
theorem integral_cubic_weight (a b : ℝ) :
    (∫ t in 0..b, 3 * (a - t) ^ 2) = a ^ 3 - (a - b) ^ 3 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => -(a - t) ^ 3) (3 * (a - t) ^ 2) t := by
    intro t
    have hs : HasDerivAt (fun x : ℝ => a - x) (-1) t := by
      simpa using! (hasDerivAt_const t a).sub (hasDerivAt_id t)
    simpa using! (hs.pow 3).neg
  have hi : IntervalIntegrable (fun t : ℝ => 3 * (a - t) ^ 2) volume 0 b :=
    (by fun_prop : Continuous (fun t : ℝ => 3 * (a - t) ^ 2)).intervalIntegrable 0 b
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi using 1
  ring

theorem sub_min_eq_lower_part (a x : ℝ) : a - min x a = max (a - x) 0 := by
  by_cases hx : x ≤ a
  · rw [min_eq_left hx, max_eq_left (sub_nonneg.mpr hx)]
  · have hax : a ≤ x := le_of_lt (lt_of_not_ge hx)
    rw [min_eq_right hax, max_eq_right (sub_nonpos.mpr hax), sub_self]

/-- Tail measure is a measurable function of its real threshold. -/
theorem measurable_tail_measure (μ : Measure Ω) (X : Ω → ℝ) :
    Measurable (fun t : ℝ => μ {ω | t < X ω}) :=
  Antitone.measurable (fun _ _ hst => measure_mono (fun _ h => lt_of_le_of_lt hst h))

section Probability

variable [IsProbabilityMeasure μ]

/-- `L³` makes the mean finite, and almost-everywhere nonnegativity makes it
nonnegative, as required for the finite survival-integration interval. -/
theorem integrable_and_mean_nonnegative (hX : MemLp X 3 μ) (hX₀ : 0 ≤ᵐ[μ] X) :
    Integrable X μ ∧ 0 ≤ ∫ ω, X ω ∂μ :=
  ⟨hX.integrable (by norm_num), integral_nonneg_of_ae hX₀⟩

/-- The finite-interval survival integrand is integrable, since a tail
probability is bounded by one and the polynomial weight is continuous. -/
theorem integrable_survival_weight (a : ℝ) :
    IntegrableOn (fun t : ℝ => (a - t) ^ 2 * μ.real {ω | t < X ω}) (Ioc 0 a) := by
  have hw : IntegrableOn (fun t : ℝ => (a - t) ^ 2) (Ioc 0 a) :=
    ((by fun_prop : Continuous (fun t : ℝ => (a - t) ^ 2)).intervalIntegrable 0 a).1
  apply hw.mul_bdd (c := 1) (measurable_tail_measure μ X).ennreal_toReal.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun t => by
    change |μ.real {ω | t < X ω}| ≤ 1
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one

/-- For a nonnegative random variable, the lower third partial moment is the
constant cube minus the weighted survival integral. This is obtained from
weighted layer cake, rather than assumed as an expectation identity. -/
theorem integral_lower_cube_survival (hX : MemLp X 3 μ)
    (hX₀ : 0 ≤ᵐ[μ] X) {a : ℝ} (ha : 0 ≤ a) :
    (∫ ω, max (a - X ω) 0 ^ 3 ∂μ) =
      a ^ 3 - 3 * (∫ t in 0..a, (a - t) ^ 2 * μ.real {ω | t < X ω}) := by
  have hm : MemLp (fun ω => min (X ω) a) 3 μ := hX.inf (memLp_const a)
  have hm₀ : 0 ≤ᵐ[μ] (fun ω => min (X ω) a) :=
    hX₀.mono fun _ h => le_min h ha
  have hg₀ : ∀ t : ℝ, 0 ≤ 3 * (a - t) ^ 2 := fun _ => by positivity
  have hgi : ∀ b > 0, IntervalIntegrable (fun t : ℝ => 3 * (a - t) ^ 2) volume 0 b :=
    fun b _ => (by fun_prop : Continuous (fun t : ℝ => 3 * (a - t) ^ 2)).intervalIntegrable 0 b
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ hm₀ hm.aemeasurable hgi
    (Filter.Eventually.of_forall hg₀)
  simp_rw [integral_cubic_weight, sub_min_eq_lower_part] at hlayer
  have htail : (fun t : ℝ => μ {ω | t < min (X ω) a} * ENNReal.ofReal (3 * (a - t) ^ 2)) =
      (Iio a).indicator (fun t : ℝ => μ {ω | t < X ω} * ENNReal.ofReal (3 * (a - t) ^ 2)) := by
    funext t
    by_cases ht : t < a <;> simp [Set.indicator, ht]
  rw [htail, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio] at hlayer
  have hset : Iio a ∩ Ioi (0 : ℝ) = Ioo 0 a := by ext t; simp only [mem_inter_iff, mem_Iio, mem_Ioi, mem_Ioo]; tauto
  rw [hset] at hlayer
  have hl := (integrable_third_central_terms hX a).2.2
  have hG : Integrable (fun ω => a ^ 3 - max (a - X ω) 0 ^ 3) μ :=
    (integrable_const (a ^ 3)).sub hl
  have hG₀ : 0 ≤ᵐ[μ] (fun ω => a ^ 3 - max (a - X ω) 0 ^ 3) := by
    filter_upwards [hm₀] with ω hω
    rw [← sub_min_eq_lower_part, ← integral_cubic_weight]
    exact intervalIntegral.integral_nonneg_of_forall hω hg₀
  have hP : Measurable
      (fun t : ℝ => μ {ω | t < X ω} * ENNReal.ofReal (3 * (a - t) ^ 2)) :=
    (measurable_tail_measure μ X).mul ((by fun_prop :
      Measurable (fun t : ℝ => 3 * (a - t) ^ 2)).ennreal_ofReal)
  have hPfin : ∀ᵐ t ∂volume.restrict (Ioo 0 a),
      μ {ω | t < X ω} * ENNReal.ofReal (3 * (a - t) ^ 2) < ∞ := by
    exact Filter.Eventually.of_forall fun _ => ENNReal.mul_lt_top (measure_lt_top _ _)
      ENNReal.ofReal_lt_top
  have hreal := congrArg ENNReal.toReal hlayer
  rw [← integral_eq_lintegral_of_nonneg_ae hG₀ hG.aestronglyMeasurable,
    ← integral_toReal hP.aemeasurable hPfin] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hg₀ _)] at hreal
  have hrewrite : (fun t : ℝ => (μ {ω | t < X ω}).toReal * (3 * (a - t) ^ 2)) =
      (fun t : ℝ => 3 * ((a - t) ^ 2 * μ.real {ω | t < X ω})) := by
    funext t
    simp only [Measure.real]
    ring
  rw [hrewrite, integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ha] at hreal
  rw [integral_sub (integrable_const (a ^ 3)) hl] at hreal
  simp only [integral_const, probReal_univ, one_smul] at hreal
  linarith

/-- The unstandardized second identity in the appendix lemma follows by
combining the first expectation identity with its survival reduction. -/
theorem integral_absolute_third_central_survival (hX : MemLp X 3 μ)
    (hX₀ : 0 ≤ᵐ[μ] X) :
    (∫ ω, |X ω - ∫ z, X z ∂μ| ^ 3 ∂μ) =
      (∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ∂μ) * (∫ ω, X ω ^ 2 ∂μ) +
        4 * (∫ ω, X ω ∂μ) ^ 3 -
          6 * (∫ t in 0..(∫ z, X z ∂μ),
            ((∫ z, X z ∂μ) - t) ^ 2 * μ.real {ω | t < X ω}) := by
  rw [integral_absolute_third_central hX,
    integral_lower_cube_survival hX hX₀ (integrable_and_mean_nonnegative hX hX₀).2]
  ring

/-- Dividing the proved survival identity by a positive variance scale gives the
second displayed formula of the appendix lemma. The caller supplies that variance. -/
theorem standardized_absolute_third_central_survival (hX : MemLp X 3 μ)
    (hX₀ : 0 ≤ᵐ[μ] X) {V : ℝ} (hV : 0 < V) :
    (∫ ω, |X ω - ∫ z, X z ∂μ| ^ 3 ∂μ) / V ^ (3 / 2 : ℝ) =
      ((∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ∂μ) * (∫ ω, X ω ^ 2 ∂μ) +
        4 * (∫ ω, X ω ∂μ) ^ 3 -
          6 * (∫ t in 0..(∫ z, X z ∂μ),
            ((∫ z, X z ∂μ) - t) ^ 2 * μ.real {ω | t < X ω})) / V ^ (3 / 2 : ℝ) := by
  have hden : V ^ (3 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hV _)
  apply (div_eq_div_iff hden hden).2
  rw [integral_absolute_third_central_survival hX hX₀]

end Probability

end BrownianAffine
