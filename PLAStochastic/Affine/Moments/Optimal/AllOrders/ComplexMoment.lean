import PLAStochastic.Affine.Moments.Optimal.Survival.ImageSeries
import PLAStochastic.ForMathlib.Probability.Moments.SmallBallNegativeMoments
import PLAStochastic.ForMathlib.Probability.Moments.ComplexPowerMoment

/-!
# The complex moment function of the optimal Brownian lifetime

The proved image series gives the small-time bound `μ {τ ≤ t} ≤ C exp (-8 / t)`
for `0 < t ≤ 1`. Together with the geometric tail this makes every real power of
`τ = optimalUnitLifetime B` integrable, so `q ↦ E τ ^ q` is entire. At natural numbers
it is the real moment, and for `Re q < 0` it is the Mellin transform of `S(t) - 1`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The constant of the small-time survival bound. -/
def optimalSmallTimeConstant : ℝ :=
  Real.exp 8 * ∑' n, optimalImageGaussianBound 1 n

/-- Below time one, the Gaussian image bound is dominated by its value at time one. -/
theorem optimalImageGaussianBound_le_small (n : ℕ) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    optimalImageGaussianBound t n ≤
      Real.exp 8 * Real.exp (-8 / t) * optimalImageGaussianBound 1 n := by
  unfold optimalImageGaussianBound
  set m : ℝ := (n : ℝ) + 1
  have hm : 1 ≤ m := by simp only [m]; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hm2 : 0 ≤ m ^ 2 - 1 := by nlinarith
  have hdiv : m ^ 2 - 1 ≤ (m ^ 2 - 1) / t := by
    rw [le_div_iff₀ ht0]
    nlinarith
  have hexp : Real.exp (-8 * m ^ 2 / t) ≤
      Real.exp 8 * Real.exp (-8 / t) * Real.exp (-8 * m ^ 2 / 1) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hsplit : -8 * m ^ 2 / t = -8 / t + -8 * ((m ^ 2 - 1) / t) := by
      field_simp
      ring
    rw [hsplit, div_one]
    nlinarith
  calc
    (40 * m ^ 2 + 4 * t) * Real.exp (-8 * m ^ 2 / t) ≤
        (40 * m ^ 2 + 4) * (Real.exp 8 * Real.exp (-8 / t) * Real.exp (-8 * m ^ 2 / 1)) :=
      mul_le_mul (by linarith) hexp (Real.exp_nonneg _) (by positivity)
    _ = Real.exp 8 * Real.exp (-8 / t) *
        ((40 * m ^ 2 + 4 * 1) * Real.exp (-8 * m ^ 2 / 1)) := by ring

/-- The image series is exponentially close to one at small times. -/
theorem one_sub_optimalImageSeries_le {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    1 - optimalImageSeries t ≤ optimalSmallTimeConstant * Real.exp (-8 / t) := by
  have hsum := summable_optimalImageGaussianBound ht0
  have hsum₁ := summable_optimalImageGaussianBound (zero_lt_one : (0 : ℝ) < 1)
  calc
    1 - optimalImageSeries t = -∑' n, optimalImageMode n t := by
      rw [optimalImageSeries]
      ring
    _ ≤ ‖∑' n, optimalImageMode n t‖ := neg_le_abs _
    _ ≤ ∑' n, ‖optimalImageMode n t‖ := norm_tsum_le_tsum_norm (summable_norm_optimalImageMode t)
    _ ≤ ∑' n, optimalImageGaussianBound t n :=
      (summable_norm_optimalImageMode t).tsum_le_tsum
        (fun n => optimalImageMode_gaussian_bound n ht0 le_rfl) hsum
    _ ≤ ∑' n, Real.exp 8 * Real.exp (-8 / t) * optimalImageGaussianBound 1 n :=
      hsum.tsum_le_tsum (fun n => optimalImageGaussianBound_le_small n ht0 ht1)
        (hsum₁.mul_left _)
    _ = optimalSmallTimeConstant * Real.exp (-8 / t) := by
      rw [tsum_mul_left, optimalSmallTimeConstant]
      ring

/-- The actual optimal lifetime is exponentially unlikely to be small. -/
theorem optimalUnitLifetime_measureReal_le_small (hB : IsBrownianReal B μ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    μ.real {ω | optimalUnitLifetime B ω ≤ t} ≤ optimalSmallTimeConstant * Real.exp (-8 / t) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  have hcompl : {ω | optimalUnitLifetime B ω ≤ t} = {ω | t < optimalUnitLifetime B ω}ᶜ := by
    ext ω
    simp [not_lt]
  have hnull : NullMeasurableSet {ω | t < optimalUnitLifetime B ω} μ :=
    (aemeasurable_optimalUnitLifetime hB).nullMeasurableSet_preimage measurableSet_Ioi
  rw [hcompl, measureReal_compl₀ hnull, probReal_univ, ← optimalImageSeries_eq_measureReal hB t]
  exact one_sub_optimalImageSeries_le ht0 ht1

/-- Every negative power of the actual optimal lifetime is integrable. -/
theorem optimalUnitLifetime_integrable_rpow_neg (hB : IsBrownianReal B μ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun ω => optimalUnitLifetime B ω ^ (-s)) μ := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  apply integrable_rpow_neg_of_small_ball (aemeasurable_optimalUnitLifetime hB)
    (optimalUnitLifetime_positive_ae hB) (C := optimalSmallTimeConstant) (by norm_num : (0 : ℝ) < 8)
    _ hs
  intro t ht0 ht1
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (optimalUnitLifetime_measureReal_le_small hB ht0 ht1)

/-- Every real power of the actual optimal lifetime is integrable. -/
theorem optimalUnitLifetime_integrable_rpow_real (hB : IsBrownianReal B μ) (p : ℝ) :
    Integrable (fun ω => optimalUnitLifetime B ω ^ p) μ := by
  rcases le_or_gt 0 p with hp | hp
  · exact optimalUnitLifetime_integrable_rpow hB hp
  · simpa only [neg_neg] using optimalUnitLifetime_integrable_rpow_neg hB (s := -p) (by linarith)

/-- The complex moment function `q ↦ E τ ^ q` of the actual optimal unit lifetime. -/
def optimalComplexMoment (B : ℝ≥0 → Ω → ℝ) (μ : Measure Ω) (q : ℂ) : ℂ :=
  ∫ ω, ((optimalUnitLifetime B ω : ℝ) : ℂ) ^ q ∂μ

/-- The complex moment function is entire. -/
theorem differentiable_optimalComplexMoment (hB : IsBrownianReal B μ) :
    Differentiable ℂ (optimalComplexMoment B μ) :=
  differentiable_integral_ofReal_cpow (aemeasurable_optimalUnitLifetime hB)
    (optimalUnitLifetime_positive_ae hB) (optimalUnitLifetime_integrable_rpow_real hB)

/-- At natural numbers the complex moment function is the real moment. This identity holds
for every process and measure, so no Brownian hypothesis is needed. -/
theorem optimalComplexMoment_natCast (n : ℕ) :
    optimalComplexMoment B μ n = ((∫ ω, optimalUnitLifetime B ω ^ n ∂μ : ℝ) : ℂ) := by
  have hn : (fun ω => ((optimalUnitLifetime B ω : ℝ) : ℂ) ^ (n : ℂ)) =
      fun ω => ((optimalUnitLifetime B ω ^ n : ℝ) : ℂ) := by
    funext ω
    rw [Complex.cpow_natCast, Complex.ofReal_pow]
  rw [optimalComplexMoment, hn, integral_complex_ofReal]

/-- For `Re q < 0`, the complex moment is the Mellin transform of the survival defect. -/
theorem optimalComplexMoment_eq_mellin (hB : IsBrownianReal B μ) {q : ℂ} (hq : q.re < 0) :
    optimalComplexMoment B μ q =
      q * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) *
        (((μ.real {ω | t < optimalUnitLifetime B ω}) : ℂ) - 1) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_ofReal_cpow_eq_mellin (aemeasurable_optimalUnitLifetime hB)
    (optimalUnitLifetime_positive_ae hB) hq (optimalUnitLifetime_integrable_rpow_real hB q.re)

/-- The same Mellin form with the explicit image series as the survival function. -/
theorem optimalComplexMoment_eq_mellin_imageSeries (hB : IsBrownianReal B μ) {q : ℂ}
    (hq : q.re < 0) :
    optimalComplexMoment B μ q =
      q * ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((optimalImageSeries t : ℂ) - 1) := by
  simp_rw [optimalImageSeries_eq_measureReal hB]
  exact optimalComplexMoment_eq_mellin hB hq

end BrownianAffine
