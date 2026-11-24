import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.DirichletHeatKernel.SineOrthogonality
import PLAStochastic.Brownian.Killed.EndpointMeasure

/-!
The positive and negative parts of the analytic kernel, as finite measures. Their
comparison with the actual killed measure avoids assuming positivity of the series.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Positive part of the analytic series; positivity of the series itself is not assumed. -/
def heatPositivePart (r t x z : ℝ) : ℝ := max (dirichletHeatKernel r t x z) 0

def heatNegativePart (r t x z : ℝ) : ℝ := max (-dirichletHeatKernel r t x z) 0

def heatPositiveMeasure (r t x : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 r)).withDensity (fun z => ENNReal.ofReal (heatPositivePart r t x z))

def heatNegativeMeasure (r t x : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 r)).withDensity (fun z => ENNReal.ofReal (heatNegativePart r t x z))

theorem continuous_dirichletHeatKernel_right {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    Continuous (dirichletHeatKernel r t x) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (hasDerivAt_heatSpatialSeries_right hr ht 0 0 x z).continuousAt

theorem continuous_heatPositivePart {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    Continuous (heatPositivePart r t x) :=
  (continuous_dirichletHeatKernel_right hr ht x).max continuous_const

theorem continuous_heatNegativePart {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    Continuous (heatNegativePart r t x) :=
  (continuous_dirichletHeatKernel_right hr ht x).neg.max continuous_const

theorem heatPositivePart_nonneg (r t x z : ℝ) : 0 ≤ heatPositivePart r t x z := le_max_right _ _

theorem heatNegativePart_nonneg (r t x z : ℝ) : 0 ≤ heatNegativePart r t x z := le_max_right _ _

theorem heatPositivePart_sub_negativePart (r t x z : ℝ) :
    heatPositivePart r t x z - heatNegativePart r t x z = dirichletHeatKernel r t x z := by
  unfold heatPositivePart heatNegativePart
  by_cases h : 0 ≤ dirichletHeatKernel r t x z
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have h' := le_of_not_ge h
    rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
    ring

theorem heatPositiveMeasure_isFiniteMeasure {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    IsFiniteMeasure (heatPositiveMeasure r t x) := by
  have hi : IntegrableOn (heatPositivePart r t x) (Icc 0 r) :=
    (continuous_heatPositivePart hr ht x).continuousOn.integrableOn_compact isCompact_Icc
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Eventually.of_forall fun z => heatPositivePart_nonneg r t x z)).mpr hi

theorem heatNegativeMeasure_isFiniteMeasure {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    IsFiniteMeasure (heatNegativeMeasure r t x) := by
  have hi : IntegrableOn (heatNegativePart r t x) (Icc 0 r) :=
    (continuous_heatNegativePart hr ht x).continuousOn.integrableOn_compact isCompact_Icc
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Eventually.of_forall fun z => heatNegativePart_nonneg r t x z)).mpr hi

theorem heatPositiveMeasure_absolutelyContinuous (r t x : ℝ) : heatPositiveMeasure r t x ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

theorem heatNegativeMeasure_absolutelyContinuous (r t x : ℝ) : heatNegativeMeasure r t x ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict

theorem heatPositiveMeasure_compl_Icc (r t x : ℝ) : heatPositiveMeasure r t x (Icc 0 r)ᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ (by simp)

theorem heatNegativeMeasure_compl_Icc (r t x : ℝ) : heatNegativeMeasure r t x (Icc 0 r)ᶜ = 0 :=
  withDensity_absolutelyContinuous _ _ (by simp)

theorem integral_heatPositiveMeasure {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) (f : ℝ → ℝ) :
    (∫ z, f z ∂heatPositiveMeasure r t x) = ∫ z in Icc 0 r, heatPositivePart r t x z * f z := by
  rw [heatPositiveMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_heatPositivePart hr ht x).measurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (heatPositivePart_nonneg r t x _), smul_eq_mul]

theorem integral_heatNegativeMeasure {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) (f : ℝ → ℝ) :
    (∫ z, f z ∂heatNegativeMeasure r t x) = ∫ z in Icc 0 r, heatNegativePart r t x z * f z := by
  rw [heatNegativeMeasure, integral_withDensity_eq_integral_toReal_smul
    ((continuous_heatNegativePart hr ht x).measurable.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (heatNegativePart_nonneg r t x _), smul_eq_mul]

/-- The positive and negative parts are mutually singular without any positivity assertion. -/
theorem heatPositiveMeasure_eq_density (r t x : ℝ) :
    heatPositiveMeasure r t x = (volume.restrict (Icc 0 r)).withDensity
      (fun z => ENNReal.ofReal (dirichletHeatKernel r t x z)) := by
  unfold heatPositiveMeasure
  apply congrArg ((volume.restrict (Icc 0 r)).withDensity)
  funext z
  simp [heatPositivePart, ENNReal.ofReal_max]

theorem heatNegativeMeasure_eq_density (r t x : ℝ) :
    heatNegativeMeasure r t x = (volume.restrict (Icc 0 r)).withDensity
      (fun z => ENNReal.ofReal (-dirichletHeatKernel r t x z)) := by
  unfold heatNegativeMeasure
  apply congrArg ((volume.restrict (Icc 0 r)).withDensity)
  funext z
  simp [heatNegativePart, ENNReal.ofReal_max]

theorem heatPositiveMeasure_mutuallySingular_negative {r t : ℝ}
    (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    heatPositiveMeasure r t x ⟂ₘ heatNegativeMeasure r t x := by
  rw [heatPositiveMeasure_eq_density, heatNegativeMeasure_eq_density]
  exact withDensity_ofReal_mutuallySingular
    (continuous_dirichletHeatKernel_right hr ht x).measurable

/-- Any positive measure identified with the signed kernel forces the negative part to vanish. -/
theorem heatNegativeMeasure_eq_zero_of_add_eq {r t x : ℝ} {ν : Measure ℝ}
    (hr : 0 < r) (ht : 0 < t)
    (h : ν + heatNegativeMeasure r t x = heatPositiveMeasure r t x) :
    heatNegativeMeasure r t x = 0 := by
  have hle : heatNegativeMeasure r t x ≤ heatPositiveMeasure r t x := by
    rw [← h]
    exact Measure.le_add_left le_rfl
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
    hle.absolutelyContinuous (heatPositiveMeasure_mutuallySingular_negative hr ht x).symm

theorem ae_mem_Ioo_of_ae_mem_Icc_of_ac {ν : Measure ℝ} {r : ℝ}
    (h : ∀ᵐ z ∂ν, z ∈ Icc 0 r) (hac : ν ≪ volume) :
    ∀ᵐ z ∂ν, z ∈ Ioo 0 r := by
  have h0 : ∀ᵐ z ∂ν, z ≠ 0 := by
    rw [ae_iff]
    exact hac (by simp)
  have hr : ∀ᵐ z ∂ν, z ≠ r := by
    rw [ae_iff]
    exact hac (by simp)
  filter_upwards [h, h0, hr] with z hz hz0 hzr
  exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hz0), lt_of_le_of_ne hz.2 hzr⟩

theorem heatPositiveMeasure_ae_mem_Ioo (r t x : ℝ) :
    ∀ᵐ z ∂heatPositiveMeasure r t x, z ∈ Ioo 0 r :=
  ae_mem_Ioo_of_ae_mem_Icc_of_ac
    (ae_iff.mpr (heatPositiveMeasure_compl_Icc r t x))
    (heatPositiveMeasure_absolutelyContinuous r t x)

theorem heatNegativeMeasure_ae_mem_Ioo (r t x : ℝ) :
    ∀ᵐ z ∂heatNegativeMeasure r t x, z ∈ Ioo 0 r :=
  ae_mem_Ioo_of_ae_mem_Icc_of_ac
    (ae_iff.mpr (heatNegativeMeasure_compl_Icc r t x))
    (heatNegativeMeasure_absolutelyContinuous r t x)

theorem integral_sine_heatParts_sub {r t : ℝ} (hr : 0 < r) (ht : 0 < t)
    (x : ℝ) (n : ℕ) :
    (∫ z, Real.sin (heatFrequency r n * z) ∂heatPositiveMeasure r t x) -
      (∫ z, Real.sin (heatFrequency r n * z) ∂heatNegativeMeasure r t x) =
      Real.sin (heatFrequency r n * x) * Real.exp (-(heatFrequency r n ^ 2) * t / 2) := by
  rw [integral_heatPositiveMeasure hr ht, integral_heatNegativeMeasure hr ht]
  have hp : IntegrableOn (fun z => heatPositivePart r t x z *
      Real.sin (heatFrequency r n * z)) (Icc 0 r) :=
    ((continuous_heatPositivePart hr ht x).mul (by fun_prop)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hn : IntegrableOn (fun z => heatNegativePart r t x z *
      Real.sin (heatFrequency r n * z)) (Icc 0 r) :=
    ((continuous_heatNegativePart hr ht x).mul (by fun_prop)).continuousOn.integrableOn_compact
      isCompact_Icc
  rw [← integral_sub hp hn]
  simp_rw [← sub_mul, heatPositivePart_sub_negativePart]
  exact integral_dirichletHeatKernel_mul_sine hr ht x n

theorem integrable_heatSine {ν : Measure ℝ} [IsFiniteMeasure ν] (r : ℝ) (n : ℕ) :
    Integrable (fun z => Real.sin (heatFrequency r n * z)) ν := by
  apply Integrable.of_bound (by fun_prop) 1
  exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

theorem integral_sine_killed_add_negative_eq_positive (hB : IsBrownianReal B μ)
    {x r : ℝ} (hr : 0 < r) (hx : x ∈ Icc 0 r) {T : ℝ≥0} (hT : 0 < T) (n : ℕ) :
    (∫ z, Real.sin (heatFrequency r n * z) ∂(killedBrownianMeasure B μ x r T +
      heatNegativeMeasure r T x)) =
      ∫ z, Real.sin (heatFrequency r n * z) ∂heatPositiveMeasure r T x := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (heatNegativeMeasure r T x) :=
    heatNegativeMeasure_isFiniteMeasure hr (show (0 : ℝ) < T from hT) x
  rw [integral_add_measure (integrable_heatSine r n) (integrable_heatSine r n),
    integral_sine_killedBrownianMeasure hB hr hx T n]
  have h := integral_sine_heatParts_sub hr (show (0 : ℝ) < T from hT) x n
  nlinarith

end BrownianAffine
