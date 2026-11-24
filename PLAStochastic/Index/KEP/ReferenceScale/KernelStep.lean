import PLAStochastic.Index.GEP.Kernel.Row.FreeDensity
import PLAStochastic.ForMathlib.Analysis.Calculus.TruncatedConvolution
import PLAStochastic.ForMathlib.MeasureTheory.Measure.Lebesgue.WeightedAffineDensity
import PLAStochastic.ForMathlib.Probability.Hellinger.Density

/-!
# The final actual killed convolution steps

The input row is the existing pointwise `krDens`. Its final interval projection
is removed only to obtain a smooth representative on the interior. The second
derivative identity retains the two boundary terms created by the intermediate
projection.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

def kepStepSpatial (f : ℝ → ℝ) (β a t : ℝ) : ℝ := f ((β - t) / a) / |a|

def kepStepSpatialFirst (f' : ℝ → ℝ) (β a t : ℝ) : ℝ :=
  -(f' ((β - t) / a)) / (a * |a|)

def kepStepSpatialSecond (f'' : ℝ → ℝ) (β a t : ℝ) : ℝ :=
  f'' ((β - t) / a) / (a ^ 2 * |a|)

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepStepSpatial {f f' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (β a t : ℝ) :
    HasDerivAt (kepStepSpatial f β a) (kepStepSpatialFirst f' β a t) t := by
  convert ((hd ((β - t) / a)).comp t
    (((hasDerivAt_const t β).sub (hasDerivAt_id t)).div_const a)).div_const |a|
    using 1 <;> first | rfl | (dsimp [kepStepSpatialFirst]; ring)

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_kepStepSpatialFirst {f' f'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f' (f'' x) x) (β a t : ℝ) :
    HasDerivAt (kepStepSpatialFirst f' β a) (kepStepSpatialSecond f'' β a t) t := by
  convert (((hd ((β - t) / a)).comp t
    (((hasDerivAt_const t β).sub (hasDerivAt_id t)).div_const a)).neg).div_const
    (a * |a|) using 1 <;> first | rfl | (dsimp [kepStepSpatialSecond]; ring)

theorem continuous_kepStepSpatial {f : ℝ → ℝ} (hf : Continuous f) (β a : ℝ) :
    Continuous (kepStepSpatial f β a) :=
  (hf.comp ((continuous_const.sub continuous_id).div_const a)).div_const |a|

theorem continuous_kepStepSpatialFirst {f' : ℝ → ℝ} (hf : Continuous f') (β a : ℝ) :
    Continuous (kepStepSpatialFirst f' β a) :=
  ((hf.comp ((continuous_const.sub continuous_id).div_const a)).neg).div_const (a * |a|)

theorem continuous_kepStepSpatialSecond {f'' : ℝ → ℝ} (hf : Continuous f'') (β a : ℝ) :
    Continuous (kepStepSpatialSecond f'' β a) :=
  (hf.comp ((continuous_const.sub continuous_id).div_const a)).div_const (a ^ 2 * |a|)

theorem integrable_kepStepSpatialFirst {f' : ℝ → ℝ} (hf' : Integrable f' volume)
    {a : ℝ} (ha : a ≠ 0) (β : ℝ) : Integrable (kepStepSpatialFirst f' β a) volume := by
  have h : Integrable (fun x => f' (x / a)) volume := by
    convert hf'.comp_mul_left' (inv_ne_zero ha) using 1
    funext x
    rw [div_eq_mul_inv, mul_comm]
  exact ((h.comp_sub_left β).neg).div_const (a * |a|)

/-- The exact derivative scale, including the small-slope denominator. -/
theorem integral_abs_kepStepSpatialFirst (f' : ℝ → ℝ) (β : ℝ) {a : ℝ} (ha : a ≠ 0) :
    (∫ t, |kepStepSpatialFirst f' β a t|) = (∫ x, |f' x|) / |a| := by
  simp only [kepStepSpatialFirst, abs_div, abs_neg, abs_mul, abs_abs]
  rw [integral_div, integral_sub_left_eq_self (fun x => |f' (x / a)|) volume β,
    Measure.integral_comp_div (fun x => |f' x|) a, smul_eq_mul]
  field_simp

theorem integral_abs_kepStepSpatialSecond (f'' : ℝ → ℝ) (β : ℝ) {a : ℝ} (ha : a ≠ 0) :
    (∫ t, |kepStepSpatialSecond f'' β a t|) = (∫ x, |f'' x|) / |a| ^ 2 := by
  simp only [kepStepSpatialSecond, abs_div, abs_mul, abs_pow, abs_abs]
  rw [integral_div, integral_sub_left_eq_self (fun x => |f'' (x / a)|) volume β,
    Measure.integral_comp_div (fun x => |f'' x|) a, smul_eq_mul]
  field_simp

def kepStepDensity (p : HellingerDensity (volume : Measure ℝ)) (β a : ℝ) (ha : a ≠ 0) :
    HellingerDensity (volume : Measure ℝ) where
  density := kepStepSpatial p.density β a
  measurable := (p.measurable.comp
    ((measurable_const.sub measurable_id).div_const a)).div_const |a|
  nonneg := fun x => div_nonneg (p.nonneg _) (abs_nonneg a)
  integrable := by
    have h : Integrable (fun x => p.density (x / a)) volume := by
      convert p.integrable.comp_mul_left' (inv_ne_zero ha) using 1
      funext x
      rw [div_eq_mul_inv, mul_comm]
    exact (h.comp_sub_left β).div_const |a|
  integral_eq_one := by
    simp only [kepStepSpatial, integral_div]
    rw [integral_sub_left_eq_self (fun x => p.density (x / a)) volume β,
      Measure.integral_comp_div p.density a, smul_eq_mul, p.integral_eq_one, mul_one,
      div_self (abs_ne_zero.mpr ha)]

def kepFinalConvolution (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w β a : ℝ) (n : ℕ) (x y : ℝ) : ℝ :=
  truncatedConvolution 0 w (kepStepSpatial f β a)
    (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z) y

variable (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D w β a : ℝ}

/-- The smooth final-convolution representative is the actual row on the band. -/
theorem krDens_eq_kepFinalConvolution (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (n : ℕ) (x : ℝ) {y : ℝ} (hy : y ∈ Icc 0 w) :
    krDens (Icc 0 w) ν f β a (n + 2) x y = kepFinalConvolution ν f w β a n x y := by
  have hn : n + 2 = n + 1 + (0 + 1) := by omega
  rw [hn, krDens_add ν measurableSet_Icc (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hf hf0 hfD hν ha n 0 x y]
  change (∫ z, krDens (Icc 0 w) ν f β a (n + 1) x z *
    krDens (Icc 0 w) ν f β a 1 z y) = _
  simp_rw [krDens_one]
  unfold kepFinalConvolution truncatedConvolution
  rw [← integral_Icc_eq_integral_Ioc]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    by_cases hz : z ∈ Icc (0 : ℝ) w
    · rw [indicator_of_mem hz]
      simp only [krKer, indicator_of_mem hz, indicator_of_mem hy, one_mul]
      unfold kepStepSpatial
      rw [mul_comm, show β - (y - z) = z + β - y by ring]
    · rw [indicator_of_notMem hz, krDens_eq_zero_of_right_notMem ν hz, zero_mul]

theorem hasDerivAt_kepFinalConvolution {f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt f (f' x) x) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (n : ℕ) (x y : ℝ) :
    HasDerivAt (kepFinalConvolution ν f w β a n x)
      (truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z) y) y :=
  hasDerivAt_truncatedConvolution (continuous_kepStepSpatial hf β a)
    (continuous_kepStepSpatialFirst hf' β a) (hasDerivAt_kepStepSpatial hd β a)
    (kr_integrable_krDens_right ν measurableSet_Icc (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hf.measurable
      hf0 hfD (n + 1) x).integrableOn y

theorem hasDerivAt_kepFinalConvolutionFirst {f' f'' : ℝ → ℝ}
    (hf : Measurable f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x, HasDerivAt f' (f'' x) x) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (n : ℕ) (x y : ℝ) :
    HasDerivAt (truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
      (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z))
      (truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z) y) y :=
  hasDerivAt_truncatedConvolution (continuous_kepStepSpatialFirst hf' β a)
    (continuous_kepStepSpatialSecond hf'' β a) (hasDerivAt_kepStepSpatialFirst hd β a)
    (kr_integrable_krDens_right ν measurableSet_Icc (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hf
      hf0 hfD (n + 1) x).integrableOn y

theorem hasDerivAt_krDens_interior {f' : ℝ → ℝ}
    (hf : Continuous f) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt f (f' x) x) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (n : ℕ) (x : ℝ) {y : ℝ} (hy : y ∈ Ioo 0 w) :
    HasDerivAt (fun z => krDens (Icc 0 w) ν f β a (n + 2) x z)
      (truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z) y) y := by
  apply (hasDerivAt_kepFinalConvolution ν hf hf' hd hf0 hfD n x y).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
  exact krDens_eq_kepFinalConvolution ν hf.measurable hf0 hfD hν ha n x
    ⟨hz.1.le, hz.2.le⟩

/-- Both final actual convolutions are retained before moving one derivative
to the intermediate row. In particular its two endpoint values are present. -/
theorem kepFinalConvolution_second_boundary {f' f'' : ℝ → ℝ}
    (hw : 0 ≤ w) (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (n : ℕ) (x y : ℝ) :
    truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 2) x z) y =
      truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
        (truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
          (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z)) y +
        kepStepSpatialFirst f' β a y * kepFinalConvolution ν f w β a n x 0 -
        kepStepSpatialFirst f' β a (y - w) * kepFinalConvolution ν f w β a n x w := by
  have hv' : Continuous (truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
      (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z)) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_kepFinalConvolutionFirst ν (w := w) (β := β) (a := a)
        hf.measurable hf' hf'' hdd hf0 hfD n x z).continuousAt
  have he : truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 2) x z) y =
      truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (kepFinalConvolution ν f w β a n x) y := by
    unfold truncatedConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [krDens_eq_kepFinalConvolution ν (β := β) hf.measurable hf0 hfD hν ha n x
      ⟨hz.1.le, hz.2⟩]
  rw [he]
  simpa only [sub_zero] using
    truncatedConvolution_second_eq hw (continuous_kepStepSpatialSecond hf'' β a) hv'
      (hasDerivAt_kepStepSpatialFirst hdd β a)
      (hasDerivAt_kepFinalConvolution ν hf hf' hd hf0 hfD n x) y

/-- The endpoint-aware estimate for the actual intermediate row. Its derivative
bound can later be supplied by the existing long-row BV decomposition. -/
theorem kepFinalConvolution_second_boundary_bound {f' f'' : ℝ → ℝ}
    (hw : 0 ≤ w) (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hfi' : Integrable f' volume)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hdd : ∀ x, HasDerivAt f' (f'' x) x)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (ha : a ≠ 0) (n : ℕ) (x : ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hvV : ∀ z ∈ Ioc 0 w, |truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
      (fun t => krDens (Icc 0 w) ν f β a (n + 1) x t) z| ≤ V) (y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 2) x z) y| ≤
      V * ((∫ t, |f' t|) / |a|) +
        |kepStepSpatialFirst f' β a y| * |kepFinalConvolution ν f w β a n x 0| +
        |kepStepSpatialFirst f' β a (y - w)| * |kepFinalConvolution ν f w β a n x w| := by
  have hv' : Continuous (truncatedConvolution 0 w (kepStepSpatialFirst f' β a)
      (fun z => krDens (Icc 0 w) ν f β a (n + 1) x z)) :=
    continuous_iff_continuousAt.mpr fun z =>
      (hasDerivAt_kepFinalConvolutionFirst ν (w := w) (β := β) (a := a)
        hf.measurable hf' hf'' hdd hf0 hfD n x z).continuousAt
  have he : truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (fun z => krDens (Icc 0 w) ν f β a (n + 2) x z) y =
      truncatedConvolution 0 w (kepStepSpatialSecond f'' β a)
        (kepFinalConvolution ν f w β a n x) y := by
    unfold truncatedConvolution
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z hz
    dsimp only
    rw [krDens_eq_kepFinalConvolution ν (β := β) hf.measurable hf0 hfD hν ha n x
      ⟨hz.1.le, hz.2⟩]
  rw [he]
  simpa only [sub_zero, integral_abs_kepStepSpatialFirst f' β ha] using
    abs_truncatedConvolution_second_le hw (continuous_kepStepSpatialFirst hf' β a)
      (continuous_kepStepSpatialSecond hf'' β a) (integrable_kepStepSpatialFirst hfi' ha β)
      hv' (hasDerivAt_kepStepSpatialFirst hdd β a)
      (hasDerivAt_kepFinalConvolution ν hf hf' hd hf0 hfD n x) hV hvV y

end

end PGM
