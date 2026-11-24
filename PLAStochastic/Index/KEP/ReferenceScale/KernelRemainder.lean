import PLAStochastic.Index.KEP.ReferenceScale.KernelBV
import PLAStochastic.ForMathlib.Probability.Hellinger.Observables

/-!
# The second actual convolution step on the L2 remainder

Both derivatives stay on the input density. The remainder itself is not
differentiated and need not have pointwise bounds before its first true step.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

theorem density_sq_integrable_of_bound
    (p : HellingerDensity (volume : Measure ℝ)) {D : ℝ} (hpD : ∀ x, p.density x ≤ D) :
    Integrable (fun x => p.density x ^ 2) volume := by
  apply (p.integrable.const_mul D).mono' (p.measurable.pow_const 2).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [p.nonneg x, hpD x]

theorem abs_truncatedConvolution_le_L2
    (p : HellingerDensity (volume : Measure ℝ)) {D a b : ℝ}
    (hpD : ∀ x, p.density x ≤ D) {v : ℝ → ℝ}
    (hv2 : MemLp v 2 volume) (hs : ∀ z, z ∉ Icc a b → v z = 0) (y : ℝ) :
    |truncatedConvolution a b p.density v y| ≤
      Real.sqrt D * Real.sqrt (∫ z, v z ^ 2) := by
  have hD : 0 ≤ D := (p.nonneg 0).trans (hpD 0)
  have hpi := density_sq_integrable_of_bound p hpD
  have hpy : MemLp (fun t => p.density (y - t)) 2 volume :=
    (memLp_two_iff_integrable_sq ((p.measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)).2 (hpi.comp_sub_left y)
  have he : truncatedConvolution a b p.density v y = ∫ t, p.density (y - t) * v t := by
    rw [truncatedConvolution_eq_free hs]
    change (convolution p.density v (ContinuousLinearMap.mul ℝ ℝ) volume) y = _
    exact convolution_mul_swap
  have hip : (∫ t, p.density (y - t) ^ 2) ≤ D := by
    rw [integral_sub_left_eq_self (fun t => p.density t ^ 2) volume y]
    calc
      (∫ t, p.density t ^ 2) ≤ ∫ t, D * p.density t := by
        apply integral_mono hpi (p.integrable.const_mul D)
        intro t
        change p.density t ^ 2 ≤ D * p.density t
        nlinarith [p.nonneg t, hpD t]
      _ = D := by rw [integral_const_mul, p.integral_eq_one, mul_one]
  have hn := HellingerDensity.norm_toLp_sq hpy
  have hvn := HellingerDensity.norm_toLp_sq hv2
  have hpn : ‖hpy.toLp _‖ ≤ Real.sqrt D := by
    nlinarith [norm_nonneg (hpy.toLp _), Real.sqrt_nonneg D, Real.sq_sqrt hD]
  have hvn' : ‖hv2.toLp _‖ = Real.sqrt (∫ t, v t ^ 2) := by
    rw [← hvn, Real.sqrt_sq (norm_nonneg _)]
  have hc := abs_real_inner_le_norm (hpy.toLp _) (hv2.toLp _)
  rw [HellingerDensity.inner_toLp_eq_integral_mul hpy hv2, hvn'] at hc
  rw [he]
  exact hc.trans (mul_le_mul_of_nonneg_right hpn (Real.sqrt_nonneg _))

theorem abs_truncatedConvolution_le_input_bound {p v : ℝ → ℝ} {a b M : ℝ}
    (hp : Integrable p volume) (hv : Measurable v) (hM : 0 ≤ M)
    (hvM : ∀ x ∈ Ioc a b, |v x| ≤ M) (y : ℝ) :
    |truncatedConvolution a b p v y| ≤ (∫ t, |p t|) * M := by
  have hpy := hp.comp_sub_left y
  have hi : IntegrableOn (fun t => p (y - t) * v t) (Ioc a b) :=
    hpy.integrableOn.mul_bdd hv.aestronglyMeasurable
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simpa only [Real.norm_eq_abs] using hvM t ht)
  calc
    |truncatedConvolution a b p v y| ≤ ∫ t in Ioc a b, |p (y - t) * v t| := by
      simpa only [truncatedConvolution, Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun t => p (y - t) * v t)
    _ ≤ ∫ t in Ioc a b, |p (y - t)| * M := by
      apply setIntegral_mono_on hi.abs (hpy.abs.mul_const M).integrableOn measurableSet_Ioc
      intro t ht
      change |p (y - t) * v t| ≤ |p (y - t)| * M
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hvM t ht) (abs_nonneg _)
    _ ≤ ∫ t, |p (y - t)| * M :=
      setIntegral_le_integral (hpy.abs.mul_const M) (ae_of_all _ fun _ => by positivity)
    _ = _ := by rw [integral_mul_const, integral_sub_left_eq_self (fun t => |p t|) volume y]

/-- The rough remainder pays the second derivative once, after its first
bounded-density convolution. No derivative or supremum of `v` is required. -/
theorem truncatedConvolution_second_remainder_bound
    (p : HellingerDensity (volume : Measure ℝ)) {p' p'' v : ℝ → ℝ} {a b D : ℝ}
    (hp : Continuous p.density) (hp' : Continuous p')
    (hd : ∀ t, HasDerivAt p.density (p' t) t)
    (hpi'' : Integrable p'' volume) (hpD : ∀ t, p.density t ≤ D)
    (hv : Integrable v volume) (hv2 : MemLp v 2 volume)
    (hs : ∀ z, z ∉ Icc a b → v z = 0) (y : ℝ) :
    |truncatedConvolution a b p'' (truncatedConvolution a b p.density v) y| ≤
      (∫ t, |p'' t|) * Real.sqrt D * Real.sqrt (∫ z, v z ^ 2) := by
  have hc : Continuous (truncatedConvolution a b p.density v) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp hp' hd hv.integrableOn t).continuousAt
  have h := abs_truncatedConvolution_le_input_bound (a := a) (b := b) hpi'' hc.measurable
    (by positivity : 0 ≤ Real.sqrt D * Real.sqrt (∫ z, v z ^ 2))
    (fun t _ => abs_truncatedConvolution_le_L2 p hpD hv2 hs t) y
  simpa only [mul_assoc] using h

end

end PGM
