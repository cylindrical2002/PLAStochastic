import PLAStochastic.Index.KEP.ReferenceScale.KernelStep
import PLAStochastic.Index.GEP.Kernel.BV.Translation

/-!
# Two actual convolution steps on a BV representative

The whole-line variation includes jumps at both interval endpoints. One true
step gives a derivative bound from variation; the second true step keeps its
endpoint terms and pays the input first-derivative norm once.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory Set Filter Topology

theorem truncatedConvolution_eq_free {p v : ℝ → ℝ} {a b : ℝ}
    (hs : ∀ z, z ∉ Icc a b → v z = 0) (y : ℝ) :
    truncatedConvolution a b p v y = ∫ t, p t * v (y - t) := by
  change truncatedConvolution a b p v y =
    (convolution p v (ContinuousLinearMap.mul ℝ ℝ) volume) y
  rw [convolution_mul_swap]
  unfold truncatedConvolution
  rw [← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    by_cases ht : t ∈ Icc a b
    · rw [indicator_of_mem ht]
    · rw [indicator_of_notMem ht, hs t ht, mul_zero]

theorem truncatedConvolution_bv_lip {p v : ℝ → ℝ} {a b D : ℝ}
    (hp : Measurable p) (hp0 : ∀ t, 0 ≤ p t) (hpD : ∀ t, p t ≤ D)
    (hv : Integrable v volume) (hs : ∀ z, z ∉ Icc a b → v z = 0)
    (hBV : BoundedVariationOn (fun t => (v t : ℂ)) univ) (x y : ℝ) :
    |truncatedConvolution a b p v x - truncatedConvolution a b p v y| ≤
      D * (eVariationOn (fun t => (v t : ℂ)) univ).toReal * |x - y| := by
  have hD : 0 ≤ D := (hp0 0).trans (hpD 0)
  have hi (z : ℝ) : Integrable (fun t => p t * v (z - t)) volume :=
    (hv.comp_sub_left z).bdd_mul hp.aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hp0 t)]; exact hpD t)
  have hdiff : Integrable (fun t => |v (x - t) - v (y - t)|) volume :=
    ((hv.comp_sub_left x).sub (hv.comp_sub_left y)).abs
  have hc : (∫ t, |v (x - t) - v (y - t)|) =
      ∫ t, |v (t + (x - y)) - v t| := by
    rw [← integral_sub_left_eq_self (fun t => |v (t + (x - y)) - v t|) volume y]
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [show y - t + (x - y) = x - t by ring]
  have ht := kernelTranslation_le hBV hv.ofReal (x - y)
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at ht
  rw [truncatedConvolution_eq_free hs x, truncatedConvolution_eq_free hs y,
    ← integral_sub (hi x) (hi y)]
  calc
    |∫ t, p t * v (x - t) - p t * v (y - t)| ≤
        ∫ t, |p t * v (x - t) - p t * v (y - t)| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => p t * v (x - t) - p t * v (y - t))
    _ ≤ ∫ t, D * |v (x - t) - v (y - t)| := by
      apply integral_mono ((hi x).sub (hi y)).abs (hdiff.const_mul D)
      intro t
      change |p t * v (x - t) - p t * v (y - t)| ≤ D * |v (x - t) - v (y - t)|
      rw [← mul_sub, abs_mul, abs_of_nonneg (hp0 t)]
      exact mul_le_mul_of_nonneg_right (hpD t) (abs_nonneg _)
    _ = D * ∫ t, |v (t + (x - y)) - v t| := by rw [integral_const_mul, hc]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left ht hD
      nlinarith

/-- A bounded probability density is only differentiated to identify the
derivative. Its bound comes from the original BV input, including its jumps. -/
theorem truncatedConvolution_first_bv_bound {p p' v : ℝ → ℝ} {a b D : ℝ}
    (hp : Continuous p) (hp' : Continuous p') (hd : ∀ t, HasDerivAt p (p' t) t)
    (hp0 : ∀ t, 0 ≤ p t) (hpD : ∀ t, p t ≤ D)
    (hv : Integrable v volume) (hs : ∀ z, z ∉ Icc a b → v z = 0)
    (hBV : BoundedVariationOn (fun t => (v t : ℂ)) univ) (y : ℝ) :
    |truncatedConvolution a b p' v y| ≤
      D * (eVariationOn (fun t => (v t : ℂ)) univ).toReal := by
  have hD : 0 ≤ D := (hp0 0).trans (hpD 0)
  have hh := (hasDerivAt_truncatedConvolution hp hp' hd hv.integrableOn y).le_of_lip'
    (by positivity : 0 ≤ D * (eVariationOn (fun t => (v t : ℂ)) univ).toReal)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using truncatedConvolution_bv_lip hp.measurable hp0 hpD
        hv hs hBV x y)
  simpa only [Real.norm_eq_abs] using hh

theorem abs_truncatedConvolution_le_density_bound {p v : ℝ → ℝ} {a b D : ℝ}
    (hp : Measurable p) (hp0 : ∀ t, 0 ≤ p t) (hpD : ∀ t, p t ≤ D)
    (hv : Integrable v volume) (hs : ∀ z, z ∉ Icc a b → v z = 0) (y : ℝ) :
    |truncatedConvolution a b p v y| ≤ D * ∫ z, |v z| := by
  have hi : Integrable (fun t => p (y - t) * v t) volume :=
    hv.bdd_mul (hp.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (ae_of_all _ fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (hp0 _)]; exact hpD _)
  have he : truncatedConvolution a b p v y = ∫ t, p (y - t) * v t := by
    rw [truncatedConvolution_eq_free hs]
    change (convolution p v (ContinuousLinearMap.mul ℝ ℝ) volume) y = _
    exact convolution_mul_swap
  rw [he]
  calc
    |∫ t, p (y - t) * v t| ≤ ∫ t, |p (y - t) * v t| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => p (y - t) * v t)
    _ ≤ ∫ t, D * |v t| := by
      apply integral_mono hi.abs (hv.abs.const_mul D)
      intro t
      change |p (y - t) * v t| ≤ D * |v t|
      rw [abs_mul, abs_of_nonneg (hp0 _)]
      exact mul_le_mul_of_nonneg_right (hpD _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

/-- The two-step estimate on the actual regular component. Neither boundary
term is replaced by a supremum of the input density derivative. -/
theorem truncatedConvolution_second_bv_bound {p p' p'' v : ℝ → ℝ} {a b D : ℝ}
    (hab : a ≤ b) (hp : Continuous p) (hp' : Continuous p') (hp'' : Continuous p'')
    (hpi' : Integrable p' volume) (hd : ∀ t, HasDerivAt p (p' t) t)
    (hdd : ∀ t, HasDerivAt p' (p'' t) t)
    (hp0 : ∀ t, 0 ≤ p t) (hpD : ∀ t, p t ≤ D)
    (hv : Integrable v volume) (hs : ∀ z, z ∉ Icc a b → v z = 0)
    (hBV : BoundedVariationOn (fun t => (v t : ℂ)) univ) (y : ℝ) :
    |truncatedConvolution a b p'' (truncatedConvolution a b p v) y| ≤
      D * (eVariationOn (fun t => (v t : ℂ)) univ).toReal * (∫ t, |p' t|) +
        D * (∫ z, |v z|) * (|p' (y - a)| + |p' (y - b)|) := by
  have hD : 0 ≤ D := (hp0 0).trans (hpD 0)
  have hc' : Continuous (truncatedConvolution a b p' v) :=
    continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_truncatedConvolution hp' hp'' hdd hv.integrableOn t).continuousAt
  have hA := abs_truncatedConvolution_second_le hab hp' hp'' hpi' hc' hdd
    (hasDerivAt_truncatedConvolution hp hp' hd hv.integrableOn)
    (by positivity : 0 ≤ D * (eVariationOn (fun t => (v t : ℂ)) univ).toReal)
    (fun t _ => truncatedConvolution_first_bv_bound hp hp' hd hp0 hpD hv hs hBV t) y
  have ha := mul_le_mul_of_nonneg_left
    (abs_truncatedConvolution_le_density_bound hp.measurable hp0 hpD hv hs a)
    (abs_nonneg (p' (y - a)))
  have hb := mul_le_mul_of_nonneg_left
    (abs_truncatedConvolution_le_density_bound hp.measurable hp0 hpD hv hs b)
    (abs_nonneg (p' (y - b)))
  nlinarith

theorem integral_abs_bv_support_le {g : ℝ → ℝ} {a b B : ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B) (hg : Integrable g volume)
    (hs : ∀ z, z ∉ Icc a b → g z = 0)
    (hvar : eVariationOn (fun z => (g z : ℂ)) univ ≤ ENNReal.ofReal B) :
    (∫ z, |g z|) ≤ (b - a) * B := by
  have hbv : BoundedVariationOn (fun z => (g z : ℂ)) univ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvar
  have hv : (eVariationOn (fun z => (g z : ℂ)) univ).toReal ≤ B := by
    simpa only [ENNReal.toReal_ofReal hB] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hvar
  have hga : g (a - 1) = 0 := hs _ (by intro hx; linarith [hx.1])
  have hb (z : ℝ) : |g z| ≤ B := by
    have hd := hbv.dist_le (mem_univ z) (mem_univ (a - 1))
    have he : dist (g z : ℂ) (g (a - 1) : ℂ) = |g z| := by
      rw [hga, Complex.ofReal_zero, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
    rw [he] at hd
    exact hd.trans hv
  have he : (∫ z, |g z|) = ∫ z in Icc a b, |g z| := by
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      dsimp only
      by_cases hz : z ∈ Icc a b
      · rw [indicator_of_mem hz]
      · simp only [indicator_of_notMem hz, hs z hz, abs_zero]
  rw [he]
  calc
    (∫ z in Icc a b, |g z|) ≤ ∫ _z in Icc a b, B :=
      setIntegral_mono_on hg.abs.integrableOn
        (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
        measurableSet_Icc (fun z _ => hb z)
    _ = (b - a) * B := by
      rw [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab), smul_eq_mul]

end

end PGM
