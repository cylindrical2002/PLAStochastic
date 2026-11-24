import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Differentiating a convolution truncated to a fixed interval

The second derivative keeps both endpoint terms. The interval projection is
not differentiated as if it were constant on the entire real line.
-/

set_option autoImplicit false

namespace MeasureTheory

noncomputable section

open Set Filter

def truncatedConvolution (a b : ℝ) (p v : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ z in Ioc a b, p (y - z) * v z

theorem integrableOn_truncatedConvolution_integrand {a b : ℝ} {p v : ℝ → ℝ}
    (hp : Continuous p) (hv : IntegrableOn v (Ioc a b)) (y : ℝ) :
    IntegrableOn (fun z => p (y - z) * v z) (Ioc a b) :=
  (((integrableOn_Icc_iff_integrableOn_Ioc).2 hv).continuousOn_mul
    ((hp.comp (continuous_const.sub continuous_id)).continuousOn) isCompact_Icc).mono_set
    Ioc_subset_Icc_self

theorem truncatedConvolution_add {a b : ℝ} {p v r : ℝ → ℝ}
    (hp : Continuous p) (hv : IntegrableOn v (Ioc a b)) (hr : IntegrableOn r (Ioc a b))
    (y : ℝ) : truncatedConvolution a b p (v + r) y =
      truncatedConvolution a b p v y + truncatedConvolution a b p r y := by
  unfold truncatedConvolution
  simp only [Pi.add_apply, mul_add]
  exact integral_add (integrableOn_truncatedConvolution_integrand hp hv y)
    (integrableOn_truncatedConvolution_integrand hp hr y)

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_truncatedConvolution {a b : ℝ} {p p' v : ℝ → ℝ}
    (hp : Continuous p) (hp' : Continuous p')
    (hd : ∀ x, HasDerivAt p (p' x) x) (hv : IntegrableOn v (Ioc a b))
    (y : ℝ) :
    HasDerivAt (truncatedConvolution a b p v)
      (truncatedConvolution a b p' v y) y := by
  have hF : IntegrableOn (fun z => p (y - z) * v z) (Ioc a b) :=
    integrableOn_truncatedConvolution_integrand hp hv y
  have hd' : ∀ z x : ℝ, HasDerivAt (fun x => p (x - z) * v z)
      (p' (x - z) * v z) x := fun z x => by
    simpa only [sub_zero, mul_one, Function.comp_apply, id_eq] using
      ((hd (x - z)).comp x ((hasDerivAt_id x).sub_const z)).mul_const (v z)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hp'.continuousOn : ContinuousOn p' (Icc (y - 1 - b) (y + 1 - a)))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioc a b)) (s := Ioo (y - 1) (y + 1))
    (bound := fun z => M * |v z|)
    (F := fun x z : ℝ => p (x - z) * v z)
    (F' := fun x z : ℝ => p' (x - z) * v z)
    (Ioo_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun x =>
      ((hp.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
        hv.aestronglyMeasurable))
    hF
    ((hp'.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hv.aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
      intro x hx
      rw [Real.norm_eq_abs, abs_mul]
      have hbnd := hM (x - z) (show x - z ∈ Icc (y - 1 - b) (y + 1 - a) from
        ⟨by linarith [hz.2, hx.1], by linarith [hz.1, hx.2]⟩)
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hbnd)
        (abs_nonneg _))
    (hv.abs.const_mul M)
    (ae_of_all _ fun z x _ => hd' z x)).2

set_option backward.isDefEq.respectTransparency.types false in
/-- Integration by parts for the last real convolution step. -/
theorem truncatedConvolution_second_eq {a b : ℝ} (hab : a ≤ b)
    {p' p'' v v' : ℝ → ℝ} (hp'' : Continuous p'') (hv' : Continuous v')
    (hdp : ∀ x, HasDerivAt p' (p'' x) x)
    (hdv : ∀ x, HasDerivAt v (v' x) x) (y : ℝ) :
    truncatedConvolution a b p'' v y = truncatedConvolution a b p' v' y +
      p' (y - a) * v a - p' (y - b) * v b := by
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b)
    (u := fun z => p' (y - z)) (u' := fun z => -p'' (y - z))
    (v := v) (v' := v')
    (fun z _ => by
      convert (hdp (y - z)).comp z
        ((hasDerivAt_const z y).sub (hasDerivAt_id z)) using 1 <;> first | rfl | ring)
    (fun z _ => hdv z)
    ((hp''.comp (continuous_const.sub continuous_id)).neg.intervalIntegrable a b)
    (hv'.intervalIntegrable a b)
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab] at hi
  simp only [neg_mul, integral_neg] at hi
  unfold truncatedConvolution
  linarith

/-- An endpoint-aware pointwise estimate. The derivative norm is paid once. -/
theorem abs_truncatedConvolution_second_le {a b : ℝ} (hab : a ≤ b)
    {p' p'' v v' : ℝ → ℝ} (hp' : Continuous p') (hp'' : Continuous p'')
    (hp'i : Integrable p' volume) (hv' : Continuous v')
    (hdp : ∀ x, HasDerivAt p' (p'' x) x)
    (hdv : ∀ x, HasDerivAt v (v' x) x)
    {V : ℝ} (hV : 0 ≤ V) (hvV : ∀ x ∈ Ioc a b, |v' x| ≤ V) (y : ℝ) :
    |truncatedConvolution a b p'' v y| ≤
      V * (∫ x, |p' x|) + |p' (y - a)| * |v a| + |p' (y - b)| * |v b| := by
  have hpi : Integrable (fun z => |p' (y - z)|) volume :=
    ((hp'i.comp_sub_left y).abs)
  have hi : |truncatedConvolution a b p' v' y| ≤ V * (∫ x, |p' x|) := by
    calc
      |truncatedConvolution a b p' v' y| ≤
          ∫ z in Ioc a b, |p' (y - z) * v' z| := by
        simpa only [truncatedConvolution, Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun z => p' (y - z) * v' z)
      _ ≤ ∫ z in Ioc a b, V * |p' (y - z)| := by
        apply setIntegral_mono_on
          (((hp'.comp (continuous_const.sub continuous_id)).mul hv').abs.integrableOn_Icc
            |>.mono_set Ioc_subset_Icc_self)
          (hpi.const_mul V).integrableOn measurableSet_Ioc
        intro z hz
        change |p' (y - z) * v' z| ≤ V * |p' (y - z)|
        rw [abs_mul, mul_comm V]
        exact mul_le_mul_of_nonneg_left (hvV z hz) (abs_nonneg _)
      _ ≤ ∫ z, V * |p' (y - z)| :=
        setIntegral_le_integral (hpi.const_mul V) (ae_of_all _ fun _ => by positivity)
      _ = V * (∫ x, |p' x|) := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun x => |p' x|) volume y]
  rw [truncatedConvolution_second_eq hab hp'' hv' hdp hdv]
  calc
    |truncatedConvolution a b p' v' y + p' (y - a) * v a - p' (y - b) * v b| ≤
        |truncatedConvolution a b p' v' y + p' (y - a) * v a| +
          |p' (y - b) * v b| := abs_sub _ _
    _ ≤ |truncatedConvolution a b p' v' y| + |p' (y - a) * v a| +
        |p' (y - b) * v b| := by
      linarith [abs_add_le (truncatedConvolution a b p' v' y) (p' (y - a) * v a)]
    _ ≤ _ := by rw [abs_mul, abs_mul]; linarith

end

end MeasureTheory
