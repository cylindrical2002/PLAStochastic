import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.L1
import PLAStochastic.ForMathlib.MeasureTheory.Integral.IntegrableRealSeries
import PLAStochastic.ForMathlib.MeasureTheory.Measure.SignedPositiveLaplaceUniqueness

/-! # The true image-series Laplace transform and its identification with Q -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem measurable_optimalQImageSeries_time (x y : ℝ) :
    Measurable (optimalQImageSeries x y) := by
  apply Measurable.tsum
  intro n
  exact (measurable_optimalQImageMode n).comp (f := fun T : ℝ => (x,y,T)) (by fun_prop)

theorem measurable_laplace_optimalQImageMode (n : ℕ) (x y k : ℝ) :
    Measurable (fun T => Real.exp (-(k^2/2)*T)*optimalQImageMode n x y T) :=
  (by fun_prop : Measurable (fun T : ℝ => Real.exp (-(k^2/2)*T))).mul
    ((measurable_optimalQImageMode n).comp (f := fun T : ℝ => (x,y,T)) (by fun_prop))

theorem integrableOn_laplace_optimalQImageSeries {x y k : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hk : 0 < k) :
    IntegrableOn (fun T => Real.exp (-(k^2/2)*T)*optimalQImageSeries x y T) (Ioi 0) := by
  have hi := integrable_real_tsum_of_summable_integral_norm
    (fun n => measurable_laplace_optimalQImageMode n x y k)
    (fun n => integrableOn_laplace_optimalQImageMode n hx hy hk)
    (summable_integral_norm_laplace_optimalQImageMode hx hy hk)
  simpa only [IntegrableOn,optimalQImageSeries,tsum_mul_left] using hi

theorem integral_laplace_optimalQImageSeries {x y k : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hk : 0 < k) :
    (∫ T in Ioi (0:ℝ),Real.exp (-(k^2/2)*T)*optimalQImageSeries x y T)=
      optimalMomentLaplaceKernel k (1-x) y := by
  have h := integral_tsum_of_summable_integral_norm
    (fun n => integrableOn_laplace_optimalQImageMode n hx hy hk)
    (summable_integral_norm_laplace_optimalQImageMode hx hy hk)
  simp only [integral_laplace_optimalQImageMode _ hx hy hk,tsum_mul_left] at h
  rw [(hasSum_optimalQImageTransformMode hk x y).tsum_eq] at h
  exact h.symm

/-- No image-law assumption: equality follows from the actual signed Laplace uniqueness theorem. -/
theorem optimalQImageSeries_eq_convolution_ae {x y : ℝ}
    (hx : x∈Ioo 0 1) (hy : y∈Ioo 0 1) :
    optimalQImageSeries x y =ᵐ[volume.restrict (Ioi (0:ℝ))] optimalMomentConvolution (1-x) y := by
  have hxabs : |x| ≤ 1 := by rw [abs_of_pos hx.1]; exact hx.2.le
  have hyabs : |y| ≤ 1 := by rw [abs_of_pos hy.1]; exact hy.2.le
  have ha : 1-x∈Ioo (0:ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  apply ae_eq_of_gaussian_laplace_eq_above
    (measurable_optimalQImageSeries_time x y)
    (measurable_optimalMomentConvolution.comp (f := fun T : ℝ => (1-x,y,T)) (by fun_prop))
    (by norm_num : 0 < (1:ℝ))
  · intro k hk
    exact integrableOn_laplace_optimalQImageSeries hxabs hyabs (by linarith)
  · intro k hk
    exact integrableOn_laplace_optimalMomentConvolution ha hy (by linarith)
  · intro k hk
    dsimp only [Function.comp_def]
    rw [integral_laplace_optimalQImageSeries hxabs hyabs (by linarith),
      integral_laplace_optimalMomentConvolution ha hy (by linarith)]

end BrownianAffine
