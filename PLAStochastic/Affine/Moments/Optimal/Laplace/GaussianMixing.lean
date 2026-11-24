import PLAStochastic.Affine.Moments.Optimal.Width.UnitWidthReal
import PLAStochastic.Affine.Moments.Optimal.Laplace.KernelIdentification
import PLAStochastic.ForMathlib.Probability.Gaussian.PositiveMixingTonelli
import PLAStochastic.Affine.Moments.Optimal.Integrals.RemainingClosedForms

noncomputable section
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

theorem measurable_optimalMomentTimeTransform (n : ℕ) :
    Measurable (fun p : ℝ×ℝ×ℝ => optimalMomentTimeTransform n p.1 p.2.1 p.2.2) := by
  have hm : Measurable (fun p : (ℝ×ℝ×ℝ)×ℝ =>
      p.2^n*Real.exp (-(p.1.2.2^2/2)*p.2)*optimalMomentConvolution p.1.1 p.1.2.1 p.2) :=
    (by fun_prop : Measurable (fun p : (ℝ×ℝ×ℝ)×ℝ => p.2^n*Real.exp (-(p.1.2.2^2/2)*p.2))).mul
      (measurable_optimalMomentConvolution.comp (f := fun p : (ℝ×ℝ×ℝ)×ℝ => (p.1.1,p.1.2.1,p.2)) (by fun_prop))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem lintegral_optimalMomentTimeTransform {a b k : ℝ}
    (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) (hk : 0<k) (n : ℕ) :
    (∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (T^n*Real.exp (-(k^2/2)*T))*
      ENNReal.ofReal (optimalMomentConvolution a b T))=
        ENNReal.ofReal (optimalMomentTimeTransform n a b k) := by
  symm
  unfold optimalMomentTimeTransform positiveLaplaceMoment
  rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_optimalMomentTimeTransform ha hb hk n)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
        exact mul_nonneg (mul_nonneg (pow_nonneg hT.le n) (Real.exp_nonneg _))
          (optimalMomentConvolution_nonneg ha hb T))]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro T hT
  exact ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hT.le n) (Real.exp_nonneg _))

def optimalMomentGaussianKernel (n : ℕ) (p : ℝ×ℝ×ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.cosh ((p.2.1-p.1)*p.2.2))*
    ENNReal.ofReal (optimalMomentTimeTransform n p.1 p.2.1 p.2.2)

theorem measurable_optimalMomentGaussianKernel (n : ℕ) :
    Measurable (optimalMomentGaussianKernel n) :=
  (by fun_prop : Measurable (fun p : ℝ×ℝ×ℝ => ENNReal.ofReal (Real.cosh ((p.2.1-p.1)*p.2.2)))).mul
    (measurable_optimalMomentTimeTransform n).ennreal_ofReal

theorem lintegral_optimalMomentUnitIntegrand_gaussian (n : ℕ) :
    (∫⁻ p, ENNReal.ofReal (optimalMomentUnitIntegrand ((n:ℝ)+1) p) ∂optimalMomentUnitMeasure)=
      ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ k : ℝ in Ioi 0, ∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
          optimalMomentGaussianKernel n (a,b,k) := by
  have hm := (measurable_optimalMomentUnitIntegrand ((n:ℝ)+1)).ennreal_ofReal
  have hG := measurable_optimalMomentGaussianKernel n
  have hpoint (a b : ℝ) (ha : a∈Ioo 0 1) (hb : b∈Ioo 0 1) :
      (∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (optimalMomentUnitIntegrand ((n:ℝ)+1) (a,b,T)))=
        ENNReal.ofReal (Real.sqrt (2/Real.pi))*∫⁻ k : ℝ in Ioi 0,
          optimalMomentGaussianKernel n (a,b,k) := by
    have he := gaussianLaplaceTonelli n (b-a)
      (measurable_optimalMomentConvolution.comp (f := fun T : ℝ => (a,b,T)) (by fun_prop)).ennreal_ofReal
    simp only [Function.comp_apply] at he
    calc
      _ = ∫⁻ T : ℝ in Ioi 0, ENNReal.ofReal (T^((n:ℝ)-1/2)*Real.exp ((b-a)^2/(2*T)))*
          ENNReal.ofReal (optimalMomentConvolution a b T) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro T hT
        dsimp only [optimalMomentUnitIntegrand]
        rw [show (n:ℝ)+1-3/2=(n:ℝ)-1/2 by ring,
          ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hT.le _) (Real.exp_nonneg _))]
      _ = _ := by
        rw [he]
        congr 1
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro k hk
        dsimp only [optimalMomentGaussianKernel]
        rw [lintegral_optimalMomentTimeTransform ha hb hk n]
  change (∫⁻ p, ENNReal.ofReal (optimalMomentUnitIntegrand ((n:ℝ)+1) p)
    ∂(volume.restrict (Ioo (0:ℝ) 1)).prod
      ((volume.restrict (Ioo (0:ℝ) 1)).prod (volume.restrict (Ioi (0:ℝ)))))=_
  rw [lintegral_prod _ hm.aemeasurable]
  calc
    _ = ∫⁻ a : ℝ in Ioo 0 1, ∫⁻ b : ℝ in Ioo 0 1,
        ENNReal.ofReal (Real.sqrt (2/Real.pi))*∫⁻ k : ℝ in Ioi 0,
          optimalMomentGaussianKernel n (a,b,k) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro a ha
      dsimp only
      have hma : Measurable (fun y : ℝ×ℝ => ENNReal.ofReal (optimalMomentUnitIntegrand ((n:ℝ)+1) (a,y))) :=
        hm.comp measurable_prodMk_left
      rw [lintegral_prod _ hma.aemeasurable]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro b hb
      exact hpoint a b ha hb
    _ = ENNReal.ofReal (Real.sqrt (2/Real.pi))*
        ∫⁻ a : ℝ in Ioo 0 1, ∫⁻ b : ℝ in Ioo 0 1, ∫⁻ k : ℝ in Ioi 0,
          optimalMomentGaussianKernel n (a,b,k) := by
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
      congr 1
      have hm₁ : Measurable (fun p : ℝ×ℝ => ∫⁻ k : ℝ in Ioi 0,
          optimalMomentGaussianKernel n (p.1,p.2,k)) :=
        (hG.comp (f := fun p : (ℝ×ℝ)×ℝ => (p.1.1,p.1.2,p.2)) (by fun_prop)).lintegral_prod_right'
      rw [lintegral_lintegral_swap hm₁.aemeasurable]
      have hm₂ : Measurable (fun p : ℝ×ℝ => ∫⁻ a : ℝ in Ioo 0 1,
          optimalMomentGaussianKernel n (a,p.1,p.2)) :=
        (hG.comp (f := fun p : (ℝ×ℝ)×ℝ => (p.2,p.1.1,p.1.2)) (by fun_prop)).lintegral_prod_right'
      have he : (∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1, ∫⁻ k : ℝ in Ioi 0,
          optimalMomentGaussianKernel n (a,b,k))=
          ∫⁻ b : ℝ in Ioo 0 1, ∫⁻ k : ℝ in Ioi 0, ∫⁻ a : ℝ in Ioo 0 1,
          optimalMomentGaussianKernel n (a,b,k) := by
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro b hb
        exact lintegral_lintegral_swap
          (hG.comp (f := fun p : ℝ×ℝ => (p.1,b,p.2)) (by fun_prop)).aemeasurable
      rw [he]
      exact lintegral_lintegral_swap hm₂.aemeasurable

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0→Ω→ℝ}

theorem optimalUnitLifetime_moment_gaussian_lintegral (hB : IsBrownianReal B μ) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (optimalUnitLifetime B ω^((n:ℝ)+1)) ∂μ)=
      ENNReal.ofReal ((2:ℝ)^(2*((n:ℝ)+1)-2)*((n:ℝ)+1)*Real.sqrt (2*Real.pi)*Real.sqrt (2/Real.pi))*
        ∫⁻ k : ℝ in Ioi 0, ∫⁻ b : ℝ in Ioo 0 1, ∫⁻ a : ℝ in Ioo 0 1,
          optimalMomentGaussianKernel n (a,b,k) := by
  rw [optimalUnitLifetime_moment_unitIntegralENN hB (by positivity),
    lintegral_optimalMomentUnitIntegrand_gaussian]
  rw [ENNReal.ofReal_mul (by positivity : 0≤(2:ℝ)^(2*((n:ℝ)+1)-2)*((n:ℝ)+1)*Real.sqrt (2*Real.pi))]
  simp only [mul_assoc]

end BrownianAffine
