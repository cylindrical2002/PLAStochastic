import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.Laplace

/-! # Absolute integrability of the image series in every positive Laplace weight -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalQImageLaplaceBound (n : ℕ) (x y k : ℝ) : ℝ :=
  (optimalQImageCoefficientC n+optimalQImageCoefficientB n/k)*
    Real.exp (-optimalQImageLength n x y*k)

theorem summable_optimalQImageLaplaceBound {k : ℝ} (hk : 0 < k) (x y : ℝ) :
    Summable (fun n => optimalQImageLaplaceBound n x y k) := by
  have h := (((hasSum_optimalQImageC_exp hk).add
    ((hasSum_optimalQImageB_exp hk).div_const k)).mul_right (Real.exp (k*x))).mul_right (Real.exp (k*y))
  apply h.summable.congr
  intro n
  unfold optimalQImageLaplaceBound
  rw [optimalQImage_exp_shift]
  ring

theorem integral_norm_laplace_optimalQImageBase_le (n : ℕ) {x y k : ℝ}
    (hx : x ≤ 1) (hy : y ≤ 1) (hk : 0 < k) :
    (∫ T in Ioi (0:ℝ),‖Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T‖) ≤
      optimalQImageLaplaceBound n x y k := by
  let L := optimalQImageLength n x y
  have hL : 0 < L := optimalQImageLength_pos n hx hy
  have hi₁ := (integrableOn_gaussianInverseLaplaceKernel_weight hk hL).const_mul
    (optimalQImageCoefficientC n)
  have hi₂ := (integrableOn_gaussianInverseLaplaceKernel hk hL).const_mul
    (optimalQImageCoefficientB n)
  have hbound : (∫ T in Ioi (0:ℝ),‖Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T‖) ≤
      ∫ T in Ioi (0:ℝ),optimalQImageCoefficientC n*((L/T)*gaussianInverseLaplaceKernel k L T)+
        optimalQImageCoefficientB n*gaussianInverseLaplaceKernel k L T := by
    apply integral_mono_ae (integrableOn_laplace_optimalQImageBase n hx hy hk).norm (hi₁.add hi₂)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    have hT' : 0 < T := hT
    have hK : 0 ≤ gaussianInverseLaplaceKernel k L T := by unfold gaussianInverseLaplaceKernel; positivity
    have hc := optimalQImageCoefficientC_nonneg n
    have hb := optimalQImageCoefficientB_nonneg n
    dsimp only [Pi.add_apply]
    rw [optimalQImage_laplace_split]
    have hn₁ : 0 ≤ optimalQImageCoefficientC n*((L/T)*gaussianInverseLaplaceKernel k L T) := by positivity
    have hn₂ : 0 ≤ optimalQImageCoefficientB n*gaussianInverseLaplaceKernel k L T := by positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn₁,abs_of_nonneg hn₂] using
      norm_sub_le (optimalQImageCoefficientC n*((L/T)*gaussianInverseLaplaceKernel k L T))
        (optimalQImageCoefficientB n*gaussianInverseLaplaceKernel k L T)
  have he := integral_add hi₁ hi₂
  rw [he,integral_const_mul,integral_const_mul,
    integral_gaussianInverseLaplaceKernel_weight hk hL,
    integral_gaussianInverseLaplaceKernel hk hL] at hbound
  convert! hbound using 1
  unfold optimalQImageLaplaceBound
  dsimp only [L]
  rw [show -k*optimalQImageLength n x y = -optimalQImageLength n x y*k by ring]
  ring

theorem summable_integral_norm_laplace_optimalQImageBase {x y k : ℝ}
    (hx : x ≤ 1) (hy : y ≤ 1) (hk : 0 < k) :
    Summable (fun n => ∫ T in Ioi (0:ℝ),‖Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T‖) :=
  (summable_optimalQImageLaplaceBound hk x y).of_nonneg_of_le
    (fun _n => integral_nonneg (fun _T => norm_nonneg _))
    (fun n => integral_norm_laplace_optimalQImageBase_le n hx hy hk)

private theorem norm_signed_four (a b c d : ℝ) :
    ‖a+b-c-d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
  have h₁ := norm_sub_le (a+b-c) d
  have h₂ := norm_sub_le (a+b) c
  have h₃ := norm_add_le a b
  linarith

theorem summable_integral_norm_laplace_optimalQImageMode {x y k : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hk : 0 < k) :
    Summable (fun n => ∫ T in Ioi (0:ℝ),‖Real.exp (-(k^2/2)*T)*optimalQImageMode n x y T‖) := by
  have hx₁ := (abs_le.mp hx).2
  have hx₂ : -x ≤ 1 := by linarith [(abs_le.mp hx).1]
  have hy₁ := (abs_le.mp hy).2
  have hy₂ : -y ≤ 1 := by linarith [(abs_le.mp hy).1]
  have hs := ((((summable_integral_norm_laplace_optimalQImageBase hx₁ hy₁ hk).add
    (summable_integral_norm_laplace_optimalQImageBase hx₂ hy₂ hk)).add
      (summable_integral_norm_laplace_optimalQImageBase hx₁ hy₂ hk)).add
        (summable_integral_norm_laplace_optimalQImageBase hx₂ hy₁ hk)).mul_left (16:ℝ)
  apply hs.of_nonneg_of_le (fun _n => integral_nonneg (fun _T => norm_nonneg _))
  intro n
  have hpp := (integrableOn_laplace_optimalQImageBase n hx₁ hy₁ hk).norm
  have hmm := (integrableOn_laplace_optimalQImageBase n hx₂ hy₂ hk).norm
  have hpm := (integrableOn_laplace_optimalQImageBase n hx₁ hy₂ hk).norm
  have hmp := (integrableOn_laplace_optimalQImageBase n hx₂ hy₁ hk).norm
  have h₁ := integral_add hpp hmm
  have h₂ := integral_add (hpp.add hmm) hpm
  have h₃ := integral_add ((hpp.add hmm).add hpm) hmp
  simp only [Pi.add_apply] at h₁ h₂ h₃
  rw [←h₁,←h₂,←h₃,←integral_const_mul]
  apply integral_mono_ae (integrableOn_laplace_optimalQImageMode n hx hy hk).norm
    ((((hpp.add hmm).add hpm).add hmp).const_mul 16)
  filter_upwards with T
  rw [optimalQImage_mode_laplace_split,norm_mul]
  norm_num only [Real.norm_eq_abs,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 16)]
  exact mul_le_mul_of_nonneg_left (norm_signed_four _ _ _ _) (by norm_num)

end BrownianAffine
