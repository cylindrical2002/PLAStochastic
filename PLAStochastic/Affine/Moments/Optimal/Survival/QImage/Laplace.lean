import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.Transform
import PLAStochastic.ForMathlib.Probability.Gaussian.InverseLaplace

/-! # The actual inverse Laplace integral of each signed Gaussian image -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalQImageGaussian (L T : ℝ) : ℝ :=
  Real.exp (-L^2/(2*T))/Real.sqrt (2*Real.pi*T)

def optimalQImageBase (n : ℕ) (x y T : ℝ) : ℝ :=
  (optimalQImageCoefficientC n*optimalQImageLength n x y/T-optimalQImageCoefficientB n)*
    optimalQImageGaussian (optimalQImageLength n x y) T

def optimalQImageMode (n : ℕ) (x y T : ℝ) : ℝ :=
  16*(optimalQImageBase n x y T+optimalQImageBase n (-x) (-y) T-
    optimalQImageBase n x (-y) T-optimalQImageBase n (-x) y T)

def optimalQImageSeries (x y T : ℝ) : ℝ := ∑' n,optimalQImageMode n x y T

theorem measurable_optimalQImageBase (n : ℕ) :
    Measurable (fun p : ℝ×ℝ×ℝ => optimalQImageBase n p.1 p.2.1 p.2.2) := by
  unfold optimalQImageBase optimalQImageGaussian optimalQImageLength
  fun_prop

theorem measurable_optimalQImageMode (n : ℕ) :
    Measurable (fun p : ℝ×ℝ×ℝ => optimalQImageMode n p.1 p.2.1 p.2.2) := by
  unfold optimalQImageMode optimalQImageBase optimalQImageGaussian optimalQImageLength
  fun_prop

theorem optimalQImage_laplace_split (n : ℕ) (x y k T : ℝ) :
    Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T=
      optimalQImageCoefficientC n*((optimalQImageLength n x y/T)*
        gaussianInverseLaplaceKernel k (optimalQImageLength n x y) T)-
      optimalQImageCoefficientB n*gaussianInverseLaplaceKernel k (optimalQImageLength n x y) T := by
  unfold optimalQImageBase optimalQImageGaussian gaussianInverseLaplaceKernel
  rw [show -(k^2/2)*T=-k^2*T/2 by ring]
  ring

theorem integrableOn_laplace_optimalQImageBase (n : ℕ) {x y k : ℝ}
    (hx : x ≤ 1) (hy : y ≤ 1) (hk : 0 < k) :
    IntegrableOn (fun T => Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T) (Ioi 0) := by
  have hL := optimalQImageLength_pos n hx hy
  have hi := ((integrableOn_gaussianInverseLaplaceKernel_weight hk hL).const_mul
    (optimalQImageCoefficientC n)).sub
      ((integrableOn_gaussianInverseLaplaceKernel hk hL).const_mul (optimalQImageCoefficientB n))
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro T hT
  exact (optimalQImage_laplace_split n x y k T).symm

theorem integral_laplace_optimalQImageBase (n : ℕ) {x y k : ℝ}
    (hx : x ≤ 1) (hy : y ≤ 1) (hk : 0 < k) :
    (∫ T in Ioi (0:ℝ),Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T)=
      optimalQImageTransformBase n x y k := by
  have hL := optimalQImageLength_pos n hx hy
  simp_rw [optimalQImage_laplace_split]
  rw [integral_sub ((integrableOn_gaussianInverseLaplaceKernel_weight hk hL).const_mul _)
    ((integrableOn_gaussianInverseLaplaceKernel hk hL).const_mul _),
    integral_const_mul,integral_const_mul,integral_gaussianInverseLaplaceKernel_weight hk hL,
    integral_gaussianInverseLaplaceKernel hk hL]
  unfold optimalQImageTransformBase
  rw [show -k*optimalQImageLength n x y = -optimalQImageLength n x y*k by ring]
  ring

theorem optimalQImage_mode_laplace_split (n : ℕ) (x y k T : ℝ) :
    Real.exp (-(k^2/2)*T)*optimalQImageMode n x y T=
      16*(Real.exp (-(k^2/2)*T)*optimalQImageBase n x y T+
        Real.exp (-(k^2/2)*T)*optimalQImageBase n (-x) (-y) T-
        Real.exp (-(k^2/2)*T)*optimalQImageBase n x (-y) T-
        Real.exp (-(k^2/2)*T)*optimalQImageBase n (-x) y T) := by
  unfold optimalQImageMode
  ring

theorem integrableOn_laplace_optimalQImageMode (n : ℕ) {x y k : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hk : 0 < k) :
    IntegrableOn (fun T => Real.exp (-(k^2/2)*T)*optimalQImageMode n x y T) (Ioi 0) := by
  have hx₁ := (abs_le.mp hx).2
  have hx₂ : -x ≤ 1 := by linarith [(abs_le.mp hx).1]
  have hy₁ := (abs_le.mp hy).2
  have hy₂ : -y ≤ 1 := by linarith [(abs_le.mp hy).1]
  have hi := ((((integrableOn_laplace_optimalQImageBase n hx₁ hy₁ hk).add
    (integrableOn_laplace_optimalQImageBase n hx₂ hy₂ hk)).sub
      (integrableOn_laplace_optimalQImageBase n hx₁ hy₂ hk)).sub
        (integrableOn_laplace_optimalQImageBase n hx₂ hy₁ hk)).const_mul (16:ℝ)
  apply IntegrableOn.congr_fun hi _ measurableSet_Ioi
  intro T hT
  exact (optimalQImage_mode_laplace_split n x y k T).symm

theorem integral_laplace_optimalQImageMode (n : ℕ) {x y k : ℝ}
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hk : 0 < k) :
    (∫ T in Ioi (0:ℝ),Real.exp (-(k^2/2)*T)*optimalQImageMode n x y T)=
      optimalQImageTransformMode n x y k := by
  have hx₁ := (abs_le.mp hx).2
  have hx₂ : -x ≤ 1 := by linarith [(abs_le.mp hx).1]
  have hy₁ := (abs_le.mp hy).2
  have hy₂ : -y ≤ 1 := by linarith [(abs_le.mp hy).1]
  have hpp := integrableOn_laplace_optimalQImageBase n hx₁ hy₁ hk
  have hmm := integrableOn_laplace_optimalQImageBase n hx₂ hy₂ hk
  have hpm := integrableOn_laplace_optimalQImageBase n hx₁ hy₂ hk
  have hmp := integrableOn_laplace_optimalQImageBase n hx₂ hy₁ hk
  have h₁ := integral_add hpp hmm
  have h₂ := integral_sub (hpp.add hmm) hpm
  have h₃ := integral_sub ((hpp.add hmm).sub hpm) hmp
  simp only [Pi.add_apply,Pi.sub_apply] at h₁ h₂ h₃
  simp_rw [optimalQImage_mode_laplace_split]
  rw [integral_const_mul,h₃,h₂,h₁,
    integral_laplace_optimalQImageBase n hx₁ hy₁ hk,
    integral_laplace_optimalQImageBase n hx₂ hy₂ hk,
    integral_laplace_optimalQImageBase n hx₁ hy₂ hk,
    integral_laplace_optimalQImageBase n hx₂ hy₁ hk]
  rfl

end BrownianAffine
