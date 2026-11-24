import PLAStochastic.Affine.Moments.Optimal.Survival.QImage.Geometric

/-! # The signed image expansion of the actual optimal Q transform -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def optimalQImageTransformBase (n : ℕ) (x y k : ℝ) : ℝ :=
  (optimalQImageCoefficientC n-optimalQImageCoefficientB n/k)*
    Real.exp (-optimalQImageLength n x y*k)

def optimalQImageTransformMode (n : ℕ) (x y k : ℝ) : ℝ :=
  16*(optimalQImageTransformBase n x y k+optimalQImageTransformBase n (-x) (-y) k-
    optimalQImageTransformBase n x (-y) k-optimalQImageTransformBase n (-x) y k)

theorem optimalQImage_exp_shift (n : ℕ) (x y k : ℝ) :
    Real.exp (-optimalQImageLength n x y*k)=
      Real.exp (-(2*(n:ℝ)+3)*k)*Real.exp (k*x)*Real.exp (k*y) := by
  rw [←Real.exp_add,←Real.exp_add]
  congr 1
  unfold optimalQImageLength
  ring

theorem hasSum_optimalQImageTransformBase {k : ℝ} (hk : 0 < k) (x y : ℝ) :
    HasSum (fun n => optimalQImageTransformBase n x y k)
      (centeredCoth k/(8*Real.sinh k^3)*Real.exp (k*x)*Real.exp (k*y)) := by
  have hb := (hasSum_optimalQImageB_exp hk).div_const k
  have hc := hasSum_optimalQImageC_exp hk
  convert! ((hc.sub hb).mul_right (Real.exp (k*x))).mul_right (Real.exp (k*y)) using 1
  · funext n
    unfold optimalQImageTransformBase
    rw [optimalQImage_exp_shift]
    ring
  · unfold centeredCoth
    have hs : Real.sinh k ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hk)
    field_simp

/-- The manuscript's signed geometric expansion is a genuine convergent series. -/
theorem hasSum_optimalQImageTransformMode {k : ℝ} (hk : 0 < k) (x y : ℝ) :
    HasSum (fun n => optimalQImageTransformMode n x y k)
      (optimalMomentLaplaceKernel k (1-x) y) := by
  have h := (((hasSum_optimalQImageTransformBase hk x y).add
    (hasSum_optimalQImageTransformBase hk (-x) (-y))).sub
      (hasSum_optimalQImageTransformBase hk x (-y))).sub
        (hasSum_optimalQImageTransformBase hk (-x) y)
  convert! h.mul_left (16:ℝ) using 1
  · unfold optimalMomentLaplaceKernel
    rw [show 1-(1-x)=x by ring,Real.sinh_eq (k*x),Real.sinh_eq (k*y)]
    simp only [mul_neg]
    ring

end BrownianAffine
