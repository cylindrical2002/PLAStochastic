import PLAStochastic.ForMathlib.Probability.Gaussian.HyperbolaIntegral
import PLAStochastic.ForMathlib.Probability.Gaussian.SquareSubstitution

/-! # Genuine inverse Gaussian Laplace pairs on positive time -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def gaussianInverseLaplaceKernel (k L T : ℝ) : ℝ :=
  Real.exp (-k^2*T/2)*Real.exp (-L^2/(2*T))/Real.sqrt (2*Real.pi*T)

theorem gaussianInverseLaplaceKernel_square {k L x : ℝ} (hx : 0 < x) :
    2*x*gaussianInverseLaplaceKernel k L (x^2)=
      (2*Real.exp (-k*L)/Real.sqrt (2*Real.pi))*gaussianHyperbolaKernel k L x := by
  have hs : Real.sqrt (2*Real.pi*x^2)=Real.sqrt (2*Real.pi)*x := by
    rw [Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi),Real.sqrt_sq hx.le]
  have he : Real.exp (-k^2*x^2/2)*Real.exp (-L^2/(2*x^2))=
      Real.exp (-k*L)*gaussianHyperbolaKernel k L x := by
    unfold gaussianHyperbolaKernel gaussianHyperbola
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    field_simp
    ring
  unfold gaussianInverseLaplaceKernel
  rw [hs,he]
  field_simp

theorem gaussianInverseLaplaceKernel_square_weight {k L x : ℝ} (hx : 0 < x) :
    2*x*((L/x^2)*gaussianInverseLaplaceKernel k L (x^2))=
      (2*Real.exp (-k*L)/Real.sqrt (2*Real.pi))*
        ((L/x^2)*gaussianHyperbolaKernel k L x) := by
  calc
    _ = (L/x^2)*(2*x*gaussianInverseLaplaceKernel k L (x^2)) := by ring
    _ = _ := by rw [gaussianInverseLaplaceKernel_square hx]; ring

theorem integrableOn_gaussianInverseLaplaceKernel {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    IntegrableOn (gaussianInverseLaplaceKernel k L) (Ioi 0) := by
  apply (integrableOn_Ioi_square_iff _).mpr
  apply IntegrableOn.congr_fun ((integrable_gaussianHyperbolaKernel hk hL).const_mul
    (2*Real.exp (-k*L)/Real.sqrt (2*Real.pi))) _ measurableSet_Ioi
  intro x hx
  exact (gaussianInverseLaplaceKernel_square hx).symm

theorem integrableOn_gaussianInverseLaplaceKernel_weight {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    IntegrableOn (fun T => (L/T)*gaussianInverseLaplaceKernel k L T) (Ioi 0) := by
  apply (integrableOn_Ioi_square_iff _).mpr
  apply IntegrableOn.congr_fun ((integrable_gaussianHyperbola_reciprocal_weight hk hL).const_mul
    (2*Real.exp (-k*L)/Real.sqrt (2*Real.pi))) _ measurableSet_Ioi
  intro x hx
  exact (gaussianInverseLaplaceKernel_square_weight hx).symm

theorem integral_gaussianInverseLaplaceKernel {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    (∫ T in Ioi (0:ℝ), gaussianInverseLaplaceKernel k L T)=Real.exp (-k*L)/k := by
  rw [integral_Ioi_eq_square]
  have he := setIntegral_congr_fun (μ:=volume) measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) => gaussianInverseLaplaceKernel_square (k:=k) (L:=L) hx)
  rw [he,integral_const_mul,integral_gaussianHyperbolaKernel hk hL]
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

theorem integral_gaussianInverseLaplaceKernel_weight {k L : ℝ} (hk : 0 < k) (hL : 0 < L) :
    (∫ T in Ioi (0:ℝ), (L/T)*gaussianInverseLaplaceKernel k L T)=Real.exp (-k*L) := by
  rw [integral_Ioi_eq_square]
  have he := setIntegral_congr_fun (μ:=volume) measurableSet_Ioi
    (fun x (hx : x ∈ Ioi (0:ℝ)) => gaussianInverseLaplaceKernel_square_weight (k:=k) (L:=L) hx)
  rw [he,integral_const_mul,integral_gaussianHyperbola_reciprocal hk hL,
    integral_gaussianHyperbolaKernel hk hL]
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

end BrownianAffine
