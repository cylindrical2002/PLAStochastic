import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # A norm bound for the actual derivative of a three-factor product -/

noncomputable section
open Complex
namespace PGM

theorem norm_deriv_three_factor_le {f g h : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (hh : DifferentiableAt ℂ h z) :
    ‖deriv (fun u => f u * g u * h u) z‖ ≤
      ‖deriv f z‖ * ‖g z‖ * ‖h z‖ +
        ‖f z‖ * ‖deriv g z‖ * ‖h z‖ + ‖f z‖ * ‖g z‖ * ‖deriv h z‖ := by
  have hd : HasDerivAt (fun u => f u * g u * h u)
      ((deriv f z * g z + f z * deriv g z) * h z + f z * g z * deriv h z) z :=
    (hf.hasDerivAt.mul hg.hasDerivAt).mul hh.hasDerivAt
  rw [hd.deriv]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, norm_mul]
  have hx := mul_le_mul_of_nonneg_right
    ((norm_add_le (deriv f z * g z) (f z * deriv g z)).trans_eq
      (by rw [norm_mul, norm_mul])) (norm_nonneg (h z))
  calc _ ≤ (‖deriv f z‖ * ‖g z‖ + ‖f z‖ * ‖deriv g z‖) * ‖h z‖ +
        ‖f z‖ * ‖g z‖ * ‖deriv h z‖ := by linarith [hx]
    _ = _ := by ring

theorem norm_deriv_three_factor_weighted_le {f g h : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (hh : DifferentiableAt ℂ h z)
    {W V I J X P Q T : ℝ} (hX : 1 ≤ X) (hW : 0 ≤ W) (hV : 0 ≤ V)
    (hI : 0 ≤ I) (_hJ : 0 ≤ J) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hT : 0 ≤ T)
    (hfv : ‖f z‖ ≤ W * P) (hgv : ‖g z‖ ≤ W * Q) (hhv : ‖h z‖ ≤ I * X * T)
    (hfd : ‖deriv f z‖ ≤ V * P) (hgd : ‖deriv g z‖ ≤ V * Q)
    (hhd : ‖deriv h z‖ ≤ J * X ^ 2 * T) :
    ‖deriv (fun u => f u * g u * h u) z‖ ≤
      (2 * V * W * I + W ^ 2 * J) * X ^ 2 * P * Q * T := by
  have hX0 : 0 ≤ X := by linarith
  have hXX : X ≤ X ^ 2 := by nlinarith
  apply (norm_deriv_three_factor_le hf hg hh).trans
  calc
    _ ≤ (V * P) * (W * Q) * (I * X * T) +
        (W * P) * (V * Q) * (I * X * T) +
        (W * P) * (W * Q) * (J * X ^ 2 * T) := by gcongr
    _ = (2 * V * W * I * X + W ^ 2 * J * X ^ 2) * P * Q * T := by ring
    _ ≤ (2 * V * W * I * X ^ 2 + W ^ 2 * J * X ^ 2) * P * Q * T := by gcongr
    _ = _ := by ring

end PGM
