import PLAStochastic.Index.CEPS.Scaled.WeightedProductError

/-! # Actual derivative errors of three-factor products -/

noncomputable section
open Complex
namespace PGM

theorem cepsNorm_deriv_three_factor_error_le {A B I a b i : ℂ → ℂ} {z : ℂ}
    (hA : DifferentiableAt ℂ A z) (hB : DifferentiableAt ℂ B z)
    (hI : DifferentiableAt ℂ I z) (ha : DifferentiableAt ℂ a z)
    (hb : DifferentiableAt ℂ b z) (hi : DifferentiableAt ℂ i z) :
    ‖deriv (fun u => A u * B u * I u - a u * b u * i u) z‖ ≤
      (‖(deriv A z - deriv a z) * B z * I z‖ +
        ‖deriv a z * (B z - b z) * I z‖ + ‖deriv a z * b z * (I z - i z)‖) +
      (‖(A z - a z) * deriv B z * I z‖ +
        ‖a z * (deriv B z - deriv b z) * I z‖ + ‖a z * deriv b z * (I z - i z)‖) +
      (‖(A z - a z) * B z * deriv I z‖ +
        ‖a z * (B z - b z) * deriv I z‖ + ‖a z * b z * (deriv I z - deriv i z)‖) := by
  have hABI : HasDerivAt (fun u => A u * B u * I u)
      ((deriv A z * B z + A z * deriv B z) * I z + A z * B z * deriv I z) z := by
    simpa only [Pi.mul_def] using (hA.hasDerivAt.mul hB.hasDerivAt).mul hI.hasDerivAt
  have habi : HasDerivAt (fun u => a u * b u * i u)
      ((deriv a z * b z + a z * deriv b z) * i z + a z * b z * deriv i z) z := by
    simpa only [Pi.mul_def] using (ha.hasDerivAt.mul hb.hasDerivAt).mul hi.hasDerivAt
  have hd := hABI.sub habi
  simp only [Pi.sub_def] at hd
  rw [hd.deriv]
  have he : (deriv A z * B z + A z * deriv B z) * I z + A z * B z * deriv I z -
      ((deriv a z * b z + a z * deriv b z) * i z + a z * b z * deriv i z) =
        (deriv A z * B z * I z - deriv a z * b z * i z) +
          (A z * deriv B z * I z - a z * deriv b z * i z) +
            (A z * B z * deriv I z - a z * b z * deriv i z) := by ring
  rw [he]
  apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
  exact add_le_add
    (add_le_add (cepsNorm_three_factor_error_le (deriv A z) (B z) (I z) (deriv a z) (b z) (i z))
      (cepsNorm_three_factor_error_le (A z) (deriv B z) (I z) (a z) (deriv b z) (i z)))
    (cepsNorm_three_factor_error_le (A z) (B z) (deriv I z) (a z) (b z) (deriv i z))

end PGM
