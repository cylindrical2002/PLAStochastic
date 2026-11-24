import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic

/-! # Divided differences under a nonzero complex scaling -/

noncomputable section
namespace PGM

theorem dslope_comp_const_mul {f : ℂ → ℂ} {b : ℂ} (hb : b ≠ 0) (a c : ℂ)
    (hf : DifferentiableAt ℂ f (b * a)) :
    dslope (fun ξ : ℂ => f (b * ξ)) a c = b * dslope f (b * a) (b * c) := by
  by_cases hca : c = a
  · subst c
    rw [dslope_same, dslope_same]
    have hd := hf.hasDerivAt.comp a ((hasDerivAt_id a).const_mul b)
    simpa only [Function.comp_def, mul_one, mul_comm] using! hd.deriv
  · have hbc : b * c ≠ b * a := fun he => hca (mul_left_cancel₀ hb he)
    rw [dslope_of_ne _ hca, dslope_of_ne _ hbc, slope_def_field, slope_def_field]
    field_simp

end PGM
