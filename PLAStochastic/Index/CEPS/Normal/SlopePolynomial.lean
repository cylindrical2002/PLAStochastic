import PLAStochastic.Index.CEPS.Normal.SlopeCongr
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Exact removable slopes of quadratic polynomials -/

noncomputable section
open Complex
namespace PGM

theorem cepsNormal_dslope_quadratic (A B C a t : ℂ) :
    dslope (fun ξ : ℂ => A * ξ ^ 2 + B * ξ + C) a t = A * (a + t) + B := by
  by_cases hta : t = a
  · subst t
    rw [dslope_same]
    have hd := (((hasDerivAt_id a).pow 2).const_mul A).add
      ((hasDerivAt_id a).const_mul B) |>.add_const C
    have he : deriv (fun ξ : ℂ => A * ξ ^ 2 + B * ξ + C) a = A * (2 * a) + B := by
      simpa only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one] using! hd.deriv
    rw [he]
    ring
  · rw [dslope_of_ne _ hta, slope_def_field]
    field_simp
    ring

theorem cepsNormal_second_dslope_quadratic (A B C a b t : ℂ) :
    dslope (dslope (fun ξ : ℂ => A * ξ ^ 2 + B * ξ + C) a) b t = A := by
  have he : dslope (fun ξ : ℂ => A * ξ ^ 2 + B * ξ + C) a = fun ξ => A * (a + ξ) + B :=
    funext (cepsNormal_dslope_quadratic A B C a)
  rw [he]
  by_cases htb : t = b
  · subst t
    rw [dslope_same]
    have hd := (((hasDerivAt_id b).const_add a).const_mul A).add_const B
    simpa only [mul_one] using! hd.deriv
  · rw [dslope_of_ne _ htb, slope_def_field]
    field_simp
    ring

end PGM
