import PLAStochastic.ForMathlib.Analysis.Calculus.SecondDSlopeScale
import Mathlib.Analysis.Complex.RemovableSingularity

/-! # Local equality and subtraction for removable divided differences -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

theorem cepsNormal_dslope_eq_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (he : EqOn f g U) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    dslope f a b = dslope g a b := by
  by_cases hba : b = a
  · subst b
    rw [dslope_same, dslope_same]
    exact Filter.EventuallyEq.deriv_eq (he.eventuallyEq_of_mem (hU.mem_nhds ha))
  · rw [dslope_of_ne _ hba, dslope_of_ne _ hba, slope_def_field, slope_def_field,
      he hb, he ha]

theorem cepsNormal_second_dslope_eq_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (he : EqOn f g U) {a b t : ℂ}
    (ha : a ∈ U) (hb : b ∈ U) (ht : t ∈ U) :
    dslope (dslope f a) b t = dslope (dslope g a) b t :=
  cepsNormal_dslope_eq_of_eqOn hU
    (fun _ hx => cepsNormal_dslope_eq_of_eqOn hU he ha hx) hb ht

theorem cepsNormal_dslope_sub_of_differentiableAt {f g : ℂ → ℂ} {a b : ℂ}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a) :
    dslope (fun x => f x - g x) a b = dslope f a b - dslope g a b := by
  by_cases hba : b = a
  · subst b
    rw [dslope_same, dslope_same, dslope_same]
    exact deriv_sub hf hg
  · rw [dslope_of_ne _ hba, dslope_of_ne _ hba, dslope_of_ne _ hba,
      slope_def_field, slope_def_field, slope_def_field]
    ring

theorem cepsNormal_second_dslope_sub_of_differentiableAt {f g : ℂ → ℂ} {a b t : ℂ}
    (hf : DifferentiableAt ℂ f a) (hg : DifferentiableAt ℂ g a)
    (hfS : DifferentiableAt ℂ (dslope f a) b)
    (hgS : DifferentiableAt ℂ (dslope g a) b) :
    dslope (dslope (fun x => f x - g x) a) b t =
      dslope (dslope f a) b t - dslope (dslope g a) b t := by
  have he : dslope (fun x => f x - g x) a = fun x => dslope f a x - dslope g a x :=
    funext fun _ => cepsNormal_dslope_sub_of_differentiableAt hf hg
  rw [he, cepsNormal_dslope_sub_of_differentiableAt hfS hgS]

theorem cepsNormal_second_dslope_const_mul {f : ℂ → ℂ} (c : ℂ) {a b t : ℂ}
    (hf : DifferentiableAt ℂ f a) (hfS : DifferentiableAt ℂ (dslope f a) b) :
    dslope (dslope (fun x => c * f x) a) b t = c * dslope (dslope f a) b t := by
  have he : dslope (fun x => c * f x) a = fun x => c * dslope f a x :=
    funext fun x => dslope_const_mul_of_differentiable c a x hf
  rw [he, dslope_const_mul_of_differentiable c b t hfS]

end PGM
