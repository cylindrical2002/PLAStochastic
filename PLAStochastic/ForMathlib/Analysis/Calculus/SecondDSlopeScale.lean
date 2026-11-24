import PLAStochastic.ForMathlib.Analysis.Calculus.DSlopeScale

/-! # Second divided differences under nonzero complex scaling -/

noncomputable section
namespace PGM

theorem dslope_const_mul_of_differentiable {f : ℂ → ℂ} (b a c : ℂ)
    (hf : DifferentiableAt ℂ f a) :
    dslope (fun ξ : ℂ => b * f ξ) a c = b * dslope f a c := by
  by_cases hca : c = a
  · subst c
    rw [dslope_same, dslope_same]
    exact (hf.hasDerivAt.const_mul b).deriv
  · rw [dslope_of_ne _ hca, dslope_of_ne _ hca, slope_def_field, slope_def_field]
    ring

theorem second_dslope_comp_const_mul {f : ℂ → ℂ} {b : ℂ} (hb : b ≠ 0) (a c t : ℂ)
    (hf : DifferentiableAt ℂ f (b * a))
    (hS : DifferentiableAt ℂ (dslope f (b * a)) (b * c)) :
    dslope (dslope (fun ξ : ℂ => f (b * ξ)) a) c t =
      b ^ 2 * dslope (dslope f (b * a)) (b * c) (b * t) := by
  have he : dslope (fun ξ : ℂ => f (b * ξ)) a =
      fun ξ : ℂ => b * dslope f (b * a) (b * ξ) := by
    funext ξ
    exact dslope_comp_const_mul hb a ξ hf
  have hcomp : DifferentiableAt ℂ (fun ξ : ℂ => dslope f (b * a) (b * ξ)) c :=
    hS.comp c (differentiableAt_id.const_mul b)
  rw [he, dslope_const_mul_of_differentiable b c t hcomp,
    dslope_comp_const_mul hb c t hS]
  ring

end PGM
