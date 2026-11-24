import PLAStochastic.ForMathlib.Analysis.Complex.EvenSqrt

/-! # Pointwise square-root descent away from zero -/

noncomputable section
open Complex Filter Topology
namespace PGM

theorem differentiableAt_comp_sqrt_of_even_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Ψ : ℂ → E} {w : ℂ} (hw : w ≠ 0)
    (hΨ : DifferentiableAt ℂ Ψ (Complex.sqrt w))
    (hΨ' : DifferentiableAt ℂ Ψ (I * Complex.sqrt (-w)))
    (heven : ∀ r, Ψ (-r) = Ψ r) :
    DifferentiableAt ℂ (fun z => Ψ (Complex.sqrt z)) w := by
  rcases mem_slitPlane_or_neg_mem hw with hs | hs
  · exact hΨ.comp w (differentiableAt_sqrt hs)
  · have hbranch : DifferentiableAt ℂ (fun z => I * Complex.sqrt (-z)) w :=
      ((differentiableAt_sqrt hs).comp w differentiableAt_id.neg).const_mul I
    have heq : (fun z => Ψ (I * Complex.sqrt (-z))) = fun z => Ψ (Complex.sqrt z) := by
      funext z
      exact even_comp_sqrt_eq heven z
    simpa only [Function.comp_def, heq] using hΨ'.comp w hbranch

end PGM
