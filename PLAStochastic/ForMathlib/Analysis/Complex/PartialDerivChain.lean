import PLAStochastic.ForMathlib.Analysis.Complex.ContinuousFDerivTwo

/-! # A two-variable holomorphic chain rule using actual partial derivatives -/

noncomputable section
open Complex
namespace PGM

theorem hasDerivAt_comp_complex_partials {F : ℂ × ℂ → ℂ} {q ξ : ℂ → ℂ}
    {z α β : ℂ} (hF : DifferentiableAt ℂ F (q z, ξ z))
    (hq : HasDerivAt q α z) (hξ : HasDerivAt ξ β z) :
    HasDerivAt (fun u => F (q u, ξ u))
      (deriv (fun u => F (u, ξ z)) (q z) * α +
        deriv (fun u => F (q z, u)) (ξ z) * β) z := by
  have hcurve : HasDerivAt (fun u => (q u, ξ u)) (α, β) z := hq.prodMk hξ
  have h : HasDerivAt (fun u => F (q u, ξ u))
      (fderiv ℂ F (q z, ξ z) (α, β)) z := by
    simpa only [Function.comp_def] using hF.hasFDerivAt.comp_hasDerivAt z hcurve
  rw [fderiv_eq_complex_partials hF] at h
  change HasDerivAt (fun u => F (q u, ξ u))
    (deriv (fun u => F (u, ξ z)) (q z) * α + deriv (fun u => F (q z, u)) (ξ z) * β) z at h
  exact h

end PGM
