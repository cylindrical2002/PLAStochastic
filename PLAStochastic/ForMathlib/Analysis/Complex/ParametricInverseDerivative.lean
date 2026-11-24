import PLAStochastic.ForMathlib.Analysis.Complex.ParametricInverseGerm
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! # Actual derivatives of parametric inverses with scalar block derivative -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasFDerivAt_parametric_inverse_of_scalar_block
    {f r : E × ℂ → ℂ} {p₀ : E} {V : ℂ}
    (hf : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0))
    (hr : DifferentiableAt ℂ r (p₀, 0)) (hr₀ : r (p₀, 0) = 0) (hV : V ≠ 0)
    (he : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), f (u.1, r u) = u.2) :
    HasFDerivAt r (V⁻¹ • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0) := by
  have hf' : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (p₀, r (p₀, 0)) := by
    simpa only [hr₀] using hf
  have hJ := (hasFDerivAt_fst (𝕜 := ℂ) (p := (p₀, (0 : ℂ)))).prodMk hr.hasFDerivAt
  have hD := hf'.comp (p₀, (0 : ℂ)) hJ
  have hEq : (fun u : E × ℂ => u.2) =ᶠ[𝓝 (p₀, 0)] (fun u => f (u.1, r u)) := by
    filter_upwards [he] with u hu
    exact hu.symm
  have huniq := (hD.congr_of_eventuallyEq hEq).unique
    (hasFDerivAt_snd (𝕜 := ℂ) (p := (p₀, (0 : ℂ))))
  have hd : fderiv ℂ r (p₀, 0) = V⁻¹ • ContinuousLinearMap.snd ℂ E ℂ := by
    apply ContinuousLinearMap.ext
    intro u
    have hv := congrArg (fun T : E × ℂ →L[ℂ] ℂ => T u) huniq
    have hm : V * fderiv ℂ r (p₀, 0) u = u.2 := by
      simpa using hv
    change fderiv ℂ r (p₀, 0) u = V⁻¹ * u.2
    calc
      fderiv ℂ r (p₀, 0) u = V⁻¹ * (V * fderiv ℂ r (p₀, 0) u) := by
        rw [← mul_assoc, inv_mul_cancel₀ hV, one_mul]
      _ = V⁻¹ * u.2 := by rw [hm]
  rw [← hd]
  exact hr.hasFDerivAt

end PGM
