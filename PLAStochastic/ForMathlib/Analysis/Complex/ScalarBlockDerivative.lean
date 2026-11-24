import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Actual zero sections and scalar derivatives determine the full parameter derivative -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasFDerivAt_scalar_block_of_zero_section {f : E × ℂ → ℂ} {p₀ : E} {V : ℂ}
    (hf : DifferentiableAt ℂ f (p₀, 0))
    (hzero : ∀ᶠ p in 𝓝 p₀, f (p, 0) = 0)
    (hs : HasDerivAt (fun s : ℂ => f (p₀, s)) V 0) :
    HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0) := by
  let D := fderiv ℂ f (p₀, 0)
  have hd : HasFDerivAt f D (p₀, 0) := hf.hasFDerivAt
  have hL : D.comp (ContinuousLinearMap.inl ℂ E ℂ) = 0 := by
    have hcomp := hd.comp p₀ (ContinuousLinearMap.inl ℂ E ℂ).hasFDerivAt
    have hconst : HasFDerivAt (fun p : E => f (p, 0)) 0 p₀ :=
      (hasFDerivAt_const (𝕜 := ℂ) (0 : ℂ) p₀).congr_of_eventuallyEq hzero
    exact hcomp.unique hconst
  have hR : D (0, 1) = V := by
    have hc : HasDerivAt (fun s : ℂ => (p₀, s)) (0, 1) 0 :=
      (hasDerivAt_const (0 : ℂ) p₀).prodMk (hasDerivAt_id 0)
    exact (hd.comp_hasDerivAt 0 hc).unique hs
  have he : D = V • ContinuousLinearMap.snd ℂ E ℂ := by
    apply ContinuousLinearMap.ext
    intro u
    have hLu : D (u.1, 0) = 0 := by
      have h := congrArg (fun T : E →L[ℂ] ℂ => T u.1) hL
      simpa using h
    have hu : u = (u.1, 0) + u.2 • ((0 : E), (1 : ℂ)) := by
      ext <;> simp [smul_eq_mul]
    change D u = V * u.2
    calc
      D u = D ((u.1, 0) + u.2 • ((0 : E), (1 : ℂ))) := congrArg D hu
      _ = D (u.1, 0) + u.2 • D (0, 1) := by rw [map_add, map_smul]
      _ = _ := by rw [hLu, hR, zero_add]; simp [smul_eq_mul, mul_comm]
  rwa [he] at hd

end PGM
