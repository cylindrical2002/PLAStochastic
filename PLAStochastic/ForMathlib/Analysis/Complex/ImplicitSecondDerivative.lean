import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # A second derivative from a scalar holomorphic implicit equation -/

noncomputable section
open Set Filter Topology
namespace PGM

theorem hasDerivAt_deriv_of_implicit {B ψ : ℂ → ℂ} {U V : Set ℂ} {μ q : ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hB : DifferentiableOn ℂ B U)
    (hψ : DifferentiableOn ℂ ψ V) (hmap : MapsTo B U V) (hq : q ∈ U)
    (hroot : ∀ r ∈ U, ψ (B r) + μ * B r = r)
    (hp : deriv ψ (B q) + μ ≠ 0) :
    HasDerivAt (deriv B) (-deriv (deriv ψ) (B q) / (deriv ψ (B q) + μ) ^ 3) q := by
  let P := fun r => deriv ψ (B r) + μ
  have hfirst : ∀ r ∈ U, P r * deriv B r = 1 := by
    intro r hr
    have hBr := ((hB r hr).differentiableAt (hU.mem_nhds hr)).hasDerivAt
    have hψr := ((hψ (B r) (hmap hr)).differentiableAt (hV.mem_nhds (hmap hr))).hasDerivAt
    have hd := (hψr.comp r hBr).add (hBr.const_mul μ)
    have he : (fun r => ψ (B r) + μ * B r) =ᶠ[𝓝 r] id :=
      eventually_of_mem (hU.mem_nhds hr) fun s hs => hroot s hs
    have hh := (hd.congr_of_eventuallyEq he.symm).unique (hasDerivAt_id r)
    change (deriv ψ (B r) + μ) * deriv B r = 1
    linear_combination hh
  have hne : ∀ r ∈ U, P r ≠ 0 := by
    intro r hr hz
    have hh := hfirst r hr
    rw [hz, zero_mul] at hh
    exact zero_ne_one hh
  have hderiv : ∀ r ∈ U, deriv B r = (P r)⁻¹ := by
    intro r hr
    rw [← one_div]
    apply (eq_div_iff (hne r hr)).mpr
    simpa [mul_comm] using hfirst r hr
  have hBr := ((hB q hq).differentiableAt (hU.mem_nhds hq)).hasDerivAt
  have hψ' := (((hψ.deriv hV) (B q) (hmap hq)).differentiableAt
    (hV.mem_nhds (hmap hq))).hasDerivAt
  have hP := (hψ'.comp q hBr).add_const μ
  have hd := hP.inv hp
  have he : deriv B =ᶠ[𝓝 q] (fun r => (P r)⁻¹) :=
    eventually_of_mem (hU.mem_nhds hq) fun r hr => hderiv r hr
  refine (hd.congr_of_eventuallyEq he).congr_deriv ?_
  rw [hderiv q hq]
  dsimp [P]
  field_simp [hp]

end PGM
