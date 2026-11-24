import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Genuine jointly analytic scalar inverses with arbitrary Banach parameters -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- A scalar family with a block diagonal derivative has a genuine analytic inverse germ
in the full parameter product. Both inverse identities hold on actual neighborhoods. -/
theorem exists_analytic_parametric_inverse_germ {f : E × ℂ → ℂ} {p₀ : E} {V : ℂ}
    (hf : AnalyticAt ℂ f (p₀, 0))
    (hdf : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E ℂ) (p₀, 0))
    (hV : V ≠ 0) (hf₀ : f (p₀, 0) = 0) :
    ∃ g : E × ℂ → ℂ, AnalyticAt ℂ g (p₀, 0) ∧ g (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), f (u.1, g u) = u.2) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), g (u.1, f u) = u.2) := by
  let H : E × ℂ → E × ℂ := fun u => (u.1, f u)
  let D : (E × ℂ) ≃L[ℂ] (E × ℂ) := ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℂ E) (ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 V hV))
  have hH : AnalyticAt ℂ H (p₀, 0) := (show AnalyticAt ℂ (Prod.fst : E × ℂ → E) (p₀, 0) from analyticAt_fst).prod hf
  have hHD : HasFDerivAt H D.toContinuousLinearMap (p₀, 0) := by
    have hd := (hasFDerivAt_fst (𝕜 := ℂ) (p := (p₀, (0 : ℂ)))).prodMk hdf
    have he : (ContinuousLinearMap.fst ℂ E ℂ).prod
        (V • ContinuousLinearMap.snd ℂ E ℂ) = D.toContinuousLinearMap := by
      ext u <;> simp [D, ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]
    rw [he] at hd
    exact hd
  have hS : HasStrictFDerivAt H D.toContinuousLinearMap (p₀, 0) := by
    rw [← hHD.fderiv]
    exact hH.hasStrictFDerivAt
  let R := hS.toOpenPartialHomeomorph H
  let I := hS.localInverse H D (p₀, 0)
  have hH₀ : H (p₀, 0) = (p₀, 0) := by simp [H, hf₀]
  have hI : AnalyticAt ℂ I (p₀, 0) := by
    have ha := R.analyticAt_symm' hS.mem_toOpenPartialHomeomorph_source hH hHD.fderiv
    change AnalyticAt ℂ R.symm (H (p₀, 0)) at ha
    rw [hH₀] at ha
    exact ha
  have hi₀ : I (p₀, 0) = (p₀, 0) := by
    simpa only [hH₀] using hS.localInverse_apply_image
  refine ⟨fun u => (I u).2, analyticAt_snd.comp hI, by simp [hi₀], ?_, ?_⟩
  · have hr : ∀ᶠ u in 𝓝 (p₀, (0 : ℂ)), H (I u) = u := by
      simpa only [hH₀] using hS.eventually_right_inverse
    filter_upwards [hr] with u hu
    have hp := congrArg (fun v : E × ℂ => v.1) hu
    change (I u).1 = u.1 at hp
    have he := congrArg Prod.snd hu
    change f ((I u).1, (I u).2) = u.2 at he
    rwa [hp] at he
  · filter_upwards [hS.eventually_left_inverse] with u hu
    exact congrArg Prod.snd hu

end PGM
