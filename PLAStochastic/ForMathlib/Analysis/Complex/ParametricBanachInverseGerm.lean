import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! # Genuine Banach-valued analytic inverses with scalar block derivatives -/

noncomputable section
open Complex Filter Topology
namespace PGM

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- A Banach-valued family with a scalar block diagonal derivative has a genuine analytic inverse germ
in the full parameter product. Both inverse identities hold on actual neighborhoods. -/
theorem exists_analytic_parametric_banach_inverse_germ {f : E × F → F} {p₀ : E} {V : ℂ}
    (hf : AnalyticAt ℂ f (p₀, 0))
    (hdf : HasFDerivAt f (V • ContinuousLinearMap.snd ℂ E F) (p₀, 0))
    (hV : V ≠ 0) (hf₀ : f (p₀, 0) = 0) :
    ∃ g : E × F → F, AnalyticAt ℂ g (p₀, 0) ∧ g (p₀, 0) = 0 ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : F)), f (u.1, g u) = u.2) ∧
      (∀ᶠ u in 𝓝 (p₀, (0 : F)), g (u.1, f u) = u.2) := by
  let H : E × F → E × F := fun u => (u.1, f u)
  let L : F ≃L[ℂ] F :=
    { toFun := fun x => V • x
      invFun := fun x => V⁻¹ • x
      left_inv := by intro x; simp [smul_smul, hV]
      right_inv := by intro x; simp [smul_smul, hV]
      map_add' := smul_add V
      map_smul' := fun c x => smul_comm V c x
      continuous_toFun := continuous_const.smul continuous_id
      continuous_invFun := continuous_const.smul continuous_id }
  let D : (E × F) ≃L[ℂ] (E × F) := ContinuousLinearEquiv.prodCongr
    (ContinuousLinearEquiv.refl ℂ E) L
  have hH : AnalyticAt ℂ H (p₀, 0) := (show AnalyticAt ℂ (Prod.fst : E × F → E) (p₀, 0) from analyticAt_fst).prod hf
  have hHD : HasFDerivAt H D.toContinuousLinearMap (p₀, 0) := by
    have hd := (hasFDerivAt_fst (𝕜 := ℂ) (p := (p₀, (0 : F)))).prodMk hdf
    have he : (ContinuousLinearMap.fst ℂ E F).prod
        (V • ContinuousLinearMap.snd ℂ E F) = D.toContinuousLinearMap := by
      ext u <;> simp [D, L]
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
  · have hr : ∀ᶠ u in 𝓝 (p₀, (0 : F)), H (I u) = u := by
      simpa only [hH₀] using hS.eventually_right_inverse
    filter_upwards [hr] with u hu
    have hp := congrArg (fun v : E × F => v.1) hu
    change (I u).1 = u.1 at hp
    have he := congrArg Prod.snd hu
    change f ((I u).1, (I u).2) = u.2 at he
    rwa [hp] at he
  · filter_upwards [hS.eventually_left_inverse] with u hu
    exact congrArg Prod.snd hu

end PGM
