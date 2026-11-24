import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! # The divided slope of a reciprocal, including the diagonal -/

noncomputable section
open Complex

theorem dslope_inv_eq {f : ℂ → ℂ} {a b : ℂ}
    (hf : DifferentiableAt ℂ f a) (ha : f a ≠ 0) (hb : f b ≠ 0) :
    dslope (fun z => (f z)⁻¹) a b = -dslope f a b / (f a * f b) := by
  by_cases h : b = a
  · subst b
    rw [dslope_same, dslope_same]
    change deriv f⁻¹ a = _
    rw [(hf.hasDerivAt.inv ha).deriv]
    ring
  · rw [dslope_of_ne _ h, dslope_of_ne _ h]
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    field_simp
    ring
