import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.Basic

/-! # Divided differences depend only on values and germs on an open set -/

noncomputable section
open Complex Set Filter Topology
namespace PGM

theorem dslope_eq_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (he : EqOn f g U) {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) :
    dslope f a b = dslope g a b := by
  by_cases hab : b = a
  · subst b
    rw [dslope_same, dslope_same]
    exact (he.eventuallyEq_of_mem (hU.mem_nhds ha)).deriv_eq
  · rw [dslope_of_ne f hab, dslope_of_ne g hab, slope_def_field, slope_def_field,
      he ha, he hb]

theorem eqOn_dslope_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (he : EqOn f g U) {a : ℂ} (ha : a ∈ U) : EqOn (dslope f a) (dslope g a) U :=
  fun _ hb => dslope_eq_of_eqOn hU he ha hb

theorem second_dslope_eq_of_eqOn {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (he : EqOn f g U) {a b c : ℂ} (ha : a ∈ U) (hb : b ∈ U) (hc : c ∈ U) :
    dslope (dslope f a) b c = dslope (dslope g a) b c :=
  dslope_eq_of_eqOn hU (eqOn_dslope_of_eqOn hU he ha) hb hc

end PGM
