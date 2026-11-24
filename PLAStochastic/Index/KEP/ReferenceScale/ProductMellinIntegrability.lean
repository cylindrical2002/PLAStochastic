import PLAStochastic.Index.KEP.ReferenceScale.ProductMellinFields
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Absolute integrability of the complete finite Mellin fields

Every derivative term still has one factor for every original coordinate.
Single and double insertions are identified with products of updated marginal
functions before Fubini is used. This also covers diagonal terms and a single
coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset

theorem kep_integrable_single_insertion {n : ℕ} {f g : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => g (x i) * ∏ l ∈ univ.erase i, f (x l)) volume := by
  let F : Fin n → ℝ → ℝ := Function.update (fun _ => f) i g
  have hF : ∀ l, Integrable (F l) volume := by
    intro l
    by_cases hl : l = i
    · subst l
      simpa only [F, Function.update_self] using hg
    · simpa only [F, Function.update_of_ne hl] using hf
  have hp := Integrable.fintype_prod hF
  have he (x : Fin n → ℝ) : (∏ l, F l (x l)) = g (x i) * ∏ l ∈ univ.erase i, f (x l) := by
    have hh : (fun l => F l (x l)) = Function.update (fun l => f (x l)) i (g (x i)) := by
      funext l
      by_cases hl : l = i
      · subst l
        simp only [F, Function.update_self]
      · simp only [F, Function.update_of_ne hl]
    rw [hh, prod_update_of_mem (mem_univ i), sdiff_singleton_eq_erase]
  simpa only [he, ← volume_pi] using hp

theorem kep_integrable_double_insertion {n : ℕ} {f g h : ℝ → ℝ}
    (hf : Integrable f volume) (hg : Integrable g volume) (hh : Integrable h volume)
    (i j : Fin n) (hij : j ≠ i) :
    Integrable (fun x : Fin n → ℝ => g (x i) *
      (h (x j) * ∏ l ∈ (univ.erase i).erase j, f (x l))) volume := by
  let F : Fin n → ℝ → ℝ := Function.update (Function.update (fun _ => f) i g) j h
  have hF : ∀ l, Integrable (F l) volume := by
    intro l
    by_cases hlj : l = j
    · subst l
      simpa only [F, Function.update_self] using hh
    · by_cases hli : l = i
      · subst l
        simpa only [F, Function.update_of_ne hlj, Function.update_self] using hg
      · simpa only [F, Function.update_of_ne hlj, Function.update_of_ne hli] using hf
  have hp := Integrable.fintype_prod hF
  have he (x : Fin n → ℝ) : (∏ l, F l (x l)) =
      g (x i) * (h (x j) * ∏ l ∈ (univ.erase i).erase j, f (x l)) := by
    have hfun : (fun l => F l (x l)) = Function.update
        (Function.update (fun l => f (x l)) i (g (x i))) j (h (x j)) := by
      funext l
      by_cases hlj : l = j
      · subst l
        simp only [F, Function.update_self]
      · by_cases hli : l = i
        · subst l
          simp only [F, Function.update_of_ne hlj, Function.update_self]
        · simp only [F, Function.update_of_ne hlj, Function.update_of_ne hli]
    rw [hfun, prod_update_of_mem (mem_univ j), sdiff_singleton_eq_erase,
      prod_update_of_mem (mem_erase.mpr ⟨hij.symm, mem_univ i⟩), sdiff_singleton_eq_erase, erase_right_comm]
    ring
  simpa only [he, ← volume_pi] using hp

theorem kepProductMellin_integrable {n : ℕ} {f : ℝ → ℝ}
    (h0 : Integrable f volume) (h1 : Integrable (mellinOp f) volume)
    (h2 : Integrable (mellinOp (mellinOp f)) volume) :
    Integrable (kepProductDensity (n := n) f) volume ∧
      Integrable (kepProductMellinFirst (n := n) f) volume ∧
      Integrable (kepProductMellinSecond (n := n) f) volume := by
  refine ⟨?_, ?_, ?_⟩
  · convert Integrable.fintype_prod (fun _ : Fin n => h0) using 1 <;> rfl
  · unfold kepProductMellinFirst kepFiniteProductFirst
    exact integrable_finsetSum univ fun i _ => kep_integrable_single_insertion h0 h1 i
  · unfold kepProductMellinSecond kepFiniteProductSecond
    apply integrable_finsetSum
    intro i _
    have hdiag := kep_integrable_single_insertion h0 h2 i
    have hcross : Integrable (fun x : Fin n → ℝ => mellinOp f (x i) *
        ∑ j ∈ univ.erase i, mellinOp f (x j) * ∏ l ∈ (univ.erase i).erase j, f (x l)) volume := by
      simp_rw [mul_sum]
      exact integrable_finsetSum _ fun j hj =>
        kep_integrable_double_insertion h0 h1 h1 i j (mem_erase.mp hj).1
    exact hdiag.add hcross

end

end PGM
