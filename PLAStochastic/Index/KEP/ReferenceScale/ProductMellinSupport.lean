import PLAStochastic.Index.KEP.ReferenceScale.ProductMellinFields

/-!
# Support and continuity of every complete Mellin field

A vanishing original coordinate kills all three fields, including the terms
where that coordinate itself is differentiated. The actual reference zero
extension therefore introduces no hidden boundary term on a coordinate face.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open Finset

theorem kepProductMellin_zero_coordinate {n : ℕ} {f : ℝ → ℝ} (x : Fin n → ℝ) (q : Fin n)
    (h0 : f (x q) = 0) (h1 : mellinOp f (x q) = 0)
    (h2 : mellinOp (mellinOp f) (x q) = 0) :
    kepProductDensity f x = 0 ∧ kepProductMellinFirst f x = 0 ∧
      kepProductMellinSecond f x = 0 := by
  have hprod {S : Finset (Fin n)} (hq : q ∈ S) : (∏ l ∈ S, f (x l)) = 0 :=
    prod_eq_zero hq h0
  have hfirst (i : Fin n) : mellinOp f (x i) * (∏ l ∈ univ.erase i, f (x l)) = 0 := by
    by_cases hi : i = q
    · subst i
      rw [h1, zero_mul]
    · rw [hprod (mem_erase.mpr ⟨(fun h => hi h.symm), mem_univ q⟩), mul_zero]
  refine ⟨hprod (mem_univ q), ?_, ?_⟩
  · unfold kepProductMellinFirst kepFiniteProductFirst
    exact sum_eq_zero (fun i _ => hfirst i)
  · unfold kepProductMellinSecond kepFiniteProductSecond
    apply sum_eq_zero
    intro i _
    have hdiag : mellinOp (mellinOp f) (x i) * (∏ l ∈ univ.erase i, f (x l)) = 0 := by
      by_cases hi : i = q
      · subst i
        rw [h2, zero_mul]
      · rw [hprod (mem_erase.mpr ⟨(fun h => hi h.symm), mem_univ q⟩), mul_zero]
    rw [hdiag, zero_add, mul_sum]
    apply sum_eq_zero
    intro j _
    dsimp only
    by_cases hi : i = q
    · subst i
      rw [h1, zero_mul]
    · by_cases hj : j = q
      · subst j
        rw [h1, zero_mul, mul_zero]
      · rw [hprod (mem_erase.mpr ⟨(fun h => hj h.symm), mem_erase.mpr ⟨(fun h => hi h.symm), mem_univ q⟩⟩), mul_zero,
          mul_zero]

theorem kepProductMellin_continuous {n : ℕ} {f f' f'' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x)
    (hcf'' : Continuous f'') :
    Continuous (kepProductDensity (n := n) f) ∧
      Continuous (kepProductMellinFirst (n := n) f) ∧
      Continuous (kepProductMellinSecond (n := n) f) := by
  have hcf := continuous_iff_continuousAt.mpr fun x => (hdf x).continuousAt
  have hcf' := continuous_iff_continuousAt.mpr fun x => (hddf x).continuousAt
  have he1 : mellinOp f = fun x => f x + x * f' x := by
    funext x
    rw [mellinOp, (hdf x).deriv]
  have hc1 : Continuous (mellinOp f) := by rw [he1]; fun_prop
  have hc2 : Continuous (mellinOp (mellinOp f)) := by
    rw [kep_mellin_second_eq hdf hddf]
    fun_prop
  unfold kepProductDensity kepProductMellinFirst kepProductMellinSecond
    kepFiniteProductFirst kepFiniteProductSecond
  constructor
  · fun_prop
  constructor <;> fun_prop

end

end PGM
