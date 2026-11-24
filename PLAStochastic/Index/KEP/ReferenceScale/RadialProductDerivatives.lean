import PLAStochastic.Index.KEP.ReferenceScale.MellinDerivativeBudget
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The exact radial density derivatives with at most two insertions

The dilation Jacobian is distributed among the coordinates. Its first two
derivatives are the first and second Mellin insertions. The product rule uses
an ordered sum for the two distinct first insertions, so no diagonal term or
combinatorial factor is lost, including at zeros of the density.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open Finset

def kepDilationFactor (f : ℝ → ℝ) (x s : ℝ) : ℝ :=
  Real.exp s * f (Real.exp s * x)

def kepDilationFactorFirst (f : ℝ → ℝ) (x s : ℝ) : ℝ :=
  Real.exp s * mellinOp f (Real.exp s * x)

def kepDilationFactorSecond (f : ℝ → ℝ) (x s : ℝ) : ℝ :=
  Real.exp s * mellinOp (mellinOp f) (Real.exp s * x)

theorem kepDilationFactor_derivatives {f f' f'' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x)
    (x s : ℝ) :
    HasDerivAt (kepDilationFactor f x) (kepDilationFactorFirst f x s) s ∧
      HasDerivAt (kepDilationFactorFirst f x) (kepDilationFactorSecond f x s) s := by
  have he1 : mellinOp f = fun y => f y + y * f' y := by
    funext y
    rw [mellinOp, (hdf y).deriv]
  have hd1 (y : ℝ) : HasDerivAt (mellinOp f) (2 * f' y + y * f'' y) y := by
    rw [he1]
    convert (hdf y).add ((hasDerivAt_id y).mul (hddf y)) using 1 <;> first
    | rfl
    | (dsimp only [id_eq]; ring)
  have he2 := kep_mellin_second_eq hdf hddf
  have hx := (Real.hasDerivAt_exp s).mul_const x
  unfold kepDilationFactor kepDilationFactorFirst kepDilationFactorSecond
  constructor
  · convert (Real.hasDerivAt_exp s).mul ((hdf _).comp s hx) using 1 <;> first
    | rfl
    | (rw [he1]; dsimp only [Function.comp_apply]; ring)
  · convert (Real.hasDerivAt_exp s).mul ((hd1 _).comp s hx) using 1 <;> first
    | rfl
    | (rw [he2, he1]; dsimp only [Function.comp_apply]; ring)

def kepFiniteProductFirst {I : Type*} [DecidableEq I]
    (G G' : I → ℝ → ℝ) (S : Finset I) (s : ℝ) : ℝ :=
  ∑ i ∈ S, G' i s * ∏ j ∈ S.erase i, G j s

def kepFiniteProductSecond {I : Type*} [DecidableEq I]
    (G G' G'' : I → ℝ → ℝ) (S : Finset I) (s : ℝ) : ℝ :=
  ∑ i ∈ S, (G'' i s * (∏ j ∈ S.erase i, G j s) +
    G' i s * (∑ j ∈ S.erase i, G' j s * ∏ l ∈ (S.erase i).erase j, G l s))

theorem kepFiniteProduct_derivatives {I : Type*} [DecidableEq I]
    {G G' G'' : I → ℝ → ℝ} (S : Finset I) (s : ℝ)
    (hG : ∀ i ∈ S, HasDerivAt (G i) (G' i s) s)
    (hG' : ∀ i ∈ S, HasDerivAt (G' i) (G'' i s) s) :
    HasDerivAt (fun t => ∏ i ∈ S, G i t) (kepFiniteProductFirst G G' S s) s ∧
      HasDerivAt (kepFiniteProductFirst G G' S) (kepFiniteProductSecond G G' G'' S s) s := by
  constructor
  · simpa only [kepFiniteProductFirst, smul_eq_mul, mul_comm] using
      HasDerivAt.fun_finsetProd hG
  · unfold kepFiniteProductFirst kepFiniteProductSecond
    apply HasDerivAt.fun_sum
    intro i hi
    have hp := HasDerivAt.fun_finsetProd (u := S.erase i)
      (fun j hj => hG j (mem_of_mem_erase hj))
    convert (hG' i hi).mul hp using 1 <;> first
    | rfl
    | simp only [smul_eq_mul, mul_comm]

theorem kepRadialProduct_derivatives {n : ℕ} {f f' f'' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x)
    (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t => ∏ i, kepDilationFactor f (x i) t)
      (kepFiniteProductFirst (fun i => kepDilationFactor f (x i))
        (fun i => kepDilationFactorFirst f (x i)) univ s) s ∧
    HasDerivAt (kepFiniteProductFirst (fun i => kepDilationFactor f (x i))
      (fun i => kepDilationFactorFirst f (x i)) univ)
      (kepFiniteProductSecond (fun i => kepDilationFactor f (x i))
        (fun i => kepDilationFactorFirst f (x i))
        (fun i => kepDilationFactorSecond f (x i)) univ s) s :=
  kepFiniteProduct_derivatives univ s
    (fun i _ => (kepDilationFactor_derivatives hdf hddf (x i) s).1)
    (fun i _ => (kepDilationFactor_derivatives hdf hddf (x i) s).2)

end

end PGM
