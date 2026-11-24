import PLAStochastic.Index.KEP.ReferenceScale.RadialProductDerivatives

/-!
# Finite-dimensional Mellin fields with the full radial Jacobian

The density, first field and second field are expressed as finite products
with zero, one or two Mellin insertions. Common dilation factors have exactly
the degree of the full coordinate set, even on diagonals and at density zeros.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open Finset

theorem kepFiniteProductFirst_common_factor {I : Type*} [DecidableEq I]
    (G G' : I → ℝ → ℝ) (S : Finset I) (c : ℝ → ℝ) (s : ℝ) :
    kepFiniteProductFirst (fun i t => c t * G i t) (fun i t => c t * G' i t) S s =
      (c s) ^ S.card * kepFiniteProductFirst G G' S s := by
  unfold kepFiniteProductFirst
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [prod_mul_distrib, prod_const]
  have hcard : S.card = (S.erase i).card + 1 := (card_erase_add_one hi).symm
  rw [hcard, pow_succ]
  ring

theorem kepFiniteProductSecond_common_factor {I : Type*} [DecidableEq I]
    (G G' G'' : I → ℝ → ℝ) (S : Finset I) (c : ℝ → ℝ) (s : ℝ) :
    kepFiniteProductSecond (fun i t => c t * G i t) (fun i t => c t * G' i t)
      (fun i t => c t * G'' i t) S s =
        (c s) ^ S.card * kepFiniteProductSecond G G' G'' S s := by
  change (∑ i ∈ S, (c s * G'' i s * (∏ j ∈ S.erase i, c s * G j s) +
    (c s * G' i s) * kepFiniteProductFirst (fun i t => c t * G i t)
      (fun i t => c t * G' i t) (S.erase i) s)) = _
  simp_rw [kepFiniteProductFirst_common_factor]
  unfold kepFiniteProductSecond
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [prod_mul_distrib, prod_const]
  have hcard : S.card = (S.erase i).card + 1 := (card_erase_add_one hi).symm
  rw [hcard, pow_succ]
  unfold kepFiniteProductFirst
  ring

def kepProductDensity {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ := ∏ i, f (x i)

def kepProductMellinFirst {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  kepFiniteProductFirst (fun i _ => f (x i)) (fun i _ => mellinOp f (x i)) univ 0

def kepProductMellinSecond {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  kepFiniteProductSecond (fun i _ => f (x i)) (fun i _ => mellinOp f (x i))
    (fun i _ => mellinOp (mellinOp f) (x i)) univ 0

theorem kepProductMellin_radial_derivatives {n : ℕ} {f f' f'' : ℝ → ℝ}
    (hdf : ∀ x, HasDerivAt f (f' x) x) (hddf : ∀ x, HasDerivAt f' (f'' x) x)
    (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t => Real.exp ((n : ℝ) * t) * kepProductDensity f (Real.exp t • x))
      (Real.exp ((n : ℝ) * s) * kepProductMellinFirst f (Real.exp s • x)) s ∧
    HasDerivAt (fun t => Real.exp ((n : ℝ) * t) * kepProductMellinFirst f (Real.exp t • x))
      (Real.exp ((n : ℝ) * s) * kepProductMellinSecond f (Real.exp s • x)) s := by
  have hprod (t : ℝ) : (∏ i, kepDilationFactor f (x i) t) =
      Real.exp ((n : ℝ) * t) * kepProductDensity f (Real.exp t • x) := by
    unfold kepDilationFactor kepProductDensity
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
    rfl
  have hfirst (t : ℝ) : kepFiniteProductFirst (fun i => kepDilationFactor f (x i))
      (fun i => kepDilationFactorFirst f (x i)) univ t =
        Real.exp ((n : ℝ) * t) * kepProductMellinFirst f (Real.exp t • x) := by
    unfold kepDilationFactor kepDilationFactorFirst
    rw [kepFiniteProductFirst_common_factor, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
    rfl
  have hsecond (t : ℝ) : kepFiniteProductSecond (fun i => kepDilationFactor f (x i))
      (fun i => kepDilationFactorFirst f (x i)) (fun i => kepDilationFactorSecond f (x i)) univ t =
        Real.exp ((n : ℝ) * t) * kepProductMellinSecond f (Real.exp t • x) := by
    unfold kepDilationFactor kepDilationFactorFirst kepDilationFactorSecond
    rw [kepFiniteProductSecond_common_factor, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
    rfl
  have hfirstFun := funext hfirst
  have hh := kepRadialProduct_derivatives hdf hddf x s
  rw [hfirstFun] at hh
  simp_rw [hprod, hsecond] at hh
  exact hh

end

end PGM
