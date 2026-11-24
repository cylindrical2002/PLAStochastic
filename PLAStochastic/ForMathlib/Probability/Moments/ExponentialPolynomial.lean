import PLAStochastic.ForMathlib.Analysis.Calculus.ExponentialDerivative
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Polynomial moments from a fixed exponential moment

The random variable need only be measurable and almost surely nonnegative.
No independence is required. Finite sums inherit integer moment bounds from
their individual increments by the pointwise power-sum inequality.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem polynomial_moment_of_exponential {X : Ω → ℝ} (hX : Measurable X)
    {theta B : ℝ} (htheta : 0 < theta) (hpos : ∀ᵐ w ∂P, 0 ≤ X w)
    (hi : Integrable (fun w => Real.exp (theta * X w)) P)
    (hb : ∫ w, Real.exp (theta * X w) ∂P ≤ B) (k : ℕ) :
    Integrable (fun w => X w ^ k) P ∧
      ∫ w, X w ^ k ∂P ≤ (k.factorial : ℝ) / theta ^ k * B := by
  let C := (k.factorial : ℝ) / theta ^ k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound : ∀ᵐ w ∂P, ‖X w ^ k‖ ≤ C * Real.exp (theta * X w) := by
    filter_upwards [hpos] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hw k)]
    exact Real.pow_le_factorial_inv_mul_exp k htheta hw
  have hp : Integrable (fun w => X w ^ k) P :=
    (hi.const_mul C).mono' (hX.pow_const k).aestronglyMeasurable hbound
  refine ⟨hp, ?_⟩
  calc
    _ ≤ ∫ w, C * Real.exp (theta * X w) ∂P :=
      integral_mono_ae hp (hi.const_mul C)
        (hbound.mono fun w hw => (le_abs_self _).trans hw)
    _ = C * ∫ w, Real.exp (theta * X w) ∂P := integral_const_mul _ _
    _ ≤ C * B := mul_le_mul_of_nonneg_left hb hC

theorem integrable_finite_sum_pow {X : ℕ → Ω → ℝ} (N k : ℕ)
    (hX : ∀ i < N, Measurable (X i))
    (hpos : ∀ i < N, ∀ᵐ w ∂P, 0 ≤ X i w)
    (hi : ∀ i < N, Integrable (fun w => X i w ^ (k + 1)) P) :
    Integrable (fun w => (∑ i ∈ Finset.range N, X i w) ^ (k + 1)) P := by
  have hdom : Integrable (fun w => (N : ℝ) ^ k *
      ∑ i ∈ Finset.range N, X i w ^ (k + 1)) P :=
    (integrable_finsetSum _ (fun i hi' => hi i (Finset.mem_range.mp hi'))).const_mul _
  apply hdom.mono'
    ((Finset.measurable_sum _ fun i hi' => hX i (Finset.mem_range.mp hi')).pow_const _).aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr fun i =>
    ae_all_iff.mpr fun hi' : i < N => hpos i hi'] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg
    (Finset.sum_nonneg fun i hi' => hw i (Finset.mem_range.mp hi')) _)]
  simpa only [Finset.card_range] using
    pow_sum_le_card_mul_sum_pow
      (s := Finset.range N) (f := fun i => X i w)
      (fun i hi' => hw i (Finset.mem_range.mp hi')) k

theorem integral_finite_sum_pow_le {X : ℕ → Ω → ℝ} (N k : ℕ)
    (hX : ∀ i < N, Measurable (X i))
    (hpos : ∀ i < N, ∀ᵐ w ∂P, 0 ≤ X i w)
    (hi : ∀ i < N, Integrable (fun w => X i w ^ (k + 1)) P)
    {B : ℝ} (hb : ∀ i < N, ∫ w, X i w ^ (k + 1) ∂P ≤ B) :
    ∫ w, (∑ i ∈ Finset.range N, X i w) ^ (k + 1) ∂P ≤ (N : ℝ) ^ (k + 1) * B := by
  have hdom : Integrable (fun w => (N : ℝ) ^ k *
      ∑ i ∈ Finset.range N, X i w ^ (k + 1)) P :=
    (integrable_finsetSum _ (fun i hi' => hi i (Finset.mem_range.mp hi'))).const_mul _
  calc
    _ ≤ ∫ w, (N : ℝ) ^ k * ∑ i ∈ Finset.range N, X i w ^ (k + 1) ∂P := by
      apply integral_mono_ae (integrable_finite_sum_pow N k hX hpos hi) hdom
      filter_upwards [ae_all_iff.mpr fun i =>
        ae_all_iff.mpr fun hi' : i < N => hpos i hi'] with w hw
      simpa only [Finset.card_range] using
        pow_sum_le_card_mul_sum_pow
          (s := Finset.range N) (f := fun i => X i w)
          (fun i hi' => hw i (Finset.mem_range.mp hi')) k
    _ = (N : ℝ) ^ k * ∑ i ∈ Finset.range N, ∫ w, X i w ^ (k + 1) ∂P := by
      rw [integral_const_mul, integral_finsetSum _ (fun i hi' => hi i (Finset.mem_range.mp hi'))]
    _ ≤ (N : ℝ) ^ k * ∑ _i ∈ Finset.range N, B := by
      gcongr with i hi'
      exact hb i (Finset.mem_range.mp hi')
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, pow_succ]; ring

end

end ProbabilityTheory
