import PLAStochastic.Index.KEP.ReferenceScale.RareNegativeBudget

/-!
# Geometric combination of genuine finite-measure event budgets

The combination uses only containment and Cauchy--Schwarz. It does not require
independence of the events, and two linear insertion costs remain linear.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_measureReal_event_geometric {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} [IsFiniteMeasure mu] {E U L : Set alpha}
    (hEU : E ⊆ U) (hEL : E ⊆ L) {A B : ℝ} (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hU : mu.real U ≤ A) (hL : mu.real L ≤ B) : mu.real E ≤ Real.sqrt (A * B) := by
  have hu := (measureReal_mono hEU).trans hU
  have hl := (measureReal_mono hEL).trans hL
  have hn : 0 ≤ mu.real E := measureReal_nonneg
  apply Real.le_sqrt_of_sq_le
  simpa only [sq] using mul_le_mul hu hl hn hA

theorem kep_sqrt_two_linear_exponential_budgets {A B J x y : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hJ : 0 ≤ J) :
    Real.sqrt ((A * (1 + J) * Real.exp x) * (B * (1 + J) * Real.exp y)) =
      Real.sqrt (A * B) * (1 + J) * Real.exp ((x + y) / 2) := by
  rw [show (A * (1 + J) * Real.exp x) * (B * (1 + J) * Real.exp y) =
      (A * B) * (1 + J) ^ 2 * Real.exp (x + y) by rw [Real.exp_add]; ring]
  rw [Real.sqrt_mul (by positivity : 0 ≤ A * B * (1 + J) ^ 2),
    Real.sqrt_mul (mul_nonneg hA hB), Real.sqrt_sq (by positivity : 0 ≤ 1 + J),
    ← Real.exp_half]

theorem kep_weighted_event_cauchy {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} [IsFiniteMeasure mu] {S : alpha → ℝ} (hS : Measurable S)
    {E : Set alpha} (hE : MeasurableSet E) {u A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hexp : Integrable (fun x => Real.exp ((2 * u) * S x)) mu)
    (hexpA : (∫ x, Real.exp ((2 * u) * S x) ∂mu) ≤ A) (hmass : mu.real E ≤ B) :
    (∫ x in E, Real.exp (u * S x) ∂mu) ≤ Real.sqrt (A * B) := by
  let f := fun x => Real.exp (u * S x)
  let g := E.indicator (fun _ : alpha => (1 : ℝ))
  have hf : Measurable f := (hS.const_mul u).exp
  have hg : Measurable g := measurable_const.indicator hE
  have hf2 (x) : f x ^ 2 = Real.exp ((2 * u) * S x) := by
    dsimp [f]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hg2 (x) : g x ^ 2 = g x := by
    by_cases hx : x ∈ E
    · simp only [g, indicator_of_mem hx, one_pow]
    · simp only [g, indicator_of_notMem hx, zero_pow, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true]
  have hfi : Integrable (fun x => f x ^ 2) mu := by simpa only [hf2] using hexp
  have hgi : Integrable (fun x => g x ^ 2) mu := by
    simpa only [hg2] using (integrable_const (1 : ℝ)).indicator hE
  have hgB : (∫ x, g x ^ 2 ∂mu) ≤ B := by
    simp only [hg2, g, integral_indicator hE, integral_const, smul_eq_mul, mul_one,
      measureReal_restrict_apply_univ]
    exact hmass
  have hfA : (∫ x, f x ^ 2 ∂mu) ≤ A := by simpa only [hf2] using hexpA
  have hh := kep_integral_mul_le_sqrt_budget hf hg (fun _ => (Real.exp_pos _).le)
    (fun x => indicator_nonneg (fun _ _ => zero_le_one) x) hfi hgi hA hB hfA hgB
  have heq : (fun x => f x * g x) = E.indicator (fun x => Real.exp (u * S x)) := by
    funext x
    by_cases hx : x ∈ E
    · simp only [f, g, indicator_of_mem hx, mul_one]
    · simp only [g, indicator_of_notMem hx, mul_zero]
  rw [heq, integral_indicator hE] at hh
  exact hh

end

end PGM
