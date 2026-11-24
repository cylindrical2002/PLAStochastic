import PLAStochastic.Index.KEP.Additive.PolynomialBudgets
import PLAStochastic.Index.KEP.ReferenceScale.MeanSpan

/-!
# Additive actual height from count and tail bounds at the actual reference scale

The proved exponential reference budgets discharge all scale assumptions in the
polynomial assembly. The two remaining hypotheses concern actual layer counts
and actual early termination. They have not yet been proved for general Model K.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem H_EP_additive_of_reference_count_tail
    {keys : ℕ → Ω → ℕ → ℝ} (hkeys : ∀ n, Measurable (keys n))
    {eps0 A D R K p r : ℝ}
    (hA : 1 ≤ A) (hD : 0 ≤ D) (hR : 1 ≤ R) (hK : 0 ≤ K)
    (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hcount : ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n → ∀ L,
      (∫ ω, ((epLayer eps (keys n ω) n L).2 : ℝ) ∂P) ≤
        A * (n : ℝ) / kepReferenceSpan eps L + D * eps ^ p)
    (htail : ∀ eps, eps0 ≤ eps → ∀ n : ℕ, 2 ≤ n → ∀ L,
      (R * eps ^ r) * kepReferenceSpan eps L < n →
        P.real {ω | epHeight eps (keys n ω) n ≤ L} ≤ K * kepReferenceSpan eps L / n) :
    ∃ eps1 C : ℝ, ∀ eps, eps1 ≤ eps → ∀ n : ℕ, 2 ≤ n →
      |(∫ ω, (epHeight eps (keys n ω) n : ℝ) ∂P) -
        Real.log n / Real.log (gepC eps)| ≤ C := by
  obtain ⟨e0, B, -, hB, hbudget⟩ := kepReferenceSpan_budget
  apply H_EP_additive_of_polynomial_count_tail hkeys (eps0 := max eps0 e0)
    hB hA hD hR hK hp hr
  · intro eps heps
    exact (hbudget eps (le_trans (le_max_right _ _) heps)).1
  · intro eps heps
    exact (hbudget eps (le_trans (le_max_right _ _) heps)).2.1
  · intro eps heps
    exact (hbudget eps (le_trans (le_max_right _ _) heps)).2.2.1
  · intro eps heps
    exact (hbudget eps (le_trans (le_max_right _ _) heps)).2.2.2.1
  · intro eps heps
    exact (hbudget eps (le_trans (le_max_right _ _) heps)).2.2.2.2
  · intro eps heps
    exact hcount eps (le_trans (le_max_left _ _) heps)
  · intro eps heps
    exact htail eps (le_trans (le_max_left _ _) heps)

end

end PGM
