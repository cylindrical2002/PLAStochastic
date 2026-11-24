import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Notation

/-!
# Union bounds over lattice pairs and splitting an expectation on a good event

Two small measure-theoretic tools for the rank-equispaced height theorem:
a union bound over all pairs `(d, K)` with `d, K ≤ 2n`, and the bound
`E H ≤ U + Hmax · P(bad)` for a bounded `H` that is at most `U` off the bad event.
-/

namespace PGM

open MeasureTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Union bound over the pairs `(d, K)` in `[0, 2n]²`. -/
theorem measureReal_biUnion_pairs_le [IsFiniteMeasure P] (n : ℕ) (bad : ℕ → ℕ → Set Ω)
    {q : ℝ} (hq : ∀ d K, d ≤ 2 * n → K ≤ 2 * n → P.real (bad d K) ≤ q) :
    P.real (⋃ d ∈ range (2 * n + 1), ⋃ K ∈ range (2 * n + 1), bad d K) ≤
      ((2 * n + 1 : ℕ) : ℝ) ^ 2 * q := by
  calc P.real (⋃ d ∈ range (2 * n + 1), ⋃ K ∈ range (2 * n + 1), bad d K)
      ≤ ∑ d ∈ range (2 * n + 1), P.real (⋃ K ∈ range (2 * n + 1), bad d K) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ d ∈ range (2 * n + 1), ∑ K ∈ range (2 * n + 1), P.real (bad d K) :=
        sum_le_sum fun d _ => measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _d ∈ range (2 * n + 1), ∑ _K ∈ range (2 * n + 1), q := by
        refine sum_le_sum fun d hd => sum_le_sum fun K hK => hq d K ?_ ?_
        · have := mem_range.1 hd; omega
        · have := mem_range.1 hK; omega
    _ = ((2 * n + 1 : ℕ) : ℝ) ^ 2 * q := by
        simp only [sum_const, card_range, nsmul_eq_mul]; push_cast; ring

/-- Splitting an expectation: if `0 ≤ H ≤ Hmax` everywhere and `H ≤ U` off `bad`,
    then `E H ≤ U + Hmax · P(bad)`. -/
theorem integral_le_of_good [IsProbabilityMeasure P] {H : Ω → ℝ} {bad : Set Ω}
    (hbad : MeasurableSet bad) (hH : AEStronglyMeasurable H P) {U Hmax : ℝ} (hU : 0 ≤ U)
    (h0 : ∀ ω, 0 ≤ H ω) (hmax : ∀ ω, H ω ≤ Hmax) (hgood : ∀ ω, ω ∉ bad → H ω ≤ U) :
    ∫ ω, H ω ∂P ≤ U + Hmax * P.real bad := by
  have hint : Integrable H P :=
    Integrable.mono' (integrable_const Hmax) hH
      (Filter.Eventually.of_forall fun ω => by rw [Real.norm_of_nonneg (h0 ω)]; exact hmax ω)
  have hpt : ∀ ω, H ω ≤ U + bad.indicator (fun _ => Hmax) ω := by
    intro ω
    by_cases hω : ω ∈ bad
    · rw [Set.indicator_of_mem hω]; linarith [hmax ω]
    · rw [Set.indicator_of_notMem hω]; linarith [hgood ω hω]
  have hint2 : Integrable (fun ω => U + bad.indicator (fun _ => Hmax) ω) P :=
    (integrable_const U).add ((integrable_const Hmax).indicator hbad)
  calc ∫ ω, H ω ∂P ≤ ∫ ω, (U + bad.indicator (fun _ => Hmax) ω) ∂P :=
        integral_mono hint hint2 hpt
    _ = U + Hmax * P.real bad := by
        rw [integral_add (integrable_const U) ((integrable_const Hmax).indicator hbad),
          integral_const, integral_indicator hbad, setIntegral_const]
        simp [smul_eq_mul, mul_comm]

end PGM
