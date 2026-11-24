import PLAStochastic.Index.KEP.Poisson.ParentOutput
import PLAStochastic.Index.KEP.Poisson.FiniteComparison
import PLAStochastic.Index.KEP.PolynomialWindowBudget

/-!
# Uniform polynomial costs of the actual finite and stopped comparisons

The previously paid integer path moments turn a quadratic stopping window
into a linear epsilon factor for the child error and an epsilon-cubed factor
for the state drift. The same bound applies to the original parent output.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoisson_finite_comparison_window_budget {f : ℝ → ℝ}
    {flo fhi L eps n theta B r b A : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hb : 0 ≤ b) (hA : 0 ≤ A) (heps : 1 ≤ eps)
    (nu : ProbabilityMeasure ℝ) (x : ℝ) (j M : ℕ) (hM : (M : ℝ) ≤ A * eps ^ 2)
    (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (hpos : ∀ᵐ z ∂(nu : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z)) (nu : Measure ℝ))
    (hmgf : ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂(nu : Measure ℝ) ≤ B)
    (hstep : ∀ S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S)
      (nu : Measure ℝ) ≤ r + b * |S| ^ (2 / 3 : ℝ)) :
    measureHellinger (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j M))
      ((iidLaw nu).map (kepGapPrefix M)) ≤
        (2 * A + 4 * (A + (2 / (theta / (fhi / flo)) ^ 2 * B) * A ^ 3) + 1) *
          (eps * r + eps ^ 3 * b) := by
  have h := kepPoisson_finite_prefix_comparison hf hn htheta hB hr hb nu x j M hm hfin
    hchild hpos hi hmgf hstep
  have hc : 0 ≤ 2 / (theta / (fhi / flo)) ^ 2 * B := by positivity
  have hp := kep_polynomial_window_budget (r := r) (b := b) heps (Nat.cast_nonneg M)
    hA hc (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 4) hM
  exact kep_comparison_of_quadratic_budget (zero_le_one.trans heps) hr hb
    (by positivity) (by positivity) (h.trans hp)

theorem kepPoisson_parent_comparison_window_budget {f : ℝ → ℝ}
    {flo fhi L eps n theta B r b A : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hb : 0 ≤ b) (hA : 0 ≤ A) (heps : 1 ≤ eps)
    (x : ℝ) (j M : ℕ) (hM1 : 1 ≤ M) (hM : (M : ℝ) ≤ A * eps ^ 2)
    (hclass : kepReferenceClassicalThreshold ≤ eps) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (hpos : ∀ᵐ z ∂(kepReferenceLaw eps j : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z)) (kepReferenceLaw eps j : Measure ℝ))
    (hmgf : ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ B)
    (hstep : ∀ S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S)
      (kepReferenceLaw eps j : Measure ℝ) ≤ r + b * |S| ^ (2 / 3 : ℝ))
    (hPtail : ∀ k, expSeqMeasure.real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤ (1 / 2 : ℝ) ^ k)
    (hQtail : ∀ k, (iidLaw (kepReferenceLaw eps j)).real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ (1 / 2 : ℝ) ^ k) :
    measureHellinger (kepPoissonLayerMeasure hf eps n x (j + 1))
      (kepReferenceLaw eps (j + 1)) ≤
        (4 * A + 8 * (A +
          (Real.sqrt (24 / (theta / (fhi / flo)) ^ 4 * B) / (1 - Real.sqrt (1 / 2)) ^ 3) * A ^ 3) + 1) *
            (eps * r + eps ^ 3 * b) := by
  have h := kepPoisson_stopped_path_comparison hf hn htheta hB hr hb
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (kepReferenceLaw eps j) x j M hM1 hm hfin hchild hpos hi hmgf hstep hPtail hQtail
  have hparent := kepPoisson_parent_output_comparison_le hf hn x j hclass hm
  have hsquare := pow_le_pow_left₀ (measureHellinger_nonneg _ _) hparent 2
  have hc : 0 ≤ Real.sqrt (24 / (theta / (fhi / flo)) ^ 4 * B) / (1 - Real.sqrt (1 / 2)) ^ 3 := by
    have hs : Real.sqrt (1 / 2 : ℝ) < 1 := (Real.sqrt_lt' one_pos).mpr (by norm_num)
    positivity
  have hp := kep_polynomial_window_budget (r := r) (b := b) heps (Nat.cast_nonneg M)
    hA hc (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 8) hM
  have hraw : measureHellinger (kepPoissonLayerMeasure hf eps n x (j + 1))
      (kepReferenceLaw eps (j + 1)) ^ 2 ≤
      4 * (M : ℝ) * r ^ 2 + 8 * b ^ 2 * ((M : ℝ) +
        (Real.sqrt (24 / (theta / (fhi / flo)) ^ 4 * B) / (1 - Real.sqrt (1 / 2)) ^ 3) * (M : ℝ) ^ 3) := by
    apply (hsquare.trans h).trans_eq
    norm_num
    ring
  exact kep_comparison_of_quadratic_budget (zero_le_one.trans heps) hr hb
    (by positivity) (by positivity) (hraw.trans hp)

end

end PGM
