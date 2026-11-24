import PLAStochastic.Index.KEP.Poisson.ComparisonWindowBudget
import PLAStochastic.Index.KEP.Poisson.ParentFiniteness
import PLAStochastic.Index.KEP.Poisson.ParentExponential
import PLAStochastic.Index.KEP.Poisson.MeanFromComparison
import PLAStochastic.Index.KEP.Poisson.WindowProbability

/-!
# The joint one-layer transfer on the original Poisson hierarchy

The finite comparison pays the actual window survival probability. True
completed restarts pay the geometric stopping tail and parent finiteness.
The conditional mean and cumulant then pay the fixed parent exponential
moment, while the full stopped-path comparison pays the parent error.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem kepPoisson_joint_one_layer_transfer {f : ℝ → ℝ}
    {flo fhi L eps n theta r b A : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hr : 0 ≤ r) (hb : 0 ≤ b) (hA : 0 ≤ A) (heps : 1 ≤ eps)
    (hclass : kepReferenceClassicalThreshold ≤ eps) (j M : ℕ)
    (hM1 : 1 ≤ M) (hM : (M : ℝ) ≤ A * eps ^ 2) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ x, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j 1 g ≠ ⊤)
    (hchild : ∀ x, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x j ≤ 73)
    (herr : ∀ x, measureHellinger (kepPoissonLayerMeasure hf eps n x j) (kepReferenceLaw eps j) ≤ r)
    (hpos : ∀ᵐ z ∂(kepReferenceLaw eps j : Measure ℝ), 0 ≤ z)
    (hmean : ∫ z, z ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 1)
    (href : Integrable (fun z => Real.exp (theta * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
      ∫ z, Real.exp (theta * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 73)
    (hrefScale : Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z)) (kepReferenceLaw eps j : Measure ℝ) ∧
      ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂(kepReferenceLaw eps j : Measure ℝ) ≤ 73)
    (hstep : ∀ x S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S)
      (kepReferenceLaw eps j : Measure ℝ) ≤ r + b * |S| ^ (2 / 3 : ℝ))
    (hQwindow : (iidLaw (kepReferenceLaw eps j)).real {g | (M : ℕ∞) < gapSegLen eps g} ≤ 1 / 16)
    (hQtail : ∀ k, (iidLaw (kepReferenceLaw eps j)).real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ (1 / 2 : ℝ) ^ k)
    (herrorWindow : (2 * A + 4 * (A + (2 / (theta / (fhi / flo)) ^ 2 * 73) * A ^ 3) + 1) *
      (eps * r + eps ^ 3 * b) ≤ 1 / 4)
    (herrorMean : r * Real.sqrt (8 * 73 / theta ^ 2) ≤ 1)
    (hC : 0 < lawC eps (kepReferenceLaw eps j))
    (hsmall : 2 * theta / lawC eps (kepReferenceLaw eps j) ≤ (theta / (fhi / flo)) / 2)
    (hcost : 8 * 73 / (theta / (fhi / flo)) ^ 2 *
      (2 * theta / lawC eps (kepReferenceLaw eps j)) ≤ fhi / flo)
    (hscale : (3 * (fhi / flo) * (2 * theta / lawC eps (kepReferenceLaw eps j))) * M ≤ 1 / 144) :
    (∀ x, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x (j + 1) 1 g ≠ ⊤) ∧
    (∀ x, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x (j + 1)) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x (j + 1) ≤ 73) ∧
    (∀ x, measureHellinger (kepPoissonLayerMeasure hf eps n x (j + 1)) (kepReferenceLaw eps (j + 1)) ≤
      (4 * A + 8 * (A +
        (Real.sqrt (24 / (theta / (fhi / flo)) ^ 4 * 73) / (1 - Real.sqrt (1 / 2)) ^ 3) * A ^ 3) + 1) *
          (eps * r + eps ^ 3 * b)) ∧
    ∀ x k, expSeqMeasure.real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤ (1 / 2 : ℝ) ^ k := by
  have hwindow (x : ℝ) : expSeqMeasure
      {g | (M : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤ ENNReal.ofReal (1 / 2) := by
    have hfinite := kepPoissonPivot_all_finite_of_leading hf eps n j hfin x M
    have hfiniteError := kepPoisson_finite_comparison_window_budget hf hn htheta
      (by norm_num : (0 : ℝ) ≤ 73) hr hb hA heps (kepReferenceLaw eps j) x j M hM hm hfin
        hchild hpos hrefScale.1 hrefScale.2 (hstep x)
    have hH := hfiniteError.trans herrorWindow
    have h := kepPoisson_window_probability_of_prefix_error hf (kepReferenceLaw eps j) x j M hfinite
      (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (pow_le_pow_left₀ (measureHellinger_nonneg _ _) hH 2)
      (by norm_num at hQwindow ⊢; exact hQwindow)
    rw [← ofReal_measureReal]
    apply ENNReal.ofReal_le_ofReal
    norm_num at h
    linarith
  have htail (x : ℝ) (k : ℕ) : expSeqMeasure.real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤
        (1 / 2 : ℝ) ^ k := by
    have h := kepPoissonLayerSequence_geometric_tail hf hn.ne' j M hm.ne' hfin hwindow x k
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)] at h
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) h
  have hmu := kepPoisson_mean_le_two_of_comparison hf hn htheta j hm.le hchild hpos
    href.1 href.2 hmean herr herrorMean
  refine ⟨kepPoissonPivot_parent_finite_of_window hf hn j M hm hfin (by norm_num) hwindow,
    ?_, ?_, htail⟩
  · intro x
    exact kepPoisson_parent_exponential_moment hf hn htheta x j hclass hm hfin hmu hchild
      hC hsmall hcost hM1 hscale (htail x)
  · intro x
    exact kepPoisson_parent_comparison_window_budget hf hn htheta
      (by norm_num : (0 : ℝ) ≤ 73) hr hb hA heps x j M hM1 hM hclass hm hfin
        hchild hpos hrefScale.1 hrefScale.2 (hstep x) (htail x) hQtail

end

end PGM
