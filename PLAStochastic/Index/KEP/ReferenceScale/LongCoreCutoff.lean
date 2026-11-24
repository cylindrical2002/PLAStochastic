import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphCoreSeries

/-!
# An explicit tolerance-sized cutoff for the actual complete core series

The cutoff has no extra premise: every sufficiently large tolerance satisfies
the kernel cutoff, the polynomial upper bound and a positive certificate span.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepGraphLongCutoff (eps : ℝ) : ℕ := 2 * Nat.ceil eps + 8

def kepReferenceGraphBridgeCutoff (eps : ℝ) : ℕ := kepGraphLongCutoff eps + 3

theorem kepGraphLongCutoff_bounds {eps : ℝ} (heps : 2 ≤ eps) :
    8 ≤ kepGraphLongCutoff eps ∧ eps ≤ (kepGraphLongCutoff eps / 2 : ℕ) ∧
      (kepGraphLongCutoff eps : ℝ) ≤ 7 * eps := by
  have hceil := Nat.le_ceil eps
  have hceilup := (Nat.ceil_lt_add_one (by linarith : 0 ≤ eps)).le
  have hhalf : (2 * Nat.ceil eps + 8) / 2 = Nat.ceil eps + 4 := by omega
  refine ⟨by unfold kepGraphLongCutoff; omega, ?_, ?_⟩
  · unfold kepGraphLongCutoff
    rw [hhalf]
    push_cast
    linarith
  · unfold kepGraphLongCutoff
    push_cast
    linarith

theorem kepReference_complete_core_graph_series :
    ∃ theta c K eps0 : ℝ, 0 < theta ∧ 0 < c ∧ 0 < K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ B : ℝ, 0 ≤ B →
        ∀ φ : (ℕ × ℕ × ℕ) → ℝ → ℝ, (∀ z, Continuous (φ z)) →
          (∀ z t, 0 ≤ t → |φ z t| ≤ B * Real.exp (theta * t /
            segMean expSeqMeasure eps (epLayerSeq eps expCoord j))) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let N := kepGraphLongCutoff eps
        let F := fun z : ℕ × ℕ × ℕ =>
          |kepCertificateSecondGraph f f' f'' eps ((z.2.2 + N + 3 : ℕ) - 2 * eps)
            z.1 z.2.1 (z.2.2 + N + 2) (φ z)|
        Summable F ∧ (∑' z : ℕ × ℕ × ℕ, F z) ≤
          B * K * eps ^ 43 *
            (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
              Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨theta, c, K, eps0, ht, hc, hK, he0, hsum⟩ := kepReference_long_core_graph_series
  refine ⟨theta, c, K, eps0, ht, hc, hK, he0, ?_⟩
  intro eps he heps j hj B hB φ hφ hφb
  have hcut := kepGraphLongCutoff_bounds ((le_max_left _ _).trans heps)
  exact hsum eps he heps j hj (kepGraphLongCutoff eps) hcut.1 hcut.2.1 hcut.2.2 B hB φ hφ hφb

end

end PGM
