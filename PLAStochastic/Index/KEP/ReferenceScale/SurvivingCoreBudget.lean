import PLAStochastic.Index.KEP.ReferenceScale.CertificateLengthSummation

/-!
# The original actual surviving-core series is paid unconditionally

The graph length budget is read back on the original certificate pairs and
prefix sums. Tests may vary with the actual prefix length. The complementary
short-bridge and cutoff terms remain the separate rare remainder.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_surviving_core_series_budget :
    ∃ theta c K eps0 : ℝ, 0 < theta ∧ 0 < c ∧ 0 < K ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ B : ℝ, 0 ≤ B →
        ∀ φ : ℕ → ℝ → ℝ, (∀ k, Continuous (φ k)) →
          (∀ k t, 0 ≤ t → |φ k t| ≤ B * Real.exp (theta * t /
            segMean expSeqMeasure eps (epLayerSeq eps expCoord j))) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let F := fun k : ℕ => |kepSurvivingSecondCore f f' f'' eps
          (kepReferenceGraphBridgeCutoff eps) k (φ k)|
        Summable F ∧ (∑' k : ℕ, F k) ≤
          B * K * eps ^ 43 *
            (1 + Real.sqrt (kepReferenceSecondNorm eps j) +
              Real.exp (-c * eps) * kepReferenceSecondNorm eps j) := by
  obtain ⟨theta, c, K, eps0, ht, hc, hK, he0, hcore⟩ := kepReference_complete_core_graph_series
  refine ⟨theta, c, K, eps0, ht, hc, hK, he0, ?_⟩
  intro eps he heps j hj B hB φ hφ hφb
  dsimp only
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let N := kepGraphLongCutoff eps
  let M := kepReferenceGraphBridgeCutoff eps
  let Φ := fun z : ℕ × ℕ × ℕ => φ (z.1 + z.2.1 + z.2.2 + N + 3)
  let G := fun z : ℕ × ℕ × ℕ =>
    |kepCertificateSecondGraph f f' f'' eps ((z.2.2 + N + 3 : ℕ) - 2 * eps)
      z.1 z.2.1 (z.2.2 + N + 2) (Φ z)|
  let S := fun k : ℕ => ∑ ij ∈ kepLongCertificatePairs eps M k,
    G (ij.1, k - ij.2, ij.2 - ij.1 - M)
  obtain ⟨hsG, hbG⟩ := hcore eps he heps j hj B hB Φ (fun z => hφ _) (fun z => hφb _)
  obtain ⟨hsS, hbS⟩ := kep_certificate_length_series M (fun z => abs_nonneg _) hsG
  have hb (k : ℕ) : |kepSurvivingSecondCore f f' f'' eps M k (φ k)| ≤ S k := by
    have hfilter : kepSurvivingSecondCore f f' f'' eps M k (φ k) =
        ∑ ij ∈ kepLongCertificatePairs eps M k,
          kepCertificateSecondGraph f f' f'' eps ((ij.2 - ij.1 : ℕ) - 2 * eps)
            ij.1 (k - ij.2) (ij.2 - ij.1 - 1) (φ k) := by
      simp only [kepSurvivingSecondCore, kepLongCertificatePairs, Finset.sum_filter]
    rw [hfilter]
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro ij hij
    obtain ⟨hijmem, hM⟩ := Finset.mem_filter.mp hij
    obtain ⟨hijlt, hjk, _⟩ := mem_certPairs.mp hijmem
    have hMdef : M = N + 3 := rfl
    have hL : ij.2 - ij.1 - M + N + 3 = ij.2 - ij.1 := by omega
    have hstep : ij.2 - ij.1 - M + N + 2 = ij.2 - ij.1 - 1 := by omega
    have hprefix : ij.1 + (k - ij.2) + (ij.2 - ij.1 - M) + N + 3 = k := by omega
    dsimp only [G, Φ]
    rw [hL, hstep, hprefix]
  have hsF := hsS.of_nonneg_of_le (fun k => abs_nonneg _) hb
  refine ⟨hsF, ?_⟩
  exact ((hsF.tsum_le_tsum hb hsS).trans hbS).trans hbG

end

end PGM
