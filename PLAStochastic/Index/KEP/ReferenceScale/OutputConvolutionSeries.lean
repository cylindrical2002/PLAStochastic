import PLAStochastic.Index.KEP.ReferenceScale.OutputTelescoping
import PLAStochastic.Index.KEP.ReferenceScale.PrefixConvolution

/-!
# The exact actual-output series in surviving and stopped convolution prefixes

This identifies the free cutoff, surviving long correction, and finite stopped
correction of the true next reference law. No stopping-time or Fubini premises
remain. Differentiated facet graph budgets are a separate required step.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

def kepReferenceSurvivingIncrement (eps : ℝ) (j : ℕ) (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ g in {g | (k : ℕ∞) < gapSegLen eps g},
    kepPrefixConvolutionIncrement (kepReferenceLaw eps j) (lawC eps (kepReferenceLaw eps j)) φ k g
    ∂iidLaw (kepReferenceLaw eps j)

def kepReferenceStoppedIncrement (eps : ℝ) (j : ℕ) (φ : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ g in {g | gapSegLen eps g ≤ (k : ℕ∞)},
    kepPrefixConvolutionIncrement (kepReferenceLaw eps j) (lawC eps (kepReferenceLaw eps j)) φ k g
    ∂iidLaw (kepReferenceLaw eps j)

theorem kepReference_output_convolution_series :
    ∃ eps0 : ℝ, ∀ eps, eps0 ≤ eps → ∀ j : ℕ,
      ∀ φ : ℝ → ℝ, Measurable φ → ∀ B : ℝ, 0 ≤ B → (∀ x, |φ x| ≤ B) → ∀ M : ℕ,
        Summable (fun k : ℕ => kepReferenceSurvivingIncrement eps j φ (k + M)) ∧
        (∫ x, φ x ∂(kepReferenceLaw eps (j + 1) : Measure ℝ)) =
          (∫ g, φ (gapKeys g M / lawC eps (kepReferenceLaw eps j))
            ∂iidLaw (kepReferenceLaw eps j)) +
          (∑' k : ℕ, kepReferenceSurvivingIncrement eps j φ (k + M)) -
          ∑ k ∈ range M, kepReferenceStoppedIncrement eps j φ k := by
  obtain ⟨eps0, houtput⟩ := kepReference_output_cutoff_telescoping
  refine ⟨eps0, ?_⟩
  intro eps he j φ hφ B hB hb M
  obtain ⟨hfin, hs, hidentity⟩ := houtput eps he j φ hφ B hB hb M
  let ν := kepReferenceLaw eps j
  let C := lawC eps ν
  have hsurv (k : ℕ) : (∫ g, kepReferenceOutputIncrement eps j φ k g ∂iidLaw ν) =
      kepReferenceSurvivingIncrement eps j φ k := by
    change _ = ∫ g in {g | (k : ℕ∞) < gapSegLen eps g},
      kepPrefixConvolutionIncrement ν C φ k g ∂iidLaw ν
    rw [← integral_surviving_prefix_convolution_increment eps ν hφ hB hb C k,
      ← integral_indicator (measurableSet_lt_gapSegLen eps k)]
    apply integral_congr_ae
    filter_upwards [hfin] with g hg
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg
    have hT : gapSegLen eps g = n := hn.symm
    simp only [kepReferenceOutputIncrement, stoppedIncrement, hT, ENat.toNat_natCast,
      indicator_apply, mem_ofPred_eq, Nat.cast_lt]
    rfl
  have hstop (k : ℕ) :
      (∫ g, (if (gapSegLen eps g).toNat ≤ k then
        φ (gapKeys g (k + 1) / C) - φ (gapKeys g k / C) else 0) ∂iidLaw ν) =
      kepReferenceStoppedIncrement eps j φ k := by
    have hm : MeasurableSet {g : ℕ → ℝ | gapSegLen eps g ≤ (k : ℕ∞)} := by
      convert (measurableSet_lt_gapSegLen eps k).compl using 1
      ext g
      simp only [mem_compl_iff, mem_ofPred_eq, not_lt]
    change _ = ∫ g in {g | gapSegLen eps g ≤ (k : ℕ∞)},
      kepPrefixConvolutionIncrement ν C φ k g ∂iidLaw ν
    rw [← integral_stopped_prefix_convolution_increment eps ν hφ hB hb C k,
      ← integral_indicator hm]
    apply integral_congr_ae
    filter_upwards [hfin] with g hg
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hg
    have hT : gapSegLen eps g = n := hn.symm
    simp only [hT, ENat.toNat_natCast, indicator_apply, mem_ofPred_eq, Nat.cast_le]
  dsimp only [C, ν] at hsurv hstop
  simp_rw [hsurv] at hs hidentity
  simp_rw [hstop] at hidentity
  exact ⟨hs, hidentity⟩

end

end PGM
