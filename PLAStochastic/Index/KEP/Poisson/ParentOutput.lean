import PLAStochastic.Index.KEP.Poisson.StoppedComparison
import PLAStochastic.Index.KEP.StoppedOutput

/-!
# The original Poisson parent output with the exact reference normalization

The expected reference span grows by the actual reference compression
factor. Hence the original parent gap is precisely the same normalized
stopped-sum readout as the true next reference law.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepReferenceSpan_succ_mul_lawC {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) (j : ℕ) :
    kepReferenceSpan eps (j + 1) =
      kepReferenceSpan eps j * lawC eps (kepReferenceLaw eps j) := by
  rw [kepReference_lawC_eq_segMean heps j]
  have he := (le_max_right _ _).trans heps
  have hall := layerOK_all (layerOK_input gapLaw_expCoord) (bAbs_le_bIn 1 1)
    (βAbs_le_βIn _ _) (vIn_pos one_pos one_pos) (vIn_le 1 1) KcAbs_le_KcIn he
  exact (hall j).2.2.1

theorem kepPoissonLayerMeasure_parent_output {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (heps : kepReferenceClassicalThreshold ≤ eps) (hm : 0 < kepReferenceSpan eps j) :
    kepPoissonLayerMeasure hf eps n x (j + 1) =
      (expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j)).map
        (fun g => stopSum eps g / lawC eps (kepReferenceLaw eps j)) := by
  have hseq := measurable_kepPoissonLayerSequence_anchor hf eps n x j
  have hF : Measurable (fun g => stopSum eps g / lawC eps (kepReferenceLaw eps j)) :=
    (measurable_stopSum eps).div_const _
  rw [Measure.map_map hF hseq]
  unfold kepPoissonLayerMeasure
  congr 1
  funext g
  rw [kepPoissonLayerGap_succ_stopSum hf hn x j hm g,
    kepReferenceSpan_succ_mul_lawC heps j]
  change (kepReferenceSpan eps j / (kepReferenceSpan eps j * lawC eps (kepReferenceLaw eps j))) *
      stopSum eps (kepPoissonLayerSequence hf eps n x j g) =
        stopSum eps (kepPoissonLayerSequence hf eps n x j g) / lawC eps (kepReferenceLaw eps j)
  field_simp [hm.ne']

theorem kepPoisson_parent_output_comparison_le {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (x : ℝ) (j : ℕ)
    (heps : kepReferenceClassicalThreshold ≤ eps) (hm : 0 < kepReferenceSpan eps j) :
    measureHellinger (kepPoissonLayerMeasure hf eps n x (j + 1)) (kepReferenceLaw eps (j + 1)) ≤
      measureHellinger
        ((expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j)).map (kepStoppedGapPath eps))
        ((iidLaw (kepReferenceLaw eps j)).map (kepStoppedGapPath eps)) := by
  have h := measureHellinger_stopped_output_le
    (expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j))
    (iidLaw (kepReferenceLaw eps j)) eps (lawC eps (kepReferenceLaw eps j))
  have href : (kepReferenceLaw eps (j + 1) : Measure ℝ) =
      (iidLaw (kepReferenceLaw eps j)).map
        (fun g => stopSum eps g / lawC eps (kepReferenceLaw eps j)) := by
    rw [kepReferenceLaw_succ]
    rfl
  simpa only [kepPoissonLayerMeasure_parent_output hf hn x j heps hm,
    href] using h

end

end PGM
