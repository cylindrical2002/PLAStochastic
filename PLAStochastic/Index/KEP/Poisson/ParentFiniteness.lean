import PLAStochastic.Index.KEP.Poisson.GeometricTail
import PLAStochastic.Index.KEP.CompletedParentFiniteness

/-!
# Paying actual parent completion and original segment finiteness

The geometric stopping tail is established while only child completions are
known finite. A finite original stopping prefix completes the leading parent
pivot; fresh-state restarts then complete all parent pivots and every original
child segment.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem kepPoissonPivot_parent_leading_finite {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (j : ℕ)
    (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hstop : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure,
      gapSegLen eps (kepPoissonLayerSequence hf eps n y j g) ≠ ⊤) :
    ∀ x : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x (j + 1) 1 g ≠ ⊤ := by
  intro x
  filter_upwards [hstop x, ae_all_iff.mpr (kepPoissonPivot_all_finite_of_leading hf eps n j hfin x)]
    with g hg hgg
  apply completedPivot_parent_finite_of_child_stop (fun _ => rfl) j
  · rwa [← kepPoissonLayerSequence_stop_eq hf hn x j hm]
  · exact hgg

theorem kepPoisson_original_child_segments_finite {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (heps : 0 ≤ eps) (hn : 0 < n) (j : ℕ)
    (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hstop : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure,
      gapSegLen eps (kepPoissonLayerSequence hf eps n y j g) ≠ ⊤) (x : ℝ) :
    ∀ᵐ g ∂expSeqMeasure, AllSegmentsFinite eps (pairLayer eps j (kepPoissonPairs hf n x g)) := by
  have hp := kepPoissonPivot_parent_leading_finite hf hn j hm hfin hstop
  filter_upwards [ae_all_iff.mpr (kepPoissonPivot_all_finite_of_leading hf eps n (j + 1) hp x)]
    with g hg
  exact allSegmentsFinite_of_completedPivot_finite heps (fun _ => rfl) j hg

theorem kepPoissonPivot_parent_finite_of_window {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (j M : ℕ)
    (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    {q : ℝ≥0∞} (hq : q < 1)
    (hwindow : ∀ y : ℝ, expSeqMeasure
      {g | (M : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n y j g)} ≤ q) :
    ∀ x : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x (j + 1) 1 g ≠ ⊤ :=
  kepPoissonPivot_parent_leading_finite hf hn j hm hfin
    (kepPoissonLayerSequence_ae_stop_finite hf hn.ne' j M hm.ne' hfin hq hwindow)

end

end PGM
