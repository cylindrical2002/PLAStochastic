import PLAStochastic.Index.KEP.StoppedPathComparison
import PLAStochastic.Index.GEP.LayerLaw.ActualLayers

/-!
# The common original normalized stopped-sum readout

The failed-prefix decision is unchanged by zeroing every later gap, including
the extended infinite case. Its original stopped sum is therefore a common
measurable output of the full stopped path, and pays no additional Hellinger cost.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepStoppedGapPath_stop_eq (eps : ℝ) (g : ℕ → ℝ) :
    gapSegLen eps (kepStoppedGapPath eps g) = gapSegLen eps g := by
  by_cases ht : gapSegLen eps g = ⊤
  · have he : kepStoppedGapPath eps g = g := by
      funext k
      simp only [kepStoppedGapPath, ht, ENat.natCast_lt_top, if_true]
    rw [he]
  · obtain ⟨t, ht'⟩ := WithTop.ne_top_iff_exists.mp ht
    have he : gapSegLen eps g = (t : ℕ∞) := ht'.symm
    rw [he]
    apply (mem_iff_of_measurableSet_comap_seqPrefix
      ((isStoppingRule_gapSegLen eps).measurableSet_eq t) _).mpr he
    intro k hk
    simp only [kepStoppedGapPath, he, ENat.natCast_lt_natCast, if_pos hk]

theorem kepStoppedGapPath_stopSum (eps : ℝ) (g : ℕ → ℝ) :
    stopSum eps (kepStoppedGapPath eps g) = stopSum eps g := by
  unfold stopSum
  rw [kepStoppedGapPath_stop_eq]
  apply gapKeys_congr _ _ le_rfl
  intro k hk
  have he : (k : ℕ∞) < gapSegLen eps g :=
    (ENat.natCast_lt_natCast.mpr hk).trans_le (ENat.natCast_toNat_le_self _)
  exact if_pos he

instance isProbabilityMeasure_map_stopSum_div (P : Measure (ℕ → ℝ))
    [IsProbabilityMeasure P] (eps C : ℝ) :
    IsProbabilityMeasure (P.map (fun g => stopSum eps g / C)) :=
  Measure.isProbabilityMeasure_map ((measurable_stopSum eps).div_const C).aemeasurable

theorem map_stoppedPath_stopSum (P : Measure (ℕ → ℝ)) (eps C : ℝ) :
    (P.map (kepStoppedGapPath eps)).map (fun g => stopSum eps g / C) =
      P.map (fun g => stopSum eps g / C) := by
  have hF : Measurable (fun g => stopSum eps g / C) := (measurable_stopSum eps).div_const C
  rw [Measure.map_map hF (measurable_kepStoppedGapPath eps)]
  congr 1
  funext g
  exact congrArg (fun z : ℝ => z / C) (kepStoppedGapPath_stopSum eps g)

theorem measureHellinger_stopped_output_le
    (P Q : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (eps C : ℝ) :
    measureHellinger (P.map (fun g => stopSum eps g / C))
      (Q.map (fun g => stopSum eps g / C)) ≤
        measureHellinger (P.map (kepStoppedGapPath eps)) (Q.map (kepStoppedGapPath eps)) := by
  have hF : Measurable (fun g => stopSum eps g / C) := (measurable_stopSum eps).div_const C
  have h := measureHellinger_map (P.map (kepStoppedGapPath eps)) (Q.map (kepStoppedGapPath eps)) hF
  simpa only [map_stoppedPath_stopSum] using h

end

end PGM
