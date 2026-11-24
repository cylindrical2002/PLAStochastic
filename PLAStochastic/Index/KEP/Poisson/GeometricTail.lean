import PLAStochastic.Index.KEP.Poisson.LayerSequenceRestart
import PLAStochastic.ForMathlib.Probability.Kernel.FiberEventBudget

/-!
# A geometric tail for the original nonhomogeneous Poisson parent segment

Only the child's completed restarts are assumed finite. A uniform finite
window failure probability at all physical anchors is conditioned at the
actual child pivot. Surviving long segments contain surviving next windows,
which gives the geometric tail without assuming parent finiteness.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem kepPoissonLayerSequence_tail_step {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : n ≠ 0) (j M : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    {q : ℝ≥0∞}
    (hwindow : ∀ y : ℝ, expSeqMeasure
      {g | (M : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n y j g)} ≤ q)
    (x : ℝ) (i : ℕ) :
    expSeqMeasure {g | ((i + M : ℕ) : ℕ∞) <
        gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤
      q * expSeqMeasure {g | (i : ℕ∞) <
        gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} := by
  let R := kepPoissonPrefixState hf eps n x j i
  let tau := kepPoissonPivot hf eps n x j i
  let mu := expSeqMeasure.map R
  let s : Set (ℕ → ℝ) := {r | (i : ℕ∞) < gapSegLen eps r}
  let t : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
    {p | (M : ℕ∞) < gapSegLen eps
      (kepPoissonLayerSequence hf eps n (kepPoissonParentAnchor hf eps n x j (gapKeys p.1 i)) j p.2)}
  have hRi : Measurable R := measurable_kepPoissonPrefixState hf eps n x j i
  have htau := isStoppingRule_kepPoissonPivot hf eps n x j i
  have hfinite := kepPoissonPivot_all_finite_of_leading hf eps n j hfin x i
  have hs : MeasurableSet s := (isStoppingRule_gapSegLen eps).measurableSet_lt i
  have ht : MeasurableSet t := by
    have hanchor : Measurable (fun p : (ℕ → ℝ) × (ℕ → ℝ) =>
        kepPoissonParentAnchor hf eps n x j (gapKeys p.1 i)) :=
      (measurable_kepPoissonParentAnchor hf eps n x j).comp
        (((measurable_pi_apply i).comp measurable_gapKeys).comp measurable_fst)
    exact ((isStoppingRule_gapSegLen eps).measurableSet_lt M).preimage
      ((measurable_kepPoissonLayerSequence hf eps n j).comp
        (hanchor.prodMk measurable_snd))
  have hstate :
      mu s = expSeqMeasure {g | (i : ℕ∞) <
        gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} := by
    rw [Measure.map_apply hRi hs]
    apply measure_congr
    filter_upwards [hfinite] with g hg
    exact propext (mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps i)
      (kepPoissonPrefixState_agree_layerSequence hf hg))
  have hsub : ∀ᵐ g ∂expSeqMeasure,
      g ∈ {g | ((i + M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} →
        g ∈ (fun g => (R g, shiftBy tau g)) ⁻¹' ((s ×ˢ univ) ∩ t) := by
    filter_upwards [hfinite] with g hg
    intro h
    simp only [s, t, mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true, mem_ofPred_eq]
    refine ⟨?_, ?_⟩
    · exact (mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps i)
        (kepPoissonPrefixState_agree_layerSequence hf hg)).mpr
        ((ENat.natCast_le_natCast.mpr (Nat.le_add_right i M)).trans_lt h)
    · rw [kepPoissonPrefixState_parentAnchor hf (x := x) hn j i hm]
      exact kepPoissonLayerSequence_survival_restart hf hg h
  calc
    _ ≤ expSeqMeasure ((fun g => (R g, shiftBy tau g)) ⁻¹' ((s ×ˢ univ) ∩ t)) :=
      measure_mono_ae hsub
    _ = (mu.prod expSeqMeasure) ((s ×ˢ univ) ∩ t) := by
      rw [← kepPoissonPrefixState_restart_joint hf eps n x j i hfinite,
        Measure.map_apply (hRi.prodMk (measurable_shiftBy htau))
          ((hs.prod MeasurableSet.univ).inter ht)]
    _ ≤ q * mu s := measure_prod_fiber_event_le mu expSeqMeasure hs ht
      (fun r _ => hwindow (kepPoissonParentAnchor hf eps n x j (gapKeys r i)))
    _ = _ := by rw [hstate]

theorem kepPoissonLayerSequence_geometric_tail {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : n ≠ 0) (j M : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    {q : ℝ≥0∞}
    (hwindow : ∀ y : ℝ, expSeqMeasure
      {g | (M : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n y j g)} ≤ q)
    (x : ℝ) (k : ℕ) :
    expSeqMeasure {g | ((k * M : ℕ) : ℕ∞) <
      gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤ q ^ k := by
  induction k with
  | zero =>
    simp only [zero_mul, pow_zero]
    exact prob_le_one
  | succ k hk =>
    rw [Nat.succ_mul]
    exact (kepPoissonLayerSequence_tail_step hf hn j M hm hfin hwindow x (k * M)).trans
      (by simpa only [pow_succ, mul_comm] using mul_le_mul_right hk q)

theorem kepPoissonLayerSequence_ae_stop_finite {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : n ≠ 0) (j M : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    {q : ℝ≥0∞} (hq : q < 1)
    (hwindow : ∀ y : ℝ, expSeqMeasure
      {g | (M : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n y j g)} ≤ q)
    (x : ℝ) :
    ∀ᵐ g ∂expSeqMeasure, gapSegLen eps (kepPoissonLayerSequence hf eps n x j g) ≠ ⊤ := by
  have hbad (k : ℕ) : expSeqMeasure
      {g | gapSegLen eps (kepPoissonLayerSequence hf eps n x j g) = ⊤} ≤ q ^ k := by
    apply (measure_mono _).trans (kepPoissonLayerSequence_geometric_tail hf hn j M hm hfin hwindow x k)
    intro g hg
    change ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)
    rw [hg]
    exact ENat.natCast_lt_top _
  have hzero : expSeqMeasure
      {g | gapSegLen eps (kepPoissonLayerSequence hf eps n x j g) = ⊤} = 0 :=
    le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq) hbad) zero_le
  rw [ae_iff]
  simpa only [not_ne_iff] using hzero

end

end PGM
