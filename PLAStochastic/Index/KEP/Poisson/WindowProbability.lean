import PLAStochastic.Index.KEP.Poisson.FiniteComparison
import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureObservables

/-!
# Transferring the original finite stopping-window probability

The actual original child stopping event is read from its completed prefix.
The iid event is read from its canonical prefix. The square-root event
inequality transfers the proved finite Hellinger error to a window probability.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepPoisson_window_probability_of_prefix_error {f : ℝ → ℝ}
    {flo fhi L eps n : ℝ} (hf : KepIntensityProfile f flo fhi L)
    (nu : ProbabilityMeasure ℝ) (x : ℝ) (j N : ℕ)
    (hfin : ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n x j N g ≠ ⊤)
    {delta eta : ℝ} (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hH : measureHellinger (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N))
      ((iidLaw nu).map (kepGapPrefix N)) ^ 2 ≤ delta ^ 2)
    (hQ : (iidLaw nu).real {g | (N : ℕ∞) < gapSegLen eps g} ≤ eta ^ 2) :
    expSeqMeasure.real
      {g | (N : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤
        (eta + delta) ^ 2 := by
  let s : Set (ℕ → ℝ) := {g | (N : ℕ∞) < gapSegLen eps g}
  have hs : MeasurableSet s := (isStoppingRule_gapSegLen eps).measurableSet_lt N
  have hPevent : (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N)).real s =
      expSeqMeasure.real
        {g | (N : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} := by
    rw [map_measureReal_apply (measurable_kepPoissonPrefixState hf eps n x j N) hs]
    have he : expSeqMeasure (kepPoissonPrefixState hf eps n x j N ⁻¹' s) =
        expSeqMeasure
          {g | (N : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} := by
      apply measure_congr
      filter_upwards [hfin] with g hg
      exact propext (mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps N)
        (kepPoissonPrefixState_agree_layerSequence hf hg))
    exact congrArg ENNReal.toReal he
  have hQevent : ((iidLaw nu).map (kepGapPrefix N)).real s = (iidLaw nu).real s := by
    rw [map_measureReal_apply (measurable_kepGapPrefix N) hs]
    congr 1
    ext g
    exact mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps N)
      (fun _k hk => if_pos hk)
  have h := measureHellinger_sqrt_event
    (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N))
    ((iidLaw nu).map (kepGapPrefix N)) hs
  rw [hPevent, hQevent] at h
  have hH' : measureHellinger (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N))
      ((iidLaw nu).map (kepGapPrefix N)) ≤ delta := by
    nlinarith [measureHellinger_nonneg
      (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N))
      ((iidLaw nu).map (kepGapPrefix N))]
  have hQ' : Real.sqrt ((iidLaw nu).real s) ≤ eta := by
    change (iidLaw nu).real s ≤ eta ^ 2 at hQ
    nlinarith [Real.sq_sqrt (measureReal_nonneg : 0 ≤ (iidLaw nu).real s),
      Real.sqrt_nonneg ((iidLaw nu).real s)]
  have hbound : Real.sqrt (expSeqMeasure.real
      {g | (N : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)}) ≤ eta + delta := by
    have hab := (abs_le.mp h).2
    linarith only [hab, hH', hQ']
  have hsqrt := Real.sq_sqrt (measureReal_nonneg : 0 ≤ expSeqMeasure.real
    {g | (N : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)})
  nlinarith [Real.sqrt_nonneg (expSeqMeasure.real
    {g | (N : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)})]

end

end PGM
