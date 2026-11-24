import PLAStochastic.Index.KEP.StoppedStateBudgets
import PLAStochastic.Index.KEP.StoppedPathComparison

/-!
# A paid full stopped-path comparison for the actual Poisson child layer

The path is the original physical child sequence. Its proved absorbing
kernel law, conditional exponential budget, and actual stopping tail pay
every finite chain. The common stopped-path map then removes truncation.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

instance isProbabilityMeasure_map_kepPoissonLayerSequence {f : ℝ → ℝ}
    {flo fhi L : ℝ} (hf : KepIntensityProfile f flo fhi L)
    (eps n x : ℝ) (j : ℕ) :
    IsProbabilityMeasure (expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j)) :=
  Measure.isProbabilityMeasure_map (measurable_kepPoissonLayerSequence_anchor hf eps n x j).aemeasurable

theorem gapPathMap_power_budget {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℕ → ℝ} (hX : Measurable X) (N p : ℕ)
    (hi : Integrable (fun w => gapKeys (X w) N ^ p) P) {C : ℝ}
    (hbudget : ∫ w, gapKeys (X w) N ^ p ∂P ≤ C) :
    Integrable (fun g => gapKeys g N ^ p) (P.map X) ∧
      ∫ g, gapKeys g N ^ p ∂P.map X ≤ C := by
  have hF : Measurable (fun g : ℕ → ℝ => gapKeys g N ^ p) :=
    ((measurable_pi_apply N).comp measurable_gapKeys).pow_const p
  exact ⟨(integrable_map_measure hF.aestronglyMeasurable hX.aemeasurable).mpr hi,
    (by rw [integral_map hX.aemeasurable hF.aestronglyMeasurable]; exact hbudget)⟩

theorem kepPoisson_stopped_path_comparison {f : ℝ → ℝ}
    {flo fhi L eps n theta B r b q : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hb : 0 ≤ b) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (nu : ProbabilityMeasure ℝ) (x : ℝ) (j M : ℕ) (hM : 1 ≤ M)
    (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (hpos : ∀ᵐ z ∂(nu : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z)) (nu : Measure ℝ))
    (hmgf : ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂(nu : Measure ℝ) ≤ B)
    (hstep : ∀ S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S)
      (nu : Measure ℝ) ≤ r + b * |S| ^ (2 / 3 : ℝ))
    (hPtail : ∀ k, expSeqMeasure.real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤ q ^ k)
    (hQtail : ∀ k, (iidLaw nu).real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ q ^ k) :
    measureHellinger
      ((expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j)).map (kepStoppedGapPath eps))
      ((iidLaw nu).map (kepStoppedGapPath eps)) ^ 2 ≤
        2 * r ^ 2 * ((M : ℝ) / (1 - q)) +
          4 * b ^ 2 * ((M : ℝ) / (1 - q) +
            Real.sqrt (24 / (theta / (fhi / flo)) ^ 4 * B) *
              (2 / (1 - Real.sqrt q) ^ 3 * (M : ℝ) ^ 3)) := by
  let P := expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j)
  let Q := iidLaw nu
  let C := 24 / (theta / (fhi / flo)) ^ 4 * B
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have ht : 0 < theta / (fhi / flo) := div_pos htheta (div_pos hf.fhi_pos hf.pos)
  have hseq := measurable_kepPoissonLayerSequence_anchor hf eps n x j
  have hPpos : ∀ᵐ g ∂P, ∀ i, 0 ≤ g i := by
    have hs : MeasurableSet {g : ℕ → ℝ | ∀ i, 0 ≤ g i} := by
      simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le (measurable_const (a := (0 : ℝ))) (measurable_pi_apply i)
    apply (ae_map_iff hseq.aemeasurable hs).mpr
    filter_upwards [ae_all_iff.mpr fun a =>
      iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) a] with g hg
    exact kepPoissonLayerSequence_nonneg hf hn x j hm.le (fun a => (hg a).le)
  have hQpos : ∀ᵐ g ∂Q, ∀ i, 0 ≤ g i := ae_all_iff.mpr fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (nu : Measure ℝ)) i).quasiMeasurePreserving.ae hpos
  have hPm (i k : ℕ) := gapPathMap_power_budget expSeqMeasure hseq i (k + 1)
    (kepPoissonLayerSequence_power_budget hf hn htheta hB x j i k hm hfin hchild).1
    (kepPoissonLayerSequence_power_budget hf hn htheta hB x j i k hm hfin hchild).2
  have hQm (i k : ℕ) := iid_gapKeys_power_budget nu ht hpos hi hmgf i k
  have hPi2 (i : ℕ) : Integrable (fun g => gapKeys g i ^ 2) P := (hPm i 1).1
  have hQi2 (i : ℕ) : Integrable (fun g => gapKeys g i ^ 2) Q := (hQm i 1).1
  have hPi4 (i : ℕ) : Integrable (fun g => gapKeys g i ^ 4) P := (hPm i 3).1
  have hQi4 (i : ℕ) : Integrable (fun g => gapKeys g i ^ 4) Q := (hQm i 3).1
  have hPm4 (i : ℕ) : ∫ g, gapKeys g i ^ 4 ∂P ≤ C * (i : ℝ) ^ 4 := by
    have h := (hPm i 3).2
    norm_num at h
    simpa only [C, mul_comm] using h
  have hQm4 (i : ℕ) : ∫ g, gapKeys g i ^ 4 ∂Q ≤ C * (i : ℝ) ^ 4 := by
    have h := (hQm i 3).2
    norm_num at h
    simpa only [C, mul_comm] using h
  have hPlaw (i : ℕ) : kernelIterateLaw (kepPoissonStoppedPrefixKernel hf eps n x j)
      (Measure.dirac (fun _ => 0)) i = P.map (kepStoppedPrefix eps i) := by
    rw [Measure.map_map (measurable_kepStoppedPrefix eps i) hseq]
    exact (kepPoisson_stopped_sequence_state_law hf hn.ne' x j i hm.ne' hfin).symm
  have hQlaw (i : ℕ) : kernelIterateLaw (kepReferenceStoppedPrefixKernel nu eps)
      (Measure.dirac (fun _ => 0)) i = Q.map (kepStoppedPrefix eps i) :=
    (iid_kepStoppedPrefix_law nu eps i).symm
  have hPtail' (k : ℕ) : P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ q ^ k := by
    rw [map_measureReal_apply hseq ((isStoppingRule_gapSegLen eps).measurableSet_lt (k * M))]
    exact hPtail k
  have hc (i : ℕ) (g : ℕ → ℝ) :
      measureHellinger (kepPoissonStoppedPrefixKernel hf eps n x j i g)
        (kepReferenceStoppedPrefixKernel nu eps i g) ≤
      {g | (i : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => r + b * |gapKeys g i| ^ (2 / 3 : ℝ)) g := by
    have hgap : measureHellinger (kepPoissonPrefixGapKernel hf eps n x j i g)
        (Kernel.const (ℕ → ℝ) (nu : Measure ℝ) g) ≤
          r + b * |gapKeys g i| ^ (2 / 3 : ℝ) := by
      simpa only [kepPoissonPrefixGapKernel, Kernel.comap_apply, Kernel.const_apply] using hstep (gapKeys g i)
    have h := measureHellinger_absorbingSequenceKernel
      {g | (i : ℕ∞) < gapSegLen eps g} ((isStoppingRule_gapSegLen eps).measurableSet_lt i)
      (kepPoissonPrefixGapKernel hf eps n x j i) (Kernel.const (ℕ → ℝ) (nu : Measure ℝ)) i g
    apply h.trans
    by_cases hg : (i : ℕ∞) < gapSegLen eps g
    · simpa only [indicator_apply, mem_ofPred_eq, if_pos hg] using hgap
    · simp only [indicator_apply, mem_ofPred_eq, if_neg hg, le_refl]
  have hbudget : 0 ≤ 2 * r ^ 2 * ((M : ℝ) / (1 - q)) +
      4 * b ^ 2 * ((M : ℝ) / (1 - q) +
        Real.sqrt C * (2 / (1 - Real.sqrt q) ^ 3 * (M : ℝ) ^ 3)) := by
    have hden := sub_pos.mpr hq1
    have hden' : 0 < 1 - Real.sqrt q :=
      sub_pos.mpr ((Real.sqrt_lt' one_pos).mpr (by simpa using hq1))
    positivity
  apply measureHellinger_stopped_paths_of_prefix_bound P Q eps M hbudget hq0 hq1
      (hPtail := hPtail') (hQtail := hQtail)
  intro N
  have h := measureHellinger_absorbing_prefixes_of_path_budgets P Q hPpos hQpos eps M hM
    (kepPoissonStoppedPrefixKernel hf eps n x j) (kepReferenceStoppedPrefixKernel nu eps)
    hPlaw hQlaw hr hb hq0 hq1 hC hPi2 hQi2 hPi4 hQi4 hPm4 hQm4 hPtail' hQtail hc N
  simpa only [hPlaw, hQlaw] using h

end

end PGM
