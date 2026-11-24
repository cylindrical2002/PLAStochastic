import PLAStochastic.Index.KEP.Poisson.StateMoments
import PLAStochastic.Index.KEP.IIDPathMoments
import PLAStochastic.ForMathlib.Probability.Hellinger.IntegerStateBudget

/-!
# A finite prefix comparison for the actual Poisson child process

The proved physical state law and the canonical iid reference law are
compared through their actual coordinate kernels. A fixed conditional
exponential moment pays all cumulative second moments, without independence
of the physical increments.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

instance isProbabilityMeasure_kepPoissonPrefixState_map {f : ℝ → ℝ}
    {flo fhi L : ℝ} (hf : KepIntensityProfile f flo fhi L)
    (eps n x : ℝ) (j N : ℕ) :
    IsProbabilityMeasure (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N)) :=
  Measure.isProbabilityMeasure_map (measurable_kepPoissonPrefixState hf eps n x j N).aemeasurable

instance isProbabilityMeasure_kepGapPrefix_map (nu : ProbabilityMeasure ℝ) (N : ℕ) :
    IsProbabilityMeasure ((iidLaw nu).map (kepGapPrefix N)) :=
  Measure.isProbabilityMeasure_map (measurable_kepGapPrefix N).aemeasurable

theorem kepPoisson_finite_prefix_comparison {f : ℝ → ℝ}
    {flo fhi L eps n theta B r b : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hb : 0 ≤ b)
    (nu : ProbabilityMeasure ℝ) (x : ℝ) (j N : ℕ)
    (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (hpos : ∀ᵐ z ∂(nu : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp ((theta / (fhi / flo)) * z)) (nu : Measure ℝ))
    (hmgf : ∫ z, Real.exp ((theta / (fhi / flo)) * z) ∂(nu : Measure ℝ) ≤ B)
    (hstep : ∀ S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S)
      (nu : Measure ℝ) ≤ r + b * |S| ^ (2 / 3 : ℝ)) :
    measureHellinger (expSeqMeasure.map (kepPoissonPrefixState hf eps n x j N))
      ((iidLaw nu).map (kepGapPrefix N)) ^ 2 ≤
        2 * (N : ℝ) * r ^ 2 + 4 * b ^ 2 *
          ((N : ℝ) + (2 / (theta / (fhi / flo)) ^ 2 * B) * (N : ℝ) ^ 3) := by
  let K := 2 / (theta / (fhi / flo)) ^ 2 * B
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ht : 0 < theta / (fhi / flo) := div_pos htheta (div_pos hf.fhi_pos hf.pos)
  have hP (i : ℕ) := kepPoisson_prefix_state_power_budget hf hn htheta hB x j i 1 hm hfin hchild
  have hQ (i : ℕ) := iid_prefix_state_power_budget nu ht hpos hi hmgf i 1
  have hp (i : ℕ) : ∫ g, gapKeys g i ^ 2
      ∂kernelIterateLaw (kepPoissonPrefixKernel hf eps n x j) (Measure.dirac (fun _ => 0)) i ≤
        K * (i : ℝ) ^ 2 := by
    simpa only [K, Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat, mul_comm] using (hP i).2
  have hq (i : ℕ) : ∫ g, gapKeys g i ^ 2
      ∂kernelIterateLaw (kepReferencePrefixKernel nu) (Measure.dirac (fun _ => 0)) i ≤
        K * (i : ℝ) ^ 2 := by
    simpa only [K, Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat, mul_comm] using (hQ i).2
  have hc (i : ℕ) (g : ℕ → ℝ) :
      measureHellinger (kepPoissonPrefixKernel hf eps n x j i g)
        (kepReferencePrefixKernel nu i g) ≤ r + b * |gapKeys g i| ^ (2 / 3 : ℝ) := by
    have hs : measureHellinger (kepPoissonPrefixGapKernel hf eps n x j i g)
        (Kernel.const (ℕ → ℝ) (nu : Measure ℝ) g) ≤
        r + b * |gapKeys g i| ^ (2 / 3 : ℝ) := by
      simpa only [kepPoissonPrefixGapKernel, Kernel.comap_apply, Kernel.const_apply] using
        hstep (gapKeys g i)
    exact (measureHellinger_sequenceUpdateKernel (kepPoissonPrefixGapKernel hf eps n x j i)
      (Kernel.const (ℕ → ℝ) (nu : Measure ℝ)) i g).trans hs
  have h := measureHellinger_kernelIterate_integer_state_budget
    (Measure.dirac (fun _ : ℕ => (0 : ℝ)))
    (kepPoissonPrefixKernel hf eps n x j) (kepReferencePrefixKernel nu)
    (fun i g => gapKeys g i) hr hb hK (by norm_num : 0 ≤ (2 / 3 : ℝ)) (by norm_num)
    (fun i => (hP i).1) (fun i => (hQ i).1) hp hq hc N
  simpa only [kepPoissonPrefixState_law hf hn.ne' j hm.ne' hfin x N,
    iid_kepGapPrefix_law, K] using h

end

end PGM
