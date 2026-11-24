import PLAStochastic.Index.GEP.Kernel.Influence.Reward.NonnegativeCut
import PLAStochastic.Index.GEP.Kernel.Output.Identification.BoundaryKernel

/-! # The scalar influence is the constant-test output boundary

The original positive path event is retained. The identity of rewards is used
only at nonnegative physical sums, as required by the original test primitive.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem kernel_testFn_one_nonneg {s : ℝ} (hs : 0 ≤ s) :
    testFn (fun _ => (1 : ℝ)) s = s := by
  rw [testFn, setIntegral_const, Real.volume_real_Ioo_of_le hs, smul_eq_mul, mul_one, sub_zero]

theorem kernel_boundary_reward_one {D θ vlo vhi C s : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hC : 0 < C) (hs : 0 ≤ s) :
    kernelBoundaryReward ν C (fun _ => 1) s = 1/C := by
  unfold kernelBoundaryReward
  have he : (fun x => testFn (fun _ => (1 : ℝ)) ((s+x)/C)-testFn (fun _ => (1 : ℝ)) (s/C))
      =ᵐ[(ν : Measure ℝ)] (fun x => x/C) := by
    filter_upwards [hν.ae_pos] with x hx
    rw [kernel_testFn_one_nonneg (by positivity), kernel_testFn_one_nonneg (by positivity)]
    ring
  rw [integral_congr_ae he, integral_div]
  change lawMean ν/C=1/C
  rw [hν.mean]

theorem kernel_candidate_const_mul (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) (W : (ℕ → ℝ) → ℝ≥0∞)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (x : ℝ) :
    kernelFacetCandidateDensity ν f eps k i q (fun g => c*W g) x =
      c*kernelFacetCandidateDensity ν f eps k i q W x := by
  unfold kernelFacetCandidateDensity
  split_ifs
  · unfold kernelFacetRootDensity kernelLinearDensity kernelIIDRootWeight
    simp_rw [mul_left_comm _ c]
    rw [lintegral_const_mul' c _ hc]
    ac_rfl
  · simp

theorem kernel_IF_oriented_const_mul (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (W : (ℕ → ℝ) → ℝ≥0∞) {c : ℝ≥0∞} (hc : c ≠ ∞) :
    kernelIFOrientedDensity ν f eps k i A (fun g => c*W g) =
      fun x => c*kernelIFOrientedDensity ν f eps k i A W x := by
  funext x
  unfold kernelIFOrientedDensity
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro r
  split_ifs
  · have he : kernelIFActiveWeight eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r)
        (fun g => c*W g) = fun g => c*kernelIFActiveWeight eps k i
          ((Fintype.equivFin (FluxFacetIndex k)).symm r) W g := by
      funext g
      unfold kernelIFActiveWeight kernelIFPathWeight
      rw [indicator_const_mul]
    rw [he]
    exact kernel_candidate_const_mul ν f eps k i _ _ hc x
  · simp

theorem kernel_IF_oriented_const (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    {c : ℝ≥0∞} (hc : c ≠ ∞) :
    kernelIFOrientedDensity ν f eps k i A (fun _ => c) =
      fun x => c*kernelIFOrientedDensity ν f eps k i A (fun _ => 1) x := by
  simpa only [mul_one] using kernel_IF_oriented_const_mul ν f eps k i A (fun _ => 1) hc

theorem kernel_positiveDensity_const_mul {r : ℝ} (hr : 0 ≤ r) (d : ℝ → ℝ≥0∞) (x : ℝ) :
    fluxPositiveDensity (fun x => ENNReal.ofReal r*d x) x = r*fluxPositiveDensity d x := by
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [fluxPositiveDensity, indicator_of_mem hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
  · simp only [fluxPositiveDensity, indicator_of_notMem hx, mul_zero]

theorem kernel_IF_weighted_prefix_const (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) {r : ℝ} (hr : 0 ≤ r) (x : ℝ) :
    kernelIFWeightedPrefixKernel ν f eps k i (fun _ => r) x =
      r*kernelIFPrefixKernel ν f eps k i x := by
  unfold kernelIFWeightedPrefixKernel kernelIFSignedDensity kernelIFPrefixKernel
  simp_rw [kernel_IF_oriented_const ν f eps k i _ ENNReal.ofReal_ne_top]
  simp only [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hr), zero_mul,
    fluxPositiveDensity, ENNReal.toReal_zero]
  by_cases hx : x ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem hx, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr]
    ring
  · simp only [indicator_of_notMem hx, sub_self, mul_zero]

theorem kernel_IF_weighted_prefix_total_congr_nonneg (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (eps : ℝ) (k i : ℕ) {H₁ H₂ : ℝ → ℝ}
    (he : ∀ s, 0 ≤ s → H₁ s = H₂ s) :
    kernelIFWeightedPrefixKernel ν f eps k i (fun g => H₁ (gapKeys g k)) =
      kernelIFWeightedPrefixKernel ν f eps k i (fun g => H₂ (gapKeys g k)) := by
  have hp (A : FluxFacetIndex k → Prop) [DecidablePred A] :=
    kernel_IF_total_oriented_congr_nonneg ν f eps k i A
      (H₁ := fun s => ENNReal.ofReal (H₁ s)) (H₂ := fun s => ENNReal.ofReal (H₂ s))
      (fun s hs => congrArg ENNReal.ofReal (he s hs))
  have hn (A : FluxFacetIndex k → Prop) [DecidablePred A] :=
    kernel_IF_total_oriented_congr_nonneg ν f eps k i A
      (H₁ := fun s => ENNReal.ofReal (-H₁ s)) (H₂ := fun s => ENNReal.ofReal (-H₂ s))
      (fun s hs => congrArg (fun z => ENNReal.ofReal (-z)) (he s hs))
  unfold kernelIFWeightedPrefixKernel kernelIFSignedDensity
  simp_rw [hp, hn]

/-- Exact identification of the actual scalar derivative with the actual
constant-test output boundary. No density choice or a.e. regrouping is needed. -/
theorem output_IF_boundary_one {D θ vlo vhi C : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hC : 0 < C) (f : ℝ → ℝ≥0∞) (eps x : ℝ) :
    outputIFBoundary eps ν f (fun _ => 1) C x = kernelIFInfluence ν f eps x/C := by
  have he (k i : ℕ) : kernelIFWeightedPrefixKernel ν f eps k i
      (fun g => kernelBoundaryReward ν C (fun _ => 1) (gapKeys g k)) =
      kernelIFWeightedPrefixKernel ν f eps k i (fun _ => 1/C) :=
    kernel_IF_weighted_prefix_total_congr_nonneg ν f eps k i
      (H₁ := kernelBoundaryReward ν C (fun _ => 1)) (H₂ := fun _ => 1/C)
      (fun _ hs => kernel_boundary_reward_one hν hC hs)
  unfold outputIFBoundary outputIFTerm
  simp_rw [he, kernel_IF_weighted_prefix_const ν f eps _ _ (by positivity : 0 ≤ 1/C)]
  rw [kernel_IF_real_tsum_triangle (fun k i => 1/C*kernelIFPrefixKernel ν f eps k i x),
    tsum_mul_left]
  unfold kernelIFInfluence
  ring

end
end PGM
