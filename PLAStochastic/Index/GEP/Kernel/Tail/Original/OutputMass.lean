import PLAStochastic.Index.GEP.Kernel.Tail.Original.Mass
import PLAStochastic.Index.GEP.Kernel.Influence.Reward.Mass

/-! # Absolute original output-boundary mass before physical block estimates -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_facet_candidate_mono_weight (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) {W V : (ℕ → ℝ) → ℝ≥0∞}
    (hWV : ∀ g, W g ≤ V g) (x : ℝ) :
    kernelFacetCandidateDensity ν f eps k i q W x ≤ kernelFacetCandidateDensity ν f eps k i q V x := by
  unfold kernelFacetCandidateDensity
  split_ifs
  · unfold kernelFacetRootDensity kernelLinearDensity kernelIIDRootWeight
    apply mul_le_mul' le_rfl
    apply lintegral_mono
    intro g
    exact mul_le_mul' le_rfl (hWV _)
  · rfl

theorem kernel_IF_oriented_mono_weight (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    {W V : (ℕ → ℝ) → ℝ≥0∞} (hWV : ∀ g, W g ≤ V g) (x : ℝ) :
    kernelIFOrientedDensity ν f eps k i A W x ≤ kernelIFOrientedDensity ν f eps k i A V x := by
  unfold kernelIFOrientedDensity
  apply ENNReal.tsum_le_tsum
  intro r
  split_ifs
  · apply kernel_facet_candidate_mono_weight
    intro g
    unfold kernelIFActiveWeight kernelIFPathWeight
    by_cases hg : Function.update g i (kernelFacetRoot eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r) g) ∈ kernelIFPathEvent eps k
    · simpa only [indicator_of_mem hg] using hWV _
    · simp only [indicator_of_notMem hg, le_refl]
  · rfl

theorem kernel_IF_signed_enorm_le_abs_mass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (W : (ℕ → ℝ) → ℝ) (x : ℝ) :
    ‖kernelIFSignedDensity ν f eps k i A W x‖ₑ ≤
      2 * kernelIFOrientedDensity ν f eps k i A (fun g => ENNReal.ofReal |W g|) x := by
  unfold kernelIFSignedDensity
  apply enorm_sub_le.trans
  have hp := (kernel_fluxPositiveDensity_enorm_le _ x).trans
    (kernel_IF_oriented_mono_weight ν f eps k i A (fun g => ENNReal.ofReal_le_ofReal (le_abs_self (W g))) x)
  have hn := (kernel_fluxPositiveDensity_enorm_le _ x).trans
    (kernel_IF_oriented_mono_weight ν f eps k i A (fun g => ENNReal.ofReal_le_ofReal (neg_le_abs (W g))) x)
  exact (add_le_add hp hn).trans_eq (two_mul _).symm

theorem kernel_IF_weighted_prefix_enorm_le_abs_mass (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (W : (ℕ → ℝ) → ℝ) (x : ℝ) :
    ‖kernelIFWeightedPrefixKernel ν f eps k i W x‖ₑ ≤
      2 * kernelIFOrientedDensity ν f eps k i (fun _ => True) (fun g => ENNReal.ofReal |W g|) x := by
  unfold kernelIFWeightedPrefixKernel
  apply enorm_sub_le.trans
  calc
    _ ≤ 2 * kernelIFOrientedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) (fun g => ENNReal.ofReal |W g|) x +
        2 * kernelIFOrientedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) (fun g => ENNReal.ofReal |W g|) x :=
      add_le_add (kernel_IF_signed_enorm_le_abs_mass ν f eps k i _ W x)
        (kernel_IF_signed_enorm_le_abs_mass ν f eps k i _ W x)
    _ = 2 * (kernelIFOrientedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) (fun g => ENNReal.ofReal |W g|) x +
        kernelIFOrientedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) (fun g => ENNReal.ofReal |W g|) x) := (mul_add _ _ _).symm
    _ ≤ _ := mul_le_mul' le_rfl (kernel_IF_oriented_signs_le ν f eps k i _ x)

theorem kernel_ennreal_tsum_triangle (F : ℕ → ℕ → ℝ≥0∞) :
    (∑' a : ℕ × ℕ, if a.2 < a.1 then F a.1 a.2 else 0) =
      ∑' b : FluxInfluenceIndex, F b.1 b.2 := by
  rw [ENNReal.tsum_prod']
  change (∑' k : ℕ, ∑' i : ℕ, if i < k then F k i else 0) =
    ∑' b : (Σ k : ℕ, Fin k), (fun k (i : Fin k) => F k i) b.1 b.2
  rw [ENNReal.tsum_sigma (fun k (i : Fin k) => F k i)]
  apply tsum_congr
  intro k
  rw [tsum_fintype (f := fun i : Fin k => F k i), Fin.sum_univ_eq_sum_range]
  rw [tsum_eq_sum (s := Finset.range k) (fun i hi => if_neg (by simpa only [Finset.mem_range] using hi))]
  exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)

/-- The absolute reward remains on the original full path; its physical
factorization is supplied only by the subsequent exact coarea bridge. -/
def kernelOutputAbsMass (eps : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (ψ : ℝ → ℝ) (C x : ℝ) : ℝ≥0∞ :=
  ∑' b : FluxInfluenceIndex, kernelIFOrientedDensity ν f eps b.1 b.2 (fun _ => True)
    (fun g => ENNReal.ofReal |kernelBoundaryReward ν C ψ (gapKeys g b.1)|) x

theorem output_IF_boundary_enorm_le_abs_mass (eps : ℝ) (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (ψ : ℝ → ℝ) (C x : ℝ) :
    ‖outputIFBoundary eps ν f ψ C x‖ₑ ≤ 2 * kernelOutputAbsMass eps ν f ψ C x := by
  apply enorm_tsum_le_tsum_enorm.trans
  calc
    _ ≤ ∑' a : ℕ × ℕ, if a.2 < a.1 then 2 * kernelIFOrientedDensity ν f eps a.1 a.2
        (fun _ => True) (fun g => ENNReal.ofReal |kernelBoundaryReward ν C ψ (gapKeys g a.1)|) x else 0 := by
      apply ENNReal.tsum_le_tsum
      intro a
      unfold outputIFTerm
      split_ifs
      · exact kernel_IF_weighted_prefix_enorm_le_abs_mass ν f eps a.1 a.2 _ x
      · simp only [enorm_zero, le_refl]
    _ = _ := by
      rw [kernel_ennreal_tsum_triangle (fun k i => 2 * kernelIFOrientedDensity ν f eps k i
        (fun _ => True) (fun g => ENNReal.ofReal |kernelBoundaryReward ν C ψ (gapKeys g k)|) x), ENNReal.tsum_mul_left]
      rfl

/-- The original boundary is controlled by the actual five-length block mass
with its original absolute reward, retaining the full physical sum. -/
theorem output_IF_boundary_enorm_le_blocks_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D η M : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ)
    (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hfD : ∀ u, f u ≤ D)
    (hfneg : ∀ u ≤ 0, f u = 0)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    (hpos : ∀ᵐ u ∂(ν : Measure ℝ), 0 < u) {eps : ℝ} (heps : 0 ≤ eps) (C : ℝ) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
      ‖outputIFBoundary eps ν (fun u => ENNReal.ofReal (f u)) ψ C x‖ₑ ≤
        2 * kernelIFTotalPinBlockMass ν f eps
          (fun s => ENNReal.ofReal |kernelBoundaryReward ν C ψ s|) (fun _ => True) x := by
  have hH := ((measurable_kernelBoundaryReward hψ ν C).abs).ennreal_ofReal
  filter_upwards [kernel_IF_total_actual_oriented_mass_eq_blocks_ae ν hf hf0 hfD hfneg hν hpos heps hH (fun _ => True)] with x hx
  exact (output_IF_boundary_enorm_le_abs_mass eps ν _ ψ C x).trans_eq (congrArg (fun a : ℝ≥0∞ => 2 * a) hx)

end
end PGM
