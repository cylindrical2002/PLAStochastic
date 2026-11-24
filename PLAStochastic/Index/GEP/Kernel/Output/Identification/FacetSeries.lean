import PLAStochastic.Index.GEP.Kernel.Output.Identification.DeletedMarkWindow
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveLocalBound

/-!
# Locally absolutely summable actual output facet kernels

The finite kernels are the signed oriented physical densities, with the
original next-gap reward. Their local mass is controlled by the original
deleted-mark window moment before any infinite regrouping is performed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_IF_upper_signed_zero (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (W : (ℕ → ℝ) → ℝ)
    (hp : ¬ (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty) :
    kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W = fun _ => 0 := by
  classical
  have hzero : ∀ (V : (ℕ → ℝ) → ℝ≥0∞),
      kernelIFOrientedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) V = fun _ => 0 := by
    intro V
    funext x
    unfold kernelIFOrientedDensity
    rw [tsum_fintype]
    apply Finset.sum_eq_zero
    intro r _
    apply if_neg
    intro hr
    exact hp ⟨_, by simpa only [fluxPos, Finset.mem_filter, Finset.mem_univ, true_and] using hr⟩
  funext x
  simp [kernelIFSignedDensity, hzero, fluxPositiveDensity]

theorem output_IF_weighted_prefix_zero_of_lt_two (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (eps : ℝ) {k : ℕ} (hk : k < 2) (i : ℕ)
    (W : (ℕ → ℝ) → ℝ) : kernelIFWeightedPrefixKernel ν f eps k i W = fun _ => 0 := by
  classical
  have hc (q : FluxFacetIndex k) : fluxFacetCoef eps q i = 0 := by
    have hn : ¬ fluxFacetValid q := by
      intro h
      have ht := q.2.2.1.isLt
      change (q.1 : ℕ) < q.2.1 ∧ (q.2.1 : ℕ) < q.2.2.1 at h
      omega
    simp only [fluxFacetCoef, if_neg hn]
  funext x
  simp [kernelIFWeightedPrefixKernel, kernelIFSignedDensity, kernelIFOrientedDensity,
    hc, fluxPositiveDensity]

theorem output_IF_prefix_local_bound {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hik : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) (R : ℝ) :
    IntervalIntegrable (kernelIFWeightedPrefixKernel ν f eps k i
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k))) volume 0 R ∧
    (∫ x in Ι (0 : ℝ) R, ‖kernelIFWeightedPrefixKernel ν f eps k i
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x‖) ≤
      (2 * (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R))) *
        fluxWindowMoment eps ν (2 * η / C) (k,i) := by
  classical
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hW0 := fluxWindowMoment_nonneg eps ν (2 * η / C) (k,i)
  by_cases hk : 2 ≤ k
  · have hL := output_reward_lower_norm_le hν hθ hf hνf heps hk hik hψ hη hC hηθ R
    by_cases hp : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty
    · have hU := output_reward_upper_norm_le hν hθ hf hνf heps hk hik hp hψ hη hC hηθ R
      refine ⟨hL.1.sub hU.1, ?_⟩
      unfold kernelIFWeightedPrefixKernel
      calc
        _ ≤ ∫ x in Ι (0 : ℝ) R,
            ‖kernelIFSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0)
              (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x‖ +
            ‖kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i)
              (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x‖ :=
          integral_mono (hL.1.def'.sub hU.1.def').norm
            (hL.1.def'.norm.add hU.1.def'.norm) (fun _ => norm_sub_le _ _)
        _ = _ := integral_add hL.1.def'.norm hU.1.def'.norm
        _ ≤ _ := by linarith [hL.2, hU.2]
    · have hz := output_IF_upper_signed_zero ν f eps k i
        (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) hp
      have he : kernelIFWeightedPrefixKernel ν f eps k i
          (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) =
          kernelIFSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0)
            (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) := by
        funext x
        simp only [kernelIFWeightedPrefixKernel, hz, sub_zero]
      rw [he]
      refine ⟨hL.1, hL.2.trans ?_⟩
      have : 0 ≤ (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R)) *
          fluxWindowMoment eps ν (2 * η / C) (k,i) := by positivity
      nlinarith
  · rw [output_IF_weighted_prefix_zero_of_lt_two ν f eps (by omega) i]
    refine ⟨(integrable_zero _ _ _).intervalIntegrable, ?_⟩
    simp only [norm_zero, integral_zero]
    positivity

/-- A concrete kernel on the original marked prefix triangle. -/
def outputIFTerm (eps : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (ψ : ℝ → ℝ) (C : ℝ) (a : ℕ × ℕ) (x : ℝ) : ℝ :=
  if a.2 < a.1 then kernelIFWeightedPrefixKernel ν f eps a.1 a.2
    (fun g => kernelBoundaryReward ν C ψ (gapKeys g a.1)) x else 0

theorem output_IF_local_summable {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 0 < eps) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) (hηθ : η / C ≤ θ / 4)
    (hWin : Summable (fluxWindowMoment eps ν (2 * η / C))) (R : ℝ) :
    (∀ a : ℕ × ℕ, IntervalIntegrable (outputIFTerm eps ν f ψ C a) volume 0 R) ∧
      Summable (fun a : ℕ × ℕ => ∫ x in Ι (0 : ℝ) R, ‖outputIFTerm eps ν f ψ C a x‖) := by
  have hb (a : ℕ × ℕ) :
      IntervalIntegrable (outputIFTerm eps ν f ψ C a) volume 0 R ∧
      (∫ x in Ι (0 : ℝ) R, ‖outputIFTerm eps ν f ψ C a x‖) ≤
        (2 * (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R))) *
          fluxWindowMoment eps ν (2 * η / C) a := by
    unfold outputIFTerm
    by_cases ha : a.2 < a.1
    · simpa only [outputIFTerm, ha, if_true] using
        output_IF_prefix_local_bound hν hθ hf hνf heps ha hψ hη hC hηθ R
    · simp only [fluxWindowMoment, ha, if_false, norm_zero, integral_zero,
        mul_zero, le_refl, and_true]
      exact (integrable_zero _ _ _).intervalIntegrable
  exact ⟨fun a => (hb a).1,
    Summable.of_nonneg_of_le (fun a => integral_nonneg fun _ => norm_nonneg _)
      (fun a => (hb a).2) (hWin.mul_left _)⟩

theorem output_local_ae_summable {ι : Type*} [Countable ι] {j : ι → ℝ → ℝ}
    (hi : ∀ i R, IntervalIntegrable (j i) volume 0 R)
    (hs : ∀ R : ℝ, Summable fun i => ∫ x in Ι (0 : ℝ) R, ‖j i x‖) :
    ∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)), Summable (fun i => ‖j i x‖) := by
  have hlocal (n : ℕ) : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) n),
      Summable (fun i => ‖j i x‖) := by
    have hi' (i : ι) : Integrable (j i) (volume.restrict (Ioc (0 : ℝ) n)) := (hi i n).1
    have hs' : Summable (fun i => ∫ x in Ioc (0 : ℝ) n, ‖j i x‖) := by
      simpa only [uIoc_of_le (Nat.cast_nonneg n)] using hs n
    have hfinite : (∫⁻ x, ∑' i, ‖j i x‖ₑ ∂volume.restrict (Ioc (0 : ℝ) n)) ≠ ∞ := by
      rw [lintegral_tsum fun i => (hi' i).aestronglyMeasurable.enorm]
      exact kernel_tsum_lintegral_enorm_ne_top hi' hs'
    filter_upwards [ae_lt_top' (AEMeasurable.tsum fun i => (hi' i).aestronglyMeasurable.enorm)
      hfinite] with x hx
    exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne
  have hu : (⋃ n : ℕ, Ioc (0 : ℝ) (n : ℝ)) = Ioi 0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      exact hn.1
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt x
      exact mem_iUnion.mpr ⟨n, hx, hn.le⟩
  rw [← hu]
  exact (ae_restrict_iUnion_iff _ _).mpr hlocal

def outputIFBoundary (eps : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (ψ : ℝ → ℝ) (C x : ℝ) : ℝ := ∑' a : ℕ × ℕ, outputIFTerm eps ν f ψ C a x

theorem output_IF_boundary_converges {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} (heps : 0 < eps) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) (hηθ : η / C ≤ θ / 4)
    (hWin : Summable (fluxWindowMoment eps ν (2 * η / C))) :
    (∀ R : ℝ, IntervalIntegrable (outputIFBoundary eps ν f ψ C) volume 0 R) ∧
      (∀ᵐ x ∂volume.restrict (Ioi (0 : ℝ)),
        Summable (fun a : ℕ × ℕ => ‖outputIFTerm eps ν f ψ C a x‖)) := by
  have hb := output_IF_local_summable hν hθ hf hνf heps hψ hη hC hηθ hWin
  constructor
  · intro R
    rw [intervalIntegrable_iff]
    exact kernel_integrable_tsum (fun a => ((hb R).1 a).def') (hb R).2
  · exact output_local_ae_summable (fun a R => (hb R).1 a) (fun R => (hb R).2)

end
end PGM
