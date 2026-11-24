import PLAStochastic.Index.GEP.Kernel.Output.Finite.FacetBound
import PLAStochastic.Index.GEP.Kernel.Output.Finite.StopTriangle

/-!
# Deleted-mark window bounds for actual output facets

The original positive lower and upper endpoints lie on feasible inserted
prefixes. Their local reward mass is therefore supported on the same deleted
windows that give summability of the original stopping triangle.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_IF_lower_mem_winSet {eps : ℝ} {k i : ℕ} (hk : 2 ≤ k) (hik : i < k)
    {g : ℕ → ℝ} (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hS : g ∈ kernelIFLowerSection eps k i) : g ∈ winSet eps i k := by
  classical
  let c : FluxFacetIndex k → ℝ := fun q => fluxFacetCoef eps q i
  let d := fluxPrefixRHS eps k i
  have hsection : g ∈ (if h : (fluxPos c).Nonempty then fluxPolyActive c d h
      else fluxPolyZeroOK c d) := hS.1
  apply output_IF_path_mem_winSet hik (x := kernelPrefixLower eps k i g)
  apply (kernel_IF_update_event_iff hk hik g hg).mpr
  refine ⟨hS.2, ?_⟩
  by_cases hp : (fluxPos c).Nonempty
  · have hactive : g ∈ fluxPolyActive c d hp := by
      simpa only [dif_pos hp] using hsection
    exact (fluxPoly_iff_interval c d hp g hS.2).mpr ⟨hactive.1, le_rfl, hactive.2⟩
  · have hzero : g ∈ fluxPolyZeroOK c d := by
      simpa only [dif_neg hp] using hsection
    exact (fluxPoly_iff_halfLine c d hp g hS.2).mpr ⟨hzero, le_rfl⟩

theorem output_IF_upper_mem_winSet {eps : ℝ} {k i : ℕ} (hk : 2 ≤ k) (hik : i < k)
    (hp : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty)
    {g : ℕ → ℝ} (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hS : g ∈ kernelIFUpperSection eps k i hp) : g ∈ winSet eps i k := by
  apply output_IF_path_mem_winSet hik (x := kernelPrefixUpper eps k i hp g)
  apply (kernel_IF_update_event_iff hk hik g hg).mpr
  exact ⟨hS.2, (fluxPoly_iff_interval _ _ hp g hS.2).mpr ⟨hS.1.1, hS.1.2, le_rfl⟩⟩

theorem output_reward_endpoint_window_le {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    (eps : ℝ) {k i : ℕ} (hik : i < k) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) (hηθ : η / C ≤ θ / 4)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {S : Set (ℕ → ℝ)}
    (hS : MeasurableSet S) (hE0 : ∀ g ∈ S, 0 ≤ E g)
    (hSW : ∀ᵐ g ∂iidLaw ν, g ∈ S → g ∈ winSet eps i k) (R : ℝ) :
    (∫ g in {g | E g ≤ max 0 R},
      |kernelBoundaryReward ν C ψ (gapKeys (Function.update g i (E g)) k)|
        ∂(iidLaw ν).restrict S) ≤
      (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R)) *
        fluxWindowMoment eps ν (2 * η / C) (k,i) := by
  have hκθ : 2 * η / C ≤ θ / 2 := by
    calc
      2 * η / C = 2 * (η / C) := by ring
      _ ≤ θ / 2 := by linarith
  have hExp := flux_regLaw_unmarked_exp hν hθ (by positivity) hκθ k i
  have hall : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  have hcut : MeasurableSet {g | E g ≤ max 0 R} := measurableSet_le hE measurable_const
  have hI := (output_reward_endpoint_integrableOn hν hθ hik hψ hη hC hηθ hE hS hE0
    (max 0 R)).abs
  rw [Measure.restrict_restrict hcut] at hI
  simp only [fluxWindowMoment, hik, if_true]
  rw [Measure.restrict_restrict hcut, ← integral_indicator (hcut.inter hS),
    ← integral_indicator (measurableSet_winSet eps i k), ← integral_const_mul]
  apply integral_mono_ae ((integrable_indicator_iff (hcut.inter hS)).mpr hI)
    ((hExp.indicator (measurableSet_winSet eps i k)).const_mul _)
  filter_upwards [hall, hSW] with g hg hW
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  by_cases hgA : g ∈ {g | E g ≤ max 0 R} ∩ S
  · rw [indicator_of_mem hgA, indicator_of_mem (hW hgA.2), flux_gapKeys_update hik]
    exact output_reward_shift_bound hν hθ hψ hη hC hηθ
      (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) k i).1 ⟨hE0 g hgA.2, hgA.1⟩
  · rw [indicator_of_notMem hgA]
    apply mul_nonneg (by positivity)
    exact indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

theorem output_reward_oriented_norm_le {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) {k i : ℕ} (hik : i < k) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) (hηθ : η / C ≤ θ / 4)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {S : Set (ℕ → ℝ)}
    (hS : MeasurableSet S) (hE0 : ∀ g ∈ S, 0 ≤ E g)
    (hsel : ∀ g ∈ S, ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    (hSW : ∀ᵐ g ∂iidLaw ν, g ∈ S → g ∈ winSet eps i k)
    (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (horient : ∀ V : (ℕ → ℝ) → ℝ≥0∞, Measurable V →
      kernelSelectedFacetDensity ν f eps k i E S (fun g => V (Function.update g i (E g)))
        =ᵐ[volume.restrict (Ioi 0)] kernelIFOrientedDensity ν f eps k i A V) (R : ℝ) :
    IntervalIntegrable (kernelIFSignedDensity ν f eps k i A
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k))) volume 0 R ∧
    (∫ x in Ι (0 : ℝ) R, ‖kernelIFSignedDensity ν f eps k i A
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x‖) ≤
      (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R)) *
        fluxWindowMoment eps ν (2 * η / C) (k,i) := by
  let W : (ℕ → ℝ) → ℝ := fun g => kernelBoundaryReward ν C ψ (gapKeys g k)
  have hW : Measurable W := (measurable_kernelBoundaryReward hψ ν C).comp
    ((measurable_pi_apply k).comp measurable_gapKeys)
  have hWU : Measurable (fun g => W (Function.update g i (E g))) :=
    hW.comp ((measurable_update_pair i).comp (hE.prodMk measurable_id))
  have hWi := output_reward_endpoint_integrableOn hν hθ hik hψ hη hC hηθ hE hS hE0
  have hbound := output_selected_endpoint_norm_le ν hf hνf eps k i hE hS hsel hWU hWi R
  have hp := kernel_IF_positiveDensity_congr (horient _ hW.ennreal_ofReal)
  have hn := kernel_IF_positiveDensity_congr (horient _ hW.neg.ennreal_ofReal)
  have he : (fun x =>
      fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E S
        (fun g => ENNReal.ofReal (W (Function.update g i (E g))))) x -
      fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E S
        (fun g => ENNReal.ofReal (-W (Function.update g i (E g))))) x)
        =ᵐ[volume] kernelIFSignedDensity ν f eps k i A W := by
    filter_upwards [hp, hn] with x hpx hnx
    exact congrArg₂ (fun p n : ℝ => p - n) hpx hnx
  have heI := integral_congr_ae (μ := volume.restrict (Ι (0 : ℝ) R))
    (ae_restrict_of_ae (he.fun_comp norm))
  simp only [Function.comp_apply] at heI
  rw [heI] at hbound
  refine ⟨?_, hbound.trans
    (output_reward_endpoint_window_le hν hθ eps hik hψ hη hC hηθ hE hS hE0 hSW R)⟩
  exact (output_selected_endpoint_intervalIntegrable ν hf hνf eps k i hE hS hsel hWU hWi R).congr_ae
    (ae_restrict_of_ae he)

theorem output_reward_lower_norm_le {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hk : 2 ≤ k) (hik : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) (R : ℝ) :
    IntervalIntegrable (kernelIFSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0)
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k))) volume 0 R ∧
    (∫ x in Ι (0 : ℝ) R, ‖kernelIFSignedDensity ν f eps k i
      (fun q => fluxFacetCoef eps q i < 0)
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x‖) ≤
      (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R)) *
        fluxWindowMoment eps ν (2 * η / C) (k,i) := by
  apply output_reward_oriented_norm_le hν hθ hf hνf eps hik hψ hη hC hηθ
    (measurable_fluxPolyLower _ (measurable_fluxPrefixRHS eps k i))
    (measurableSet_kernelIFLowerSection eps k i)
    (fun g hg => hg.2.le)
    (fun g hg => fluxPolyLower_select _ _ g hg.2)
  · filter_upwards [kernel_IF_positive_gaps_ae ν hν.ae_pos k i] with g hg hS
    exact output_IF_lower_mem_winSet hk hik hg hS
  · exact fun V hV => kernel_IF_lower_density_eq_active_sum ν hf hνf hν.ae_pos heps hk hik hV

theorem output_reward_upper_norm_le {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hk : 2 ≤ k) (hik : i < k)
    (hp : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) (R : ℝ) :
    IntervalIntegrable (kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i)
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k))) volume 0 R ∧
    (∫ x in Ι (0 : ℝ) R, ‖kernelIFSignedDensity ν f eps k i
      (fun q => 0 < fluxFacetCoef eps q i)
      (fun g => kernelBoundaryReward ν C ψ (gapKeys g k)) x‖) ≤
      (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R)) *
        fluxWindowMoment eps ν (2 * η / C) (k,i) := by
  apply output_reward_oriented_norm_le hν hθ hf hνf eps hik hψ hη hC hηθ
    (measurable_fluxPolyUpper _ (measurable_fluxPrefixRHS eps k i) hp)
    (measurableSet_kernelIFUpperSection eps k i hp)
    (fun g hg => hg.2.le)
    (fun g _ => fluxPolyUpper_select _ _ hp g)
  · filter_upwards [kernel_IF_positive_gaps_ae ν hν.ae_pos k i] with g hg hS
    exact output_IF_upper_mem_winSet hk hik hp hg hS
  · exact fun V hV => kernel_IF_upper_density_eq_active_sum ν hf hνf hν.ae_pos heps hk hik hp hV

end
end PGM
