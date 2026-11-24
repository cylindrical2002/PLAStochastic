import PLAStochastic.Index.GEP.Kernel.Output.Finite.Endpoint
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.PrefixDerivative
import PLAStochastic.Index.GEP.Response.InfluenceDecomposition

/-!
# Explicit signed densities of locally integrable output endpoint rewards

The actual weighted endpoint measure need only be finite on sublevel sets.
Its positive and negative densities identify the spatial derivative without
requiring a global exponential moment of a possibly distant selected root.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem output_cdf_local_explicit_aePrimitive (μ : Measure ℝ)
    (hfin : ∀ R : ℝ, μ (Iic R) ≠ ∞) {d : ℝ → ℝ≥0∞}
    (hd : Measurable d)
    (hμ : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity d) :
    AEPrimitive (fun x => μ.real (Iic x)) (fluxPositiveDensity d) := by
  have hac : μ.restrict (Ioi 0) ≪ volume := by
    rw [hμ]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  exact flux_aePrimitive_congr_derivative (flux_cdf_aePrimitive_local μ hfin hac)
    (flux_positive_density_eq_rnDeriv μ hd hμ)

theorem output_cdf_nonneg_explicit_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {E W : Ω → ℝ} (hE : Measurable E)
    (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P)
    {d : ℝ → ℝ≥0∞} (hd : Measurable d)
    (hmap : ((P.withDensity (fun ω => ENNReal.ofReal (W ω))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity d) :
    AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) (fluxPositiveDensity d) := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (W ω))
  have hfin : ∀ R : ℝ, (Q.map E) (Iic R) ≠ ∞ := by
    intro R
    rw [Measure.map_apply hE measurableSet_Iic]
    change (P.withDensity (fun ω => ENNReal.ofReal (W ω))) {ω | E ω ≤ R} ≠ ∞
    rw [withDensity_apply' _ _]
    have hh := (hWi R).2
    rw [hasFiniteIntegral_iff_enorm] at hh
    simpa only [Real.enorm_of_nonneg (hW0 _)] using hh.ne
  have hp := output_cdf_local_explicit_aePrimitive (Q.map E) hfin hd hmap
  have he : (fun x => (Q.map E).real (Iic x)) =
      (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P) := by
    funext x
    rw [map_measureReal_apply hE measurableSet_Iic]
    exact flux_weighted_measure_real P hW hW0 (hE measurableSet_Iic)
  rwa [he] at hp

theorem output_cdf_signed_explicit_aePrimitive {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {E W : Ω → ℝ} (hE : Measurable E)
    (hW : Measurable W) (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P)
    {dp dn : ℝ → ℝ≥0∞} (hdp : Measurable dp) (hdn : Measurable dn)
    (hp : ((P.withDensity (fun ω => ENNReal.ofReal (W ω))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity dp)
    (hn : ((P.withDensity (fun ω => ENNReal.ofReal (-W ω))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity dn) :
    AEPrimitive (fun x => ∫ ω in {ω | E ω ≤ x}, W ω ∂P)
      (fun x => fluxPositiveDensity dp x - fluxPositiveDensity dn x) := by
  have hp' : (fun ω => ENNReal.ofReal (max (W ω) 0)) =
      (fun ω => ENNReal.ofReal (W ω)) := by
    funext ω
    simp
  have hn' : (fun ω => ENNReal.ofReal (max (-W ω) 0)) =
      (fun ω => ENNReal.ofReal (-W ω)) := by
    funext ω
    simp
  obtain ⟨hIp, cp, hcp⟩ := output_cdf_nonneg_explicit_aePrimitive P hE
    (hW.max measurable_const) (fun ω => le_max_right _ _)
    (fun R => (hWi R).pos_part) hdp (by simpa only [hp'] using hp)
  obtain ⟨hIn, cn, hcn⟩ := output_cdf_nonneg_explicit_aePrimitive P hE
    (hW.neg.max measurable_const) (fun ω => le_max_right _ _)
    (fun R => (hWi R).neg_part) hdn (by simpa only [Pi.neg_apply, hn'] using hn)
  simp only [Pi.neg_apply] at hcn
  refine ⟨fun R => (hIp R).sub (hIn R), cp - cn, ?_⟩
  filter_upwards [hcp, hcn] with x hpx hnx
  have he : (∫ ω in {ω | E ω ≤ x}, W ω ∂P) =
      (∫ ω in {ω | E ω ≤ x}, max (W ω) 0 ∂P) -
      ∫ ω in {ω | E ω ≤ x}, max (-W ω) 0 ∂P := by
    rw [← integral_sub (hWi x).pos_part (hWi x).neg_part]
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by grind
  rw [he, hpx, hnx, intervalIntegral.integral_sub (hIp x) (hIn x)]
  ring

/-- The original output reward has exactly the local endpoint moments needed
by the signed density theorem, uniformly over the original test class. -/
theorem output_endpoint_reward_integrable {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {i k : ℕ} (hik : i < k)
    {A : Set (ℕ → ℝ)} (hA : MeasurableSet A)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {R : ℝ}
    (hER : ∀ g ∈ A, E g ∈ Icc (0 : ℝ) (max 0 R)) :
    Integrable (A.indicator (fun g => kernelBoundaryReward ν C ψ
      (gapKeys (Function.update g i (E g)) k))) (iidLaw ν) := by
  have hκθ : η / C ≤ θ / 2 := by linarith
  have hExp := (flux_regLaw_unmarked_exp hν hθ (div_nonneg hη hC.le) hκθ k i).const_mul
    (M * (8 * D / θ ^ 2) / C * Real.exp (η * max 0 R / C))
  have hgs : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
      |>.ae hν.ae_pos
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  simp_rw [flux_gapKeys_update hik]
  refine hExp.mono' (((measurable_kernelBoundaryReward hψ ν C).comp
    ((measurable_fluxUnmarkedSum k i).add hE)).indicator hA).aestronglyMeasurable ?_
  filter_upwards [hgs] with g hg
  by_cases hgA : g ∈ A
  · rw [indicator_of_mem hgA, Real.norm_eq_abs]
    have hu := (fluxUnmarkedSum_nonneg_le (fun j => (hg j).le) k i).1
    calc
      _ ≤ M * (8 * D / θ ^ 2) / C *
          Real.exp (η * (fluxUnmarkedSum k i g + E g) / C) :=
        kernelBoundaryReward_le hν hθ hψ hη hC hηθ (add_nonneg hu (hER g hgA).1)
      _ ≤ M * (8 * D / θ ^ 2) / C *
          Real.exp (η * (fluxUnmarkedSum k i g + max 0 R) / C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith [(hER g hgA).2]) hη) hC.le)
      _ = _ := by
        rw [show η * (fluxUnmarkedSum k i g + max 0 R) / C =
          η * max 0 R / C + η / C * fluxUnmarkedSum k i g by ring, Real.exp_add]
        ring
  · rw [indicator_of_notMem hgA, norm_zero]
    positivity

/-- Signed selected-facet densities of the original endpoint CDF. -/
theorem output_selected_endpoint_aePrimitive (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {E W : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hsel : ∀ g ∈ S, 0 < E g → ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    (hW : Measurable W)
    (hWi : ∀ R : ℝ, IntegrableOn W {g | E g ≤ R} ((iidLaw ν).restrict S)) :
    AEPrimitive (fun x => ∫ g in {g | E g ≤ x}, W g ∂(iidLaw ν).restrict S)
      (fun x =>
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E
          (S ∩ E ⁻¹' Ioi 0) (fun g => ENNReal.ofReal (W g))) x -
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E
          (S ∩ E ⁻¹' Ioi 0) (fun g => ENNReal.ofReal (-W g))) x) := by
  apply output_cdf_signed_explicit_aePrimitive _ hE hW hWi
    (flux_measurable_selected_density ν hf eps k i hE
      (hS.inter (hE measurableSet_Ioi)) hW.ennreal_ofReal)
    (flux_measurable_selected_density ν hf eps k i hE
      (hS.inter (hE measurableSet_Ioi)) hW.neg.ennreal_ofReal)
  · rw [← restrict_withDensity hS]
    exact kernel_selected_positive_facet_map_density ν hf hν eps k i hE hS hsel hW.ennreal_ofReal
  · rw [← restrict_withDensity hS]
    exact kernel_selected_positive_facet_map_density ν hf hν eps k i hE hS hsel hW.neg.ennreal_ofReal

/-- Local moments at a nonnegative endpoint follow from `RegLaw`; no endpoint
moment is added to the original output hypotheses. -/
theorem output_reward_selected_endpoint_aePrimitive {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) {k i : ℕ} (hik : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) {E : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S) (hE0 : ∀ g ∈ S, 0 ≤ E g)
    (hsel : ∀ g ∈ S, 0 < E g → ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i) :
    let W := fun g => kernelBoundaryReward ν C ψ (gapKeys (Function.update g i (E g)) k)
    AEPrimitive (fun x => ∫ g in {g | E g ≤ x}, W g ∂(iidLaw ν).restrict S)
      (fun x =>
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E
          (S ∩ E ⁻¹' Ioi 0) (fun g => ENNReal.ofReal (W g))) x -
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E
          (S ∩ E ⁻¹' Ioi 0) (fun g => ENNReal.ofReal (-W g))) x) := by
  dsimp only
  have hU : Measurable (fun g => Function.update g i (E g)) :=
    (measurable_update_pair i).comp (hE.prodMk measurable_id)
  apply output_selected_endpoint_aePrimitive ν hf hνf eps k i hE hS hsel
    ((measurable_kernelBoundaryReward hψ ν C).comp
      (((measurable_pi_apply k).comp measurable_gapKeys).comp hU))
  intro R
  have hcut : MeasurableSet {g | E g ≤ R} := measurableSet_le hE measurable_const
  rw [IntegrableOn, Measure.restrict_restrict hcut]
  apply (integrable_indicator_iff (hcut.inter hS)).mp
  exact output_endpoint_reward_integrable hν hθ hψ hη hC hηθ hik (hcut.inter hS) hE
    (fun g hg => ⟨hE0 g hg.2, hg.1.trans (le_max_right _ _)⟩)

/-- The signed oriented density retains the positive and negative reward
measures separately until after their local finiteness is established. -/
def kernelIFSignedDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (W : (ℕ → ℝ) → ℝ) (x : ℝ) : ℝ :=
  fluxPositiveDensity (kernelIFOrientedDensity ν f eps k i A
    (fun g => ENNReal.ofReal (W g))) x -
  fluxPositiveDensity (kernelIFOrientedDensity ν f eps k i A
    (fun g => ENNReal.ofReal (-W g))) x

def kernelIFWeightedPrefixKernel (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (W : (ℕ → ℝ) → ℝ) (x : ℝ) : ℝ :=
  kernelIFSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) W x -
  kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W x

/-- The actual output endpoint CDF has the original signed active-facet
density as its derivative, for every measurable test in `OutTest`. -/
theorem output_reward_prefix_aePrimitive {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hk : 2 ≤ k) (hik : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) :
    AEPrimitive
      (outputPrefixBoundaryCDF (iidLaw ν) eps k i
        (fun g z => kernelBoundaryReward ν C ψ (gapKeys (Function.update g i z) k)))
      (kernelIFWeightedPrefixKernel ν f eps k i
        (fun g => kernelBoundaryReward ν C ψ (gapKeys g k))) := by
  classical
  let c : FluxFacetIndex k → ℝ := fun q => fluxFacetCoef eps q i
  let d := fluxPrefixRHS eps k i
  let W : (ℕ → ℝ) → ℝ := fun g => kernelBoundaryReward ν C ψ (gapKeys g k)
  have hW : Measurable W := (measurable_kernelBoundaryReward hψ ν C).comp
    ((measurable_pi_apply k).comp measurable_gapKeys)
  let S := if h : (fluxPos c).Nonempty then fluxPolyActive c d h else fluxPolyZeroOK c d
  have hS : MeasurableSet S := by
    dsimp only [S]
    split_ifs with h
    · exact measurableSet_fluxPolyActive c (measurable_fluxPrefixRHS eps k i) h
    · exact measurableSet_fluxPolyZeroOK c (measurable_fluxPrefixRHS eps k i)
  have hLp := kernel_IF_positiveDensity_congr
    (kernel_IF_lower_density_eq_active_sum ν hf hνf hν.ae_pos heps hk hik hW.ennreal_ofReal)
  have hLn := kernel_IF_positiveDensity_congr
    (kernel_IF_lower_density_eq_active_sum ν hf hνf hν.ae_pos heps hk hik hW.neg.ennreal_ofReal)
  have hL0 := output_reward_selected_endpoint_aePrimitive hν hθ hf hνf eps hik
    hψ hη hC hηθ (measurable_fluxPolyLower c (measurable_fluxPrefixRHS eps k i)) hS
    (fun g _ => fluxPolyLower_nonneg c d g)
    (fun g _ hg => fluxPolyLower_select c d g hg)
  have hL : AEPrimitive
      (fun x => ∫ g in {g | fluxPolyLower c d g ≤ x},
        W (Function.update g i (fluxPolyLower c d g)) ∂(iidLaw ν).restrict S)
      (kernelIFSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) W) := by
    apply flux_aePrimitive_congr_derivative hL0
    filter_upwards [hLp, hLn] with x hpx hnx
    change _ - _ = _ - _
    simpa only [kernelIFLowerSection, kernelPrefixLower, c, d, S, W, Pi.neg_apply]
      using congrArg₂ (fun p n : ℝ => p - n) hpx hnx
  by_cases hp : (fluxPos c).Nonempty
  · have hU0 := output_reward_selected_endpoint_aePrimitive hν hθ hf hνf eps hik
      hψ hη hC hηθ (measurable_fluxPolyUpper c (measurable_fluxPrefixRHS eps k i) hp)
      (measurableSet_fluxPolyActive c (measurable_fluxPrefixRHS eps k i) hp)
      (fun g hg => (fluxPolyLower_nonneg c d g).trans hg.2)
      (fun g _ _ => fluxPolyUpper_select c d hp g)
    have hUp := kernel_IF_positiveDensity_congr
      (kernel_IF_upper_density_eq_active_sum ν hf hνf hν.ae_pos heps hk hik hp hW.ennreal_ofReal)
    have hUn := kernel_IF_positiveDensity_congr
      (kernel_IF_upper_density_eq_active_sum ν hf hνf hν.ae_pos heps hk hik hp hW.neg.ennreal_ofReal)
    have hU : AEPrimitive
        (fun x => ∫ g in {g | fluxPolyUpper c d hp g ≤ x},
          W (Function.update g i (fluxPolyUpper c d hp g))
            ∂(iidLaw ν).restrict (fluxPolyActive c d hp))
        (kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W) := by
      apply flux_aePrimitive_congr_derivative hU0
      filter_upwards [hUp, hUn] with x hpx hnx
      change _ - _ = _ - _
      simpa only [kernelIFUpperSection, kernelPrefixUpper, c, d, W, Pi.neg_apply]
        using congrArg₂ (fun p n : ℝ => p - n) hpx hnx
    unfold outputPrefixBoundaryCDF outputPolyBoundaryCDF kernelIFWeightedPrefixKernel
    simpa [S, hp, c, d, W, sub_eq_add_neg] using hL.add (hU.const_mul (-1))
  · have hzero : ∀ (V : (ℕ → ℝ) → ℝ≥0∞),
        kernelIFOrientedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) V =
          fun _ => 0 := by
      intro V
      funext x
      unfold kernelIFOrientedDensity
      rw [tsum_fintype]
      apply Finset.sum_eq_zero
      intro r _
      apply if_neg
      intro hr
      exact hp ⟨_, by simpa only [fluxPos, Finset.mem_filter, Finset.mem_univ, true_and, c] using hr⟩
    change AEPrimitive (outputPolyBoundaryCDF (iidLaw ν) c d
      (fun g z => W (Function.update g i z))) (fun x =>
        kernelIFSignedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) W x -
        kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W x)
    have hz : kernelIFSignedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W =
        fun _ => 0 := by
      funext x
      simp [kernelIFSignedDensity, hzero, fluxPositiveDensity]
    unfold outputPolyBoundaryCDF
    simpa only [outputPolyBoundaryCDF, dif_neg hp, hz, sub_zero, S] using hL

theorem output_occupation_facet_aePrimitive {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hνf : (ν : Measure ℝ) = volume.withDensity f)
    {eps : ℝ} {k i : ℕ} (heps : 0 < eps) (hk : 2 ≤ k) (hik : i < k)
    {η M C : ℝ} {ψ : ℝ → ℝ} (hψ : OutTest η M ψ) (hη : 0 < η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) :
    AEPrimitive (outputOccupationBoundaryCDF eps ν ψ C k i)
      (kernelIFWeightedPrefixKernel ν f eps k i
        (fun g => kernelBoundaryReward ν C ψ (gapKeys g k))) := by
  have he := funext (output_occupation_boundary_eq_reward hν hθ eps hψ hη hC hηθ hik)
  rw [he]
  exact output_reward_prefix_aePrimitive hν hθ hf hνf heps hk hik hψ hη.le hC hηθ

end
end PGM
