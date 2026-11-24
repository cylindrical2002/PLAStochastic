import PLAStochastic.Index.GEP.Kernel.Output.Finite.FacetDensity
import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PrimitiveUnique

/-!
# Local absolute-mass bounds for the actual signed output facet density

The density is the concrete selected-facet representative. Local finiteness of
the endpoint measure suffices; a global reward moment is never assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_positive_density_local_norm_le (μ : Measure ℝ)
    (hfin : ∀ R : ℝ, μ (Iic R) ≠ ∞) {d : ℝ → ℝ≥0∞}
    (hd : Measurable d)
    (hμ : μ.restrict (Ioi 0) = (volume.restrict (Ioi 0)).withDensity d) (R : ℝ) :
    (∫ x in Ι (0 : ℝ) R, ‖fluxPositiveDensity d x‖) ≤ μ.real (Iic (max 0 R)) := by
  have : SigmaFinite μ := flux_sigmaFinite_of_cdf_finite μ hfin
  have hac : μ.restrict (Ioi 0) ≪ volume := by
    rw [hμ]
    exact (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have he := flux_positive_density_eq_rnDeriv μ hd hμ
  calc
    _ = ∫ x in Ι (0 : ℝ) R, fluxEndpointDensity (μ.restrict (Ioi 0)) x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae he] with x hx
      rw [← hx, Real.norm_eq_abs, fluxEndpointDensity, abs_of_nonneg ENNReal.toReal_nonneg]
    _ = (μ.restrict (Ioi 0)).real (Ι (0 : ℝ) R) :=
      Measure.setIntegral_toReal_rnDeriv hac _
    _ = μ.real ((Ι (0 : ℝ) R) ∩ Ioi 0) :=
      measureReal_restrict_apply measurableSet_uIoc
    _ ≤ μ.real (Iic (max 0 R)) := measureReal_mono (fun x hx => hx.1.2) (hfin _)

theorem output_cdf_nonneg_explicit_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {E W : Ω → ℝ} (hE : Measurable E)
    (hW : Measurable W) (hW0 : ∀ ω, 0 ≤ W ω)
    (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P)
    {d : ℝ → ℝ≥0∞} (hd : Measurable d)
    (hmap : ((P.withDensity (fun ω => ENNReal.ofReal (W ω))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity d) (R : ℝ) :
    (∫ x in Ι (0 : ℝ) R, ‖fluxPositiveDensity d x‖) ≤
      ∫ ω in {ω | E ω ≤ max 0 R}, W ω ∂P := by
  let Q := P.withDensity (fun ω => ENNReal.ofReal (W ω))
  have hfin : ∀ R : ℝ, (Q.map E) (Iic R) ≠ ∞ := by
    intro R
    rw [Measure.map_apply hE measurableSet_Iic]
    change (P.withDensity (fun ω => ENNReal.ofReal (W ω))) {ω | E ω ≤ R} ≠ ∞
    rw [withDensity_apply' _ _]
    have hh := (hWi R).2
    rw [hasFiniteIntegral_iff_enorm] at hh
    simpa only [Real.enorm_of_nonneg (hW0 _)] using hh.ne
  refine (output_positive_density_local_norm_le (Q.map E) hfin hd hmap R).trans_eq ?_
  rw [map_measureReal_apply hE measurableSet_Iic]
  exact flux_weighted_measure_real P hW hW0 (hE measurableSet_Iic)

theorem output_cdf_signed_explicit_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] {E W : Ω → ℝ} (hE : Measurable E)
    (hW : Measurable W) (hWi : ∀ R : ℝ, IntegrableOn W {ω | E ω ≤ R} P)
    {dp dn : ℝ → ℝ≥0∞} (hdp : Measurable dp) (hdn : Measurable dn)
    (hp : ((P.withDensity (fun ω => ENNReal.ofReal (W ω))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity dp)
    (hn : ((P.withDensity (fun ω => ENNReal.ofReal (-W ω))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity dn) (R : ℝ) :
    (∫ x in Ι (0 : ℝ) R, ‖fluxPositiveDensity dp x - fluxPositiveDensity dn x‖) ≤
      ∫ ω in {ω | E ω ≤ max 0 R}, |W ω| ∂P := by
  have hp' : ((P.withDensity (fun ω => ENNReal.ofReal (max (W ω) 0))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity dp := by simpa using hp
  have hn' : ((P.withDensity (fun ω => ENNReal.ofReal (max ((-W) ω) 0))).map E).restrict (Ioi 0) =
      (volume.restrict (Ioi 0)).withDensity dn := by simpa using hn
  have hIp := output_cdf_nonneg_explicit_aePrimitive P hE
    (hW.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).pos_part) hdp hp'
  have hIn := output_cdf_nonneg_explicit_aePrimitive P hE
    (hW.neg.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).neg_part) hdn hn'
  have hbp := output_cdf_nonneg_explicit_norm_le P hE
    (hW.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).pos_part) hdp hp' R
  have hbn := output_cdf_nonneg_explicit_norm_le P hE
    (hW.neg.max measurable_const) (fun ω => le_max_right _ _) (fun R => (hWi R).neg_part) hdn hn' R
  calc
    _ ≤ ∫ x in Ι (0 : ℝ) R, ‖fluxPositiveDensity dp x‖ + ‖fluxPositiveDensity dn x‖ :=
      integral_mono ((hIp.1 R).def'.sub (hIn.1 R).def').norm
        ((hIp.1 R).def'.norm.add (hIn.1 R).def'.norm) (fun x => norm_sub_le _ _)
    _ = (∫ x in Ι (0 : ℝ) R, ‖fluxPositiveDensity dp x‖) +
        ∫ x in Ι (0 : ℝ) R, ‖fluxPositiveDensity dn x‖ :=
      integral_add (hIp.1 R).def'.norm (hIn.1 R).def'.norm
    _ ≤ (∫ ω in {ω | E ω ≤ max 0 R}, max (W ω) 0 ∂P) +
        ∫ ω in {ω | E ω ≤ max 0 R}, max (-W ω) 0 ∂P := add_le_add hbp hbn
    _ = _ := by
      rw [← integral_add (hWi _).pos_part (hWi _).neg_part]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by grind

theorem output_selected_endpoint_norm_le (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {E W : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hsel : ∀ g ∈ S, ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    (hW : Measurable W)
    (hWi : ∀ R : ℝ, IntegrableOn W {g | E g ≤ R} ((iidLaw ν).restrict S)) (R : ℝ) :
    (∫ x in Ι (0 : ℝ) R, ‖
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E S
          (fun g => ENNReal.ofReal (W g))) x -
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E S
          (fun g => ENNReal.ofReal (-W g))) x‖) ≤
      ∫ g in {g | E g ≤ max 0 R}, |W g| ∂(iidLaw ν).restrict S := by
  apply output_cdf_signed_explicit_norm_le _ hE hW hWi
    (flux_measurable_selected_density ν hf eps k i hE hS hW.ennreal_ofReal)
    (flux_measurable_selected_density ν hf eps k i hE hS hW.neg.ennreal_ofReal)
  · rw [← restrict_withDensity hS]
    exact kernel_selected_facet_map_density ν hf hν eps k i hE hS hsel hW.ennreal_ofReal
  · rw [← restrict_withDensity hS]
    exact kernel_selected_facet_map_density ν hf hν eps k i hE hS hsel hW.neg.ennreal_ofReal

theorem output_reward_endpoint_integrableOn {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {k i : ℕ} (hik : i < k) {η M C : ℝ} {ψ : ℝ → ℝ}
    (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C) (hηθ : η / C ≤ θ / 4)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {S : Set (ℕ → ℝ)}
    (hS : MeasurableSet S) (hE0 : ∀ g ∈ S, 0 ≤ E g) (R : ℝ) :
    IntegrableOn (fun g => kernelBoundaryReward ν C ψ (gapKeys (Function.update g i (E g)) k))
      {g | E g ≤ R} ((iidLaw ν).restrict S) := by
  have hcut : MeasurableSet {g | E g ≤ R} := measurableSet_le hE measurable_const
  rw [IntegrableOn, Measure.restrict_restrict hcut]
  apply (integrable_indicator_iff (hcut.inter hS)).mp
  exact output_endpoint_reward_integrable hν hθ hψ hη hC hηθ hik (hcut.inter hS) hE
    (fun g hg => ⟨hE0 g hg.2, hg.1.trans (le_max_right _ _)⟩)

theorem output_selected_endpoint_intervalIntegrable (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) {E W : (ℕ → ℝ) → ℝ} (hE : Measurable E)
    {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hsel : ∀ g ∈ S, ∃ q : FluxFacetIndex k,
      E g = fluxPrefixRHS eps k i q g / fluxFacetCoef eps q i)
    (hW : Measurable W)
    (hWi : ∀ R : ℝ, IntegrableOn W {g | E g ≤ R} ((iidLaw ν).restrict S)) (R : ℝ) :
    IntervalIntegrable (fun x =>
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E S
          (fun g => ENNReal.ofReal (W g))) x -
        fluxPositiveDensity (kernelSelectedFacetDensity ν f eps k i E S
          (fun g => ENNReal.ofReal (-W g))) x) volume 0 R := by
  have hp := output_cdf_signed_explicit_aePrimitive ((iidLaw ν).restrict S) hE hW hWi
    (flux_measurable_selected_density ν hf eps k i hE hS hW.ennreal_ofReal)
    (flux_measurable_selected_density ν hf eps k i hE hS hW.neg.ennreal_ofReal)
    (by rw [← restrict_withDensity hS]
        exact kernel_selected_facet_map_density ν hf hν eps k i hE hS hsel hW.ennreal_ofReal)
    (by rw [← restrict_withDensity hS]
        exact kernel_selected_facet_map_density ν hf hν eps k i hE hS hsel hW.neg.ennreal_ofReal)
  exact hp.1 R

/-- The true active facet implies both predetermined deleted-mark windows. -/
theorem output_IF_path_mem_winSet {eps x : ℝ} {k i : ℕ} (hik : i < k)
    {g : ℕ → ℝ} (hg : Function.update g i x ∈ kernelIFPathEvent eps k) :
    g ∈ winSet eps i k := by
  have hT : (k : ℕ∞) < gapSegLen eps (Function.update g i x) := by
    rw [gapSegLen, lt_segLen_iff]
    exact hg.2
  refine ⟨pw_left_of_lt hik hT, fun _ => ?_⟩
  have hright := pw_window_of_lt hik hT
  exact lt_of_le_of_lt (by exact_mod_cast (by omega : k - (i + 2) ≤ k - 1 - i)) hright

/-- A bounded inserted endpoint costs only an explicit constant in the same
unmarked exponential moment that controls the stopping triangle. -/
theorem output_reward_shift_bound {D θ vlo vhi η M C s x R : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hηθ : η / C ≤ θ / 4) (hs : 0 ≤ s) (hx : x ∈ Icc (0 : ℝ) (max 0 R)) :
    |kernelBoundaryReward ν C ψ (s + x)| ≤
      (M * (8 * D / θ ^ 2) / C * Real.exp ((2 * η / C) * max 0 R)) *
        Real.exp ((2 * η / C) * s) := by
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hexp : η * (s + x) / C ≤ (2 * η / C) * max 0 R + (2 * η / C) * s := by
    have hsum : s + x ≤ 2 * (max 0 R + s) := by linarith [hx.2, le_max_left (0 : ℝ) R]
    calc
      _ ≤ η * (2 * (max 0 R + s)) / C :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum hη) hC.le
      _ = _ := by ring
  calc
    _ ≤ M * (8 * D / θ ^ 2) / C * Real.exp (η * (s + x) / C) :=
      kernelBoundaryReward_le hν hθ hψ hη hC hηθ (add_nonneg hs hx.1)
    _ ≤ M * (8 * D / θ ^ 2) / C *
        Real.exp ((2 * η / C) * max 0 R + (2 * η / C) * s) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [Real.exp_add]; ring

end
end PGM
