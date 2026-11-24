import PLAStochastic.Index.GEP.Kernel.Facet.Ties
import PLAStochastic.Index.GEP.Kernel.Facet.ExplicitEndpointDensity
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.ActiveMeasure

/-!
# Oriented active facets of the actual prefix section

Positive lower endpoints come from negative coefficients; upper endpoints
come from positive coefficients. The first-root partition can be removed
almost everywhere, using uniqueness of positive roots under the actual iid law.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset Filter
open scoped ENNReal

section Poly
variable {ι Ω : Type*} [Fintype ι]

theorem fluxPolyLower_select_neg (c : ι → ℝ) (d : ι → Ω → ℝ) (g : Ω)
    (hx : 0 < fluxPolyLower c d g) :
    ∃ q, c q < 0 ∧ fluxPolyLower c d g = d q g / c q := by
  classical
  unfold fluxPolyLower at hx ⊢
  split_ifs at hx ⊢ with h
  · obtain ⟨q, hq, he⟩ := (fluxNeg c).exists_mem_eq_sup' h (fun q => d q g / c q)
    refine ⟨q, (mem_filter.mp hq).2, ?_⟩
    rw [he] at hx ⊢
    exact max_eq_right (le_of_lt (by
      simpa only [lt_max_iff, lt_self_iff_false, false_or] using hx))
  · exact False.elim (lt_irrefl _ hx)

theorem fluxPolyUpper_select_pos (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (g : Ω) :
    ∃ q, 0 < c q ∧ fluxPolyUpper c d h g = d q g / c q := by
  obtain ⟨q, hq, he⟩ := (fluxPos c).exists_mem_eq_inf' h (fun q => d q g / c q)
  exact ⟨q, (mem_filter.mp hq).2, he⟩

theorem fluxPolyLower_eq_root (c : ι → ℝ) (d : ι → Ω → ℝ) (g : Ω)
    {q : ι} {x : ℝ} (hx : 0 < x) (hc : c q < 0)
    (hr : x = d q g / c q) (hfeas : ∀ p, c p * x ≤ d p g) :
    fluxPolyLower c d g = x := by
  apply le_antisymm
  · exact (fluxPolyLower_le_iff c d g hx.le).mpr fun p _ => hfeas p
  · have hn := (fluxPolyLower_le_iff c d g (fluxPolyLower_nonneg c d g)).mp le_rfl q hc
    rw [hr]
    exact (div_le_iff_of_neg hc).mpr (by simpa only [mul_comm] using hn)

theorem fluxPolyUpper_eq_root (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (g : Ω) {q : ι} {x : ℝ}
    (hc : 0 < c q) (hr : x = d q g / c q) (hfeas : ∀ p, c p * x ≤ d p g) :
    fluxPolyUpper c d h g = x := by
  apply le_antisymm
  · have hp := (le_fluxPolyUpper_iff c d h g (fluxPolyUpper c d h g)).mp le_rfl q hc
    rw [hr]
    exact (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hp)
  · exact (le_fluxPolyUpper_iff c d h g x).mpr fun p _ => hfeas p

theorem fluxPolyLower_active_root_iff (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (g : Ω) {q : ι} {x : ℝ}
    (hx : 0 < x) (hc : c q < 0) (hr : x = d q g / c q) :
    (g ∈ fluxPolyActive c d h ∧ fluxPolyLower c d g = x) ↔
      ∀ p, c p * x ≤ d p g := by
  constructor
  · rintro ⟨⟨hz, hLU⟩, hL⟩
    exact (fluxPoly_iff_interval c d h g hx).mpr ⟨hz, hL.le, hL ▸ hLU⟩
  · intro hf
    have hh := (fluxPoly_iff_interval c d h g hx).mp hf
    exact ⟨⟨hh.1, hh.2.1.trans hh.2.2⟩, fluxPolyLower_eq_root c d g hx hc hr hf⟩

theorem fluxPolyUpper_active_root_iff (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : (fluxPos c).Nonempty) (g : Ω) {q : ι} {x : ℝ}
    (hx : 0 < x) (hc : 0 < c q) (hr : x = d q g / c q) :
    (g ∈ fluxPolyActive c d h ∧ fluxPolyUpper c d h g = x) ↔
      ∀ p, c p * x ≤ d p g := by
  constructor
  · rintro ⟨⟨hz, hLU⟩, hU⟩
    exact (fluxPoly_iff_interval c d h g hx).mpr ⟨hz, hU ▸ hLU, hU.ge⟩
  · intro hf
    have hh := (fluxPoly_iff_interval c d h g hx).mp hf
    exact ⟨⟨hh.1, hh.2.1.trans hh.2.2⟩, fluxPolyUpper_eq_root c d h g hc hr hf⟩

theorem fluxPolyLower_halfLine_root_iff (c : ι → ℝ) (d : ι → Ω → ℝ)
    (h : ¬ (fluxPos c).Nonempty) (g : Ω) {q : ι} {x : ℝ}
    (hx : 0 < x) (hc : c q < 0) (hr : x = d q g / c q) :
    (g ∈ fluxPolyZeroOK c d ∧ fluxPolyLower c d g = x) ↔
      ∀ p, c p * x ≤ d p g := by
  constructor
  · rintro ⟨hz, hL⟩
    exact (fluxPoly_iff_halfLine c d h g hx).mpr ⟨hz, hL.le⟩
  · intro hf
    exact ⟨((fluxPoly_iff_halfLine c d h g hx).mp hf).1,
      fluxPolyLower_eq_root c d g hx hc hr hf⟩

end Poly

theorem fluxFirstRoot_iff_of_unique {ι Ω : Type*} [Fintype ι] [LinearOrder ι]
    (E : Ω → ℝ) (F : ι → Ω → ℝ) (g : Ω)
    (hu : ∀ q p, E g = F q g → E g = F p g → q = p) (q : ι) :
    g ∈ fluxFirstRoot E F q ↔ E g = F q g := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro r hr he
  exact (ne_of_lt hr) (hu r q he h)

theorem kernel_IF_positive_gaps_ae (ν : ProbabilityMeasure ℝ)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) (k i : ℕ) :
    ∀ᵐ g ∂iidLaw ν, ∀ j < k, j ≠ i → 0 < g j := by
  have hall : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving.ae hpos
  exact hall.mono fun g hg j _ _ => hg j

theorem kernel_IF_firstRoot_iff_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hi : i < k) (E : (ℕ → ℝ) → ℝ) (S : Set (ℕ → ℝ))
    (hSpos : ∀ g ∈ S, 0 < E g) :
    ∀ᵐ g ∂iidLaw ν, ∀ q : Fin (Fintype.card (FluxFacetIndex k)), g ∈ S →
      (g ∈ fluxFirstRoot E (kernelEnumeratedRoot eps k i) q ↔
        E g = kernelEnumeratedRoot eps k i q g) := by
  have hu := kernel_positive_root_unique_ae ν hf hν heps hi
    (W := fun _ => 1) measurable_const
  simp only [← Pi.one_def, withDensity_one] at hu
  filter_upwards [hu, kernel_IF_positive_gaps_ae ν hpos k i] with g huniq hg
  intro q hS
  apply fluxFirstRoot_iff_of_unique
  intro r s hr hs
  apply (Fintype.equivFin (FluxFacetIndex k)).symm.injective
  exact huniq hg (E g) (hSpos g hS) _ _ hr hs

theorem kernel_facet_candidate_density_congr_ae (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k)
    {W V : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) (hV : Measurable V)
    (he : W =ᵐ[iidLaw ν] V) :
    kernelFacetCandidateDensity ν f eps k i q W =ᵐ[volume.restrict (Ioi 0)]
      kernelFacetCandidateDensity ν f eps k i q V := by
  apply (withDensity_eq_iff_of_sigmaFinite
    (measurable_kernelFacetCandidateDensity ν hf eps k i q hW).aemeasurable
    (measurable_kernelFacetCandidateDensity ν hf eps k i q hV).aemeasurable).mp
  rw [← restrict_withDensity measurableSet_Ioi, ← restrict_withDensity measurableSet_Ioi,
    ← kernel_facet_root_positive_density ν hf hν eps k i q hW,
    ← kernel_facet_root_positive_density ν hf hν eps k i q hV,
    withDensity_congr_ae he]

theorem kernel_facet_candidate_density_zero (ν : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ≥0∞) (eps : ℝ) (k i : ℕ) (q : FluxFacetIndex k) :
    kernelFacetCandidateDensity ν f eps k i q (fun _ => 0) = 0 := by
  funext x
  unfold kernelFacetCandidateDensity
  split_ifs <;> simp [kernelFacetRootDensity, kernelLinearDensity, kernelIIDRootWeight]

/-- Removing the first-root convention is justified on the original iid path.
The endpoint reward and every facet reward are evaluated after the same insertion.
The conclusion stays in ENNReal and needs no finite-mass assumption on the reward. -/
theorem kernel_IF_selected_density_eq_active_sum (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hi : i < k)
    {E : (ℕ → ℝ) → ℝ} (hE : Measurable E) {S : Set (ℕ → ℝ)} (hS : MeasurableSet S)
    (hSpos : ∀ g ∈ S, 0 < E g) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (hactive : ∀ᵐ g ∂iidLaw ν, ∀ q : FluxFacetIndex k,
      (g ∈ S ∧ E g = kernelFacetRoot eps k i q g) ↔
        (A q ∧ Function.update g i (kernelFacetRoot eps k i q g) ∈ kernelIFPathEvent eps k))
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelSelectedFacetDensity ν f eps k i E S (fun g => W (Function.update g i (E g)))
      =ᵐ[volume.restrict (Ioi 0)]
        fun x => ∑' r : Fin (Fintype.card (FluxFacetIndex k)),
          if A ((Fintype.equivFin (FluxFacetIndex k)).symm r) then
            kernelFacetCandidateDensity ν f eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r)
              (kernelIFActiveWeight eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r) W) x
          else 0 := by
  classical
  have hWE : Measurable (fun g => W (Function.update g i (E g))) :=
    hW.comp ((measurable_update_pair i).comp (hE.prodMk measurable_id))
  have hfirst := kernel_IF_firstRoot_iff_ae ν hf hν hpos heps hi E S hSpos
  have heach (r : Fin (Fintype.card (FluxFacetIndex k))) :
      kernelFacetCandidateDensity ν f eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r)
        ((S ∩ fluxFirstRoot E (kernelEnumeratedRoot eps k i) r).indicator
          (fun g => W (Function.update g i (E g)))) =ᵐ[volume.restrict (Ioi 0)]
      fun x => if A ((Fintype.equivFin (FluxFacetIndex k)).symm r) then
        kernelFacetCandidateDensity ν f eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r)
          (kernelIFActiveWeight eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r) W) x else 0 := by
    let q := (Fintype.equivFin (FluxFacetIndex k)).symm r
    have hweight :
        (S ∩ fluxFirstRoot E (kernelEnumeratedRoot eps k i) r).indicator
          (fun g => W (Function.update g i (E g))) =ᵐ[iidLaw ν]
        (if A q then kernelIFActiveWeight eps k i q W else fun _ => 0) := by
      filter_upwards [hactive, hfirst] with g ha hr
      have he : g ∈ S ∩ fluxFirstRoot E (kernelEnumeratedRoot eps k i) r ↔
          A q ∧ Function.update g i (kernelFacetRoot eps k i q g) ∈ kernelIFPathEvent eps k := by
        rw [mem_inter_iff]
        constructor
        · rintro ⟨hs, hroot⟩
          exact (ha q).mp ⟨hs, (hr r hs).mp hroot⟩
        · intro hh
          obtain ⟨hs, hroot⟩ := (ha q).mpr hh
          exact ⟨hs, (hr r hs).mpr hroot⟩
      by_cases hA : A q
      · rw [if_pos hA]
        by_cases hp : Function.update g i (kernelFacetRoot eps k i q g) ∈ kernelIFPathEvent eps k
        · have hs := he.mpr ⟨hA, hp⟩
          have hroot := (ha q).mpr ⟨hA, hp⟩ |>.2
          simp only [indicator_of_mem hs, kernelIFActiveWeight, kernelIFPathWeight,
            indicator_of_mem hp, hroot]
        · rw [indicator_of_notMem (fun hs => hp (he.mp hs).2)]
          exact (indicator_of_notMem hp W).symm
      · rw [if_neg hA, indicator_of_notMem (fun hs => hA (he.mp hs).1)]
    have hm := hWE.indicator
      (hS.inter (measurableSet_fluxFirstRoot hE (measurable_kernelEnumeratedRoot eps k i) r))
    have hv : Measurable (if A q then kernelIFActiveWeight eps k i q W else fun _ => 0) := by
      split_ifs
      · exact measurable_kernelIFActiveWeight eps k i q hW
      · exact measurable_const
    have hh := kernel_facet_candidate_density_congr_ae ν hf hν eps k i q hm hv hweight
    change _ =ᵐ[volume.restrict (Ioi 0)] (fun x => if A q then
      kernelFacetCandidateDensity ν f eps k i q (kernelIFActiveWeight eps k i q W) x else 0)
    by_cases hA : A q
    · simpa only [if_pos hA] using hh
    · filter_upwards [hh] with x hx
      simpa only [if_neg hA, kernel_facet_candidate_density_zero, Pi.zero_apply] using hx
  have hall := ae_all_iff.mpr heach
  filter_upwards [hall] with x hx
  unfold kernelSelectedFacetDensity
  simp only [tsum_fintype, Finset.sum_apply]
  exact Finset.sum_congr rfl fun r _ => hx r

/-- The positive part of the true lower section endpoint, including half-lines. -/
def kernelIFLowerSection (eps : ℝ) (k i : ℕ) : Set (ℕ → ℝ) :=
  (if h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty then
    fluxPolyActive (fun q : FluxFacetIndex k => fluxFacetCoef eps q i) (fluxPrefixRHS eps k i) h
  else fluxPolyZeroOK (fun q : FluxFacetIndex k => fluxFacetCoef eps q i) (fluxPrefixRHS eps k i)) ∩
    (kernelPrefixLower eps k i) ⁻¹' Ioi 0

def kernelIFUpperSection (eps : ℝ) (k i : ℕ)
    (h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty) :
    Set (ℕ → ℝ) :=
  fluxPolyActive (fun q : FluxFacetIndex k => fluxFacetCoef eps q i) (fluxPrefixRHS eps k i) h ∩
    (kernelPrefixUpper eps k i h) ⁻¹' Ioi 0

theorem measurableSet_kernelIFLowerSection (eps : ℝ) (k i : ℕ) :
    MeasurableSet (kernelIFLowerSection eps k i) := by
  unfold kernelIFLowerSection
  apply MeasurableSet.inter
  · split_ifs with h
    · exact measurableSet_fluxPolyActive _ (measurable_fluxPrefixRHS eps k i) h
    · exact measurableSet_fluxPolyZeroOK _ (measurable_fluxPrefixRHS eps k i)
  · exact (measurable_fluxPolyLower _ (measurable_fluxPrefixRHS eps k i)) measurableSet_Ioi

theorem measurableSet_kernelIFUpperSection (eps : ℝ) (k i : ℕ)
    (h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty) :
    MeasurableSet (kernelIFUpperSection eps k i h) :=
  (measurableSet_fluxPolyActive _ (measurable_fluxPrefixRHS eps k i) h).inter
    ((measurable_fluxPolyUpper _ (measurable_fluxPrefixRHS eps k i) h) measurableSet_Ioi)

theorem kernel_IF_update_event_iff {eps x : ℝ} {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    (g : ℕ → ℝ) (hg : ∀ j < k, j ≠ i → 0 < g j) :
    Function.update g i x ∈ kernelIFPathEvent eps k ↔
      0 < x ∧ ∀ q : FluxFacetIndex k, fluxFacetCoef eps q i * x ≤ fluxPrefixRHS eps k i q g := by
  constructor
  · intro h
    have hx : 0 < x := by simpa only [Function.update_self] using h.1 i hi
    exact ⟨hx, (flux_prefix_update_iff hk hi hx hg).mp h.2⟩
  · rintro ⟨hx, hfeas⟩
    refine ⟨?_, (flux_prefix_update_iff hk hi hx hg).mpr hfeas⟩
    intro j hj
    by_cases hji : j = i
    · subst j
      simpa only [Function.update_self] using hx
    · simpa only [Function.update_of_ne hji] using hg j hj hji

theorem kernel_IF_lower_root_iff {eps : ℝ} {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    (g : ℕ → ℝ) (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hu : ∀ x : ℝ, 0 < x → ∀ q p : FluxFacetIndex k,
      x = kernelFacetRoot eps k i q g → x = kernelFacetRoot eps k i p g → q = p)
    (q : FluxFacetIndex k) :
    (g ∈ kernelIFLowerSection eps k i ∧ kernelPrefixLower eps k i g = kernelFacetRoot eps k i q g) ↔
      (fluxFacetCoef eps q i < 0 ∧
        Function.update g i (kernelFacetRoot eps k i q g) ∈ kernelIFPathEvent eps k) := by
  let c := fun p : FluxFacetIndex k => fluxFacetCoef eps p i
  let d := fluxPrefixRHS eps k i
  constructor
  · rintro ⟨⟨hS, hLpos⟩, hr⟩
    obtain ⟨p, hpc, hp⟩ := fluxPolyLower_select_neg c d g hLpos
    have hqp : q = p := hu _ hLpos q p hr hp
    have hc : c q < 0 := hqp ▸ hpc
    have hx : 0 < kernelFacetRoot eps k i q g := hr ▸ hLpos
    refine ⟨hc, (kernel_IF_update_event_iff hk hi g hg).mpr ⟨hx, ?_⟩⟩
    by_cases h : (fluxPos c).Nonempty
    · have hs : g ∈ fluxPolyActive c d h := by
        simpa only [show (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty from h,
          dite_true] using hS
      exact (fluxPolyLower_active_root_iff c d h g hx hc rfl).mp ⟨hs, hr⟩
    · have hs : g ∈ fluxPolyZeroOK c d := by
        simpa only [show ¬ (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty from h,
          dite_false] using hS
      exact (fluxPolyLower_halfLine_root_iff c d h g hx hc rfl).mp ⟨hs, hr⟩
  · rintro ⟨hc, hpath⟩
    obtain ⟨hx, hf⟩ := (kernel_IF_update_event_iff hk hi g hg).mp hpath
    have hr := fluxPolyLower_eq_root c d g hx hc rfl hf
    refine ⟨⟨?_, ?_⟩, hr⟩
    swap
    · change 0 < fluxPolyLower c d g
      rwa [hr]
    by_cases h : (fluxPos c).Nonempty
    · have hs := ((fluxPolyLower_active_root_iff c d h g hx hc rfl).mpr hf).1
      simpa only [show (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty from h,
        dite_true] using hs
    · have hs := ((fluxPolyLower_halfLine_root_iff c d h g hx hc rfl).mpr hf).1
      simpa only [show ¬ (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty from h,
        dite_false] using hs

theorem kernel_IF_upper_root_iff {eps : ℝ} {k i : ℕ} (hk : 2 ≤ k) (hi : i < k)
    (h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty)
    (g : ℕ → ℝ) (hg : ∀ j < k, j ≠ i → 0 < g j)
    (hu : ∀ x : ℝ, 0 < x → ∀ q p : FluxFacetIndex k,
      x = kernelFacetRoot eps k i q g → x = kernelFacetRoot eps k i p g → q = p)
    (q : FluxFacetIndex k) :
    (g ∈ kernelIFUpperSection eps k i h ∧ kernelPrefixUpper eps k i h g = kernelFacetRoot eps k i q g) ↔
      (0 < fluxFacetCoef eps q i ∧
        Function.update g i (kernelFacetRoot eps k i q g) ∈ kernelIFPathEvent eps k) := by
  let c := fun p : FluxFacetIndex k => fluxFacetCoef eps p i
  let d := fluxPrefixRHS eps k i
  constructor
  · rintro ⟨⟨hS, hUpos⟩, hr⟩
    obtain ⟨p, hpc, hp⟩ := fluxPolyUpper_select_pos c d h g
    have hqp : q = p := hu _ hUpos q p hr hp
    have hc : 0 < c q := hqp ▸ hpc
    have hx : 0 < kernelFacetRoot eps k i q g := hr ▸ hUpos
    exact ⟨hc, (kernel_IF_update_event_iff hk hi g hg).mpr
      ⟨hx, (fluxPolyUpper_active_root_iff c d h g hx hc rfl).mp ⟨hS, hr⟩⟩⟩
  · rintro ⟨hc, hpath⟩
    obtain ⟨hx, hf⟩ := (kernel_IF_update_event_iff hk hi g hg).mp hpath
    obtain ⟨hS, hr⟩ := (fluxPolyUpper_active_root_iff c d h g hx hc rfl).mpr hf
    refine ⟨⟨hS, ?_⟩, hr⟩
    change 0 < fluxPolyUpper c d h g
    rwa [hr]

def kernelIFOrientedDensity (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ≥0∞)
    (eps : ℝ) (k i : ℕ) (A : FluxFacetIndex k → Prop) [DecidablePred A]
    (W : (ℕ → ℝ) → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ∑' r : Fin (Fintype.card (FluxFacetIndex k)),
    if A ((Fintype.equivFin (FluxFacetIndex k)).symm r) then
      kernelFacetCandidateDensity ν f eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r)
        (kernelIFActiveWeight eps k i ((Fintype.equivFin (FluxFacetIndex k)).symm r) W) x else 0

theorem measurable_kernelIFOrientedDensity (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (eps : ℝ) (k i : ℕ)
    (A : FluxFacetIndex k → Prop) [DecidablePred A]
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    Measurable (kernelIFOrientedDensity ν f eps k i A W) := by
  unfold kernelIFOrientedDensity
  simp only [tsum_fintype]
  apply Finset.measurable_sum
  intro r _
  split_ifs
  · exact measurable_kernelFacetCandidateDensity ν hf eps k i _
      (measurable_kernelIFActiveWeight eps k i _ hW)
  · exact measurable_const

theorem kernel_IF_lower_density_eq_active_sum (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hk : 2 ≤ k) (hi : i < k)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelSelectedFacetDensity ν f eps k i (kernelPrefixLower eps k i)
      (kernelIFLowerSection eps k i) (fun g => W (Function.update g i (kernelPrefixLower eps k i g)))
      =ᵐ[volume.restrict (Ioi 0)]
        kernelIFOrientedDensity ν f eps k i (fun q => fluxFacetCoef eps q i < 0) W := by
  unfold kernelIFOrientedDensity
  apply kernel_IF_selected_density_eq_active_sum ν hf hν hpos heps hi
    (measurable_fluxPolyLower _ (measurable_fluxPrefixRHS eps k i))
    (measurableSet_kernelIFLowerSection eps k i) (fun _ h => h.2)
    (fun q => fluxFacetCoef eps q i < 0) ?_ hW
  have hu := kernel_positive_root_unique_ae ν hf hν heps hi (W := fun _ => 1) measurable_const
  simp only [← Pi.one_def, withDensity_one] at hu
  filter_upwards [hu, kernel_IF_positive_gaps_ae ν hpos k i] with g huniq hg
  exact kernel_IF_lower_root_iff hk hi g hg (huniq hg)

theorem kernel_IF_upper_density_eq_active_sum (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) (hν : (ν : Measure ℝ) = volume.withDensity f)
    (hpos : ∀ᵐ x ∂(ν : Measure ℝ), 0 < x) {eps : ℝ} {k i : ℕ}
    (heps : 0 < eps) (hk : 2 ≤ k) (hi : i < k)
    (h : (fluxPos (fun q : FluxFacetIndex k => fluxFacetCoef eps q i)).Nonempty)
    {W : (ℕ → ℝ) → ℝ≥0∞} (hW : Measurable W) :
    kernelSelectedFacetDensity ν f eps k i (kernelPrefixUpper eps k i h)
      (kernelIFUpperSection eps k i h) (fun g => W (Function.update g i (kernelPrefixUpper eps k i h g)))
      =ᵐ[volume.restrict (Ioi 0)]
        kernelIFOrientedDensity ν f eps k i (fun q => 0 < fluxFacetCoef eps q i) W := by
  unfold kernelIFOrientedDensity
  apply kernel_IF_selected_density_eq_active_sum ν hf hν hpos heps hi
    (measurable_fluxPolyUpper _ (measurable_fluxPrefixRHS eps k i) h)
    (measurableSet_kernelIFUpperSection eps k i h) (fun _ hg => hg.2)
    (fun q => 0 < fluxFacetCoef eps q i) ?_ hW
  have hu := kernel_positive_root_unique_ae ν hf hν heps hi (W := fun _ => 1) measurable_const
  simp only [← Pi.one_def, withDensity_one] at hu
  filter_upwards [hu, kernel_IF_positive_gaps_ae ν hpos k i] with g huniq hg
  exact kernel_IF_upper_root_iff hk hi h g hg (huniq hg)

end
end PGM
