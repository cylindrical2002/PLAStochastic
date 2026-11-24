import PLAStochastic.Index.GEP.Kernel.Flux.Sections.IntervalPrimitive
import PLAStochastic.Index.GEP.SurvivalBound.Certificate.NullTies

/-!
# WP4: absolute continuity of linear section endpoints

A finite linear form of independent real coordinates has an absolutely continuous
law as soon as one nonzero coefficient multiplies an absolutely continuous coordinate.
The remaining coordinates need not have densities. A measurable selector among
countably many such forms has the same property, even if the selector depends on
every coordinate. These facts justify the absolute-continuity step after actual
polyhedral section endpoints have been represented as selected linear forms.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset

theorem flux_map_mul_ac {μ : Measure ℝ} (hμ : μ ≪ volume) {a : ℝ} (ha : a ≠ 0) :
    μ.map (fun x => a * x) ≪ volume := by
  apply (hμ.map (measurable_const.mul measurable_id)).trans
  change volume.map (fun x : ℝ => a * x) ≪ volume
  rw [Real.map_volume_mul_left ha]
  exact Measure.smul_absolutelyContinuous

/-- Genuine absolute continuity of a finite linear form, stronger than absence
of atoms and sufficient to obtain an integral primitive for the CDF. -/
theorem flux_infinitePi_linear_ac {μ : ℕ → Measure ℝ} [∀ l, IsProbabilityMeasure (μ l)]
    {T : Finset ℕ} {c : ℕ → ℝ} {m : ℕ} (hm : m ∈ T) (hcm : c m ≠ 0) (hac : μ m ≪ volume) :
    (Measure.infinitePi μ).map (fun g : ℕ → ℝ => ∑ l ∈ T, c l * g l) ≪ volume := by
  have hind : iIndepFun (fun l (g : ℕ → ℝ) => c l * g l) (Measure.infinitePi μ) :=
    (iIndepFun_infinitePi (P := μ) (X := fun _ x => x) fun _ => measurable_id).comp
      (fun l x => c l * x) fun _ => measurable_const.mul measurable_id
  have hmeas : ∀ l, Measurable fun g : ℕ → ℝ => c l * g l :=
    fun l => measurable_const.mul (measurable_pi_apply l)
  have hsum := hind.indepFun_finsetSum_of_notMem hmeas (Finset.notMem_erase m T)
  have hYfun : (∑ l ∈ T.erase m, fun g : ℕ → ℝ => c l * g l) =
      fun g => ∑ l ∈ T.erase m, c l * g l := by
    funext g
    exact Finset.sum_apply g _ _
  rw [hYfun] at hsum
  have hY : Measurable fun g : ℕ → ℝ => ∑ l ∈ T.erase m, c l * g l :=
    Finset.measurable_sum _ fun l _ => hmeas l
  have hV := hmeas m
  have hfull : (fun g : ℕ → ℝ => ∑ l ∈ T, c l * g l) =
      fun g => (∑ l ∈ T.erase m, c l * g l) + c m * g m := by
    funext g
    exact (Finset.sum_erase_add T _ hm).symm
  rw [hfull]
  change (Measure.infinitePi μ).map
    ((fun g : ℕ → ℝ => ∑ l ∈ T.erase m, c l * g l) + (fun g => c m * g m)) ≪ volume
  rw [hsum.map_add_eq_map_conv_map hY hV]
  apply Measure.conv_absolutelyContinuous
  have he : (Measure.infinitePi μ).map (fun g : ℕ → ℝ => c m * g m) =
      (μ m).map (fun x => c m * x) := by
    rw [← Measure.infinitePi_map_eval μ m]
    exact (Measure.map_map (show Measurable (fun x : ℝ => c m * x) from
      measurable_const.mul measurable_id) (measurable_pi_apply m)).symm
  rw [he]
  exact flux_map_mul_ac hac hcm

/-- The same result for the mixed product laws used by the WP4 complex expansion. -/
theorem flux_wordLaw_linear_ac {ν σ : ProbabilityMeasure ℝ}
    (hν : (ν : Measure ℝ) ≪ volume) (hσ : (σ : Measure ℝ) ≪ volume)
    (S : Finset ℕ) {T : Finset ℕ} {c : ℕ → ℝ} {m : ℕ}
    (hm : m ∈ T) (hcm : c m ≠ 0) :
    (wordLaw ν σ S).map (fun g : ℕ → ℝ => ∑ l ∈ T, c l * g l) ≪ volume := by
  unfold wordLaw
  apply flux_infinitePi_linear_ac hm hcm
  by_cases h : m ∈ S
  · simpa only [h, if_true] using hσ
  · simpa only [h, if_false] using hν

/-- Section endpoints selected from nondegenerate linear candidates have
absolutely continuous laws. The selector may be a minimum or maximum, with ties. -/
theorem flux_selected_linear_endpoint_ac {μ : ℕ → Measure ℝ}
    [∀ l, IsProbabilityMeasure (μ l)] {ι : Type*} [Countable ι]
    (T : ι → Finset ℕ) (c : ι → ℕ → ℝ) {E : (ℕ → ℝ) → ℝ}
    (hE : Measurable E)
    (hnd : ∀ i, ∃ m ∈ T i, c i m ≠ 0 ∧ μ m ≪ volume)
    (hsel : ∀ᵐ g ∂(Measure.infinitePi μ), ∃ i, E g = ∑ l ∈ T i, c i l * g l) :
    (Measure.infinitePi μ).map E ≪ volume := by
  refine fluxEndpoint_ac_of_countable_selection (Measure.infinitePi μ)
    (fun i => Finset.measurable_sum _ fun l _ => measurable_const.mul (measurable_pi_apply l))
    hE ?_ hsel
  intro i
  obtain ⟨m, hm, hcm, hac⟩ := hnd i
  exact flux_infinitePi_linear_ac hm hcm hac

/-- Positive-local form: values at zero may represent a fixed boundary or an
empty section; every positive value must be a nondegenerate linear candidate. -/
theorem flux_selected_linear_endpoint_ac_positive {μ : ℕ → Measure ℝ}
    [∀ l, IsProbabilityMeasure (μ l)] {ι : Type*} [Countable ι]
    (T : ι → Finset ℕ) (c : ι → ℕ → ℝ) {E : (ℕ → ℝ) → ℝ}
    (hE : Measurable E)
    (hnd : ∀ i, ∃ m ∈ T i, c i m ≠ 0 ∧ μ m ≪ volume)
    (hsel : ∀ᵐ g ∂(Measure.infinitePi μ), 0 < E g → ∃ i, E g = ∑ l ∈ T i, c i l * g l) :
    ((Measure.infinitePi μ).map E).restrict (Set.Ioi 0) ≪ volume := by
  refine fluxEndpoint_ac_positive_of_countable_selection (Measure.infinitePi μ)
    (fun i => Finset.measurable_sum _ fun l _ => measurable_const.mul (measurable_pi_apply l))
    hE ?_ hsel
  intro i
  obtain ⟨m, hm, hcm, hac⟩ := hnd i
  exact flux_infinitePi_linear_ac hm hcm hac

/-- A spatial facet crossing has the form `r * B - A_rest`: the second block
contains a smoothing coordinate independent of all remaining first-block gaps.
This proves the endpoint law is absolutely continuous without differentiating
any input density. -/
theorem flux_block_endpoint_ac {μ : ℕ → Measure ℝ} [∀ l, IsProbabilityMeasure (μ l)]
    {I J : Finset ℕ} (hIJ : Disjoint I J) {m : ℕ} (hm : m ∈ J)
    (hac : μ m ≪ volume) {r : ℝ} (hr : r ≠ 0) :
    (Measure.infinitePi μ).map
      (fun g : ℕ → ℝ => r * (∑ l ∈ J, g l) - ∑ l ∈ I, g l) ≪ volume := by
  classical
  let c : ℕ → ℝ := fun l => if l ∈ J then r else -1
  have he : (fun g : ℕ → ℝ => r * (∑ l ∈ J, g l) - ∑ l ∈ I, g l) =
      fun g => ∑ l ∈ I ∪ J, c l * g l := by
    funext g
    rw [Finset.sum_union hIJ]
    have hI : (∑ l ∈ I, c l * g l) = -(∑ l ∈ I, g l) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      have hlJ : l ∉ J := fun h => Finset.disjoint_left.mp hIJ hl h
      simp only [c, hlJ, if_false, neg_one_mul]
    have hJ : (∑ l ∈ J, c l * g l) = r * ∑ l ∈ J, g l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l hl => by simp only [c, hl, if_true]
    rw [hI, hJ]
    ring
  rw [he]
  exact flux_infinitePi_linear_ac (Finset.mem_union_right I hm)
    (by simpa only [c, hm, if_true] using hr) hac

end

end PGM
