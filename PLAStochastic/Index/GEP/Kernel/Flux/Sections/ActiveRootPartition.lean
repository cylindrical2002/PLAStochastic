import PLAStochastic.Index.GEP.Kernel.Flux.Sections.PolyPrimitive

/-!
# Measurable active-root partition

A finite measurable list of candidate roots gives a canonical disjoint
partition even at ties. The selected endpoint pushforward is exactly the sum
of the candidate pushforwards restricted to their active pieces. No independence
of the selector and no unproved boundary-null assertion is needed.
-/

namespace PGM

noncomputable section

open MeasureTheory Set Filter Finset

variable {ι Ω : Type*} [Fintype ι] [LinearOrder ι] [MeasurableSpace Ω]

/-- The first candidate attaining the endpoint; prior ties are excluded. -/
def fluxFirstRoot (E : Ω → ℝ) (F : ι → Ω → ℝ) (q : ι) : Set Ω :=
  {ω | E ω = F q ω ∧ ∀ r, r < q → E ω ≠ F r ω}

theorem measurableSet_fluxFirstRoot {E : Ω → ℝ} {F : ι → Ω → ℝ}
    (hE : Measurable E) (hF : ∀ q, Measurable (F q)) (q : ι) :
    MeasurableSet (fluxFirstRoot E F q) := by
  apply (measurableSet_eq_fun hE (hF q)).inter
  change MeasurableSet {ω : Ω | ∀ r, r < q → E ω ≠ F r ω}
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro r
  by_cases hr : r < q
  · simp only [hr, forall_true_left]
    have he : ({ω | E ω = F r ω}ᶜ : Set Ω) = {ω | E ω ≠ F r ω} := by ext ω; rfl
    rw [← he]
    exact (measurableSet_eq_fun hE (hF r)).compl
  · simp only [hr, false_implies, Set.ofPred_true]
    exact MeasurableSet.univ

omit [MeasurableSpace Ω] [Fintype ι] in
theorem fluxFirstRoot_disjoint (E : Ω → ℝ) (F : ι → Ω → ℝ) :
    Pairwise (fun q r => Disjoint (fluxFirstRoot E F q) (fluxFirstRoot E F r)) := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro ω hq hr
  rcases lt_or_gt_of_ne hqr with h | h
  · exact hr.2 q h hq.1
  · exact hq.2 r h hr.1

omit [MeasurableSpace Ω] in
theorem fluxFirstRoot_exists {E : Ω → ℝ} {F : ι → Ω → ℝ} {ω : Ω}
    (h : ∃ q, E ω = F q ω) : ∃ q, ω ∈ fluxFirstRoot E F q := by
  classical
  let S := Finset.univ.filter (fun q => E ω = F q ω)
  have hS : S.Nonempty := by
    obtain ⟨q, hq⟩ := h
    exact ⟨q, mem_filter.mpr ⟨mem_univ _, hq⟩⟩
  refine ⟨S.min' hS, (mem_filter.mp (S.min'_mem hS)).2, ?_⟩
  intro r hr he
  have hmem : r ∈ S := mem_filter.mpr ⟨mem_univ _, he⟩
  exact (not_lt_of_ge (S.min'_le r hmem)) hr

/-- Decompose the selected endpoint law into the actual candidate-root laws
on a measurable disjoint active partition. -/
theorem flux_map_selected_eq_sum (P : Measure Ω) {S : Set Ω} (hS : MeasurableSet S)
    {E : Ω → ℝ} {F : ι → Ω → ℝ} (hE : Measurable E) (hF : ∀ q, Measurable (F q))
    (hsel : ∀ ω ∈ S, ∃ q, E ω = F q ω) :
    (P.restrict S).map E =
      Measure.sum (fun q => (P.restrict (S ∩ fluxFirstRoot E F q)).map (F q)) := by
  have hm (q : ι) : MeasurableSet (S ∩ fluxFirstRoot E F q) :=
    hS.inter (measurableSet_fluxFirstRoot hE hF q)
  have hd : Pairwise (fun q r => Disjoint (S ∩ fluxFirstRoot E F q) (S ∩ fluxFirstRoot E F r)) :=
    (fluxFirstRoot_disjoint E F).mono fun q r h => h.mono inter_subset_right inter_subset_right
  have hc : (⋃ q, S ∩ fluxFirstRoot E F q) = S := by
    ext ω
    constructor
    · intro hω
      obtain ⟨q, hq⟩ := mem_iUnion.mp hω
      exact hq.1
    · intro hω
      obtain ⟨q, hq⟩ := fluxFirstRoot_exists (hsel ω hω)
      exact mem_iUnion.mpr ⟨q, hω, hq⟩
  have hp := Measure.restrict_iUnion (μ := P) hd hm
  rw [hc] at hp
  rw [hp, Measure.map_sum hE.aemeasurable]
  congr 1
  funext q
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (hm q)] with ω hω
  exact hω.2.1

omit [LinearOrder ι] in
/-- The original facet index need not carry an order: finite enumeration
supplies a canonical measurable disjoint partition. -/
theorem flux_map_selected_eq_sum_fintype (P : Measure Ω) {S : Set Ω} (hS : MeasurableSet S)
    {E : Ω → ℝ} {F : ι → Ω → ℝ} (hE : Measurable E) (hF : ∀ q, Measurable (F q))
    (hsel : ∀ ω ∈ S, ∃ q, E ω = F q ω) :
    (P.restrict S).map E =
      Measure.sum (fun q : Fin (Fintype.card ι) =>
        (P.restrict (S ∩ fluxFirstRoot E (fun r => F ((Fintype.equivFin ι).symm r)) q)).map
          (F ((Fintype.equivFin ι).symm q))) := by
  apply flux_map_selected_eq_sum P hS hE (fun q => hF _)
  intro ω hω
  obtain ⟨q, hq⟩ := hsel ω hω
  exact ⟨Fintype.equivFin ι q, by simpa only [Equiv.symm_apply_apply] using hq⟩

end

end PGM
