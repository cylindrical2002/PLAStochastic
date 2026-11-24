import PLAStochastic.Index.KEP.Poisson.ArrivalWindowSlices

/-!
# Finiteness and measurability of the actual arrival-window count

The first exponential partial sum above a fixed time defines the window
count. Exact disjoint window slices sum to the full Poisson probability
mass, proving finite crossing almost surely without adding a divergence
assumption. All count fibers and the padded configuration are measurable.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open Classical MeasureTheory ProbabilityTheory Set Renyi Function
open scoped ENNReal Nat

def kepArrivalCount (s : ℝ) (g : ℕ → ℝ) : ℕ :=
  if h : ∃ k : ℕ, s < gapKeys g (k + 1) then Nat.find h else 0

theorem kepArrivalCount_eq_iff (s : ℝ) (g : ℕ → ℝ) (k : ℕ) :
    kepArrivalCount s g = k ↔ g ∈ kepArrivalCountEvent s k ∨
      (k = 0 ∧ ¬ ∃ r : ℕ, s < gapKeys g (r + 1)) := by
  unfold kepArrivalCount
  by_cases h : ∃ r : ℕ, s < gapKeys g (r + 1)
  · rw [dif_pos h, Nat.find_eq_iff]
    have hf : (∀ i : Fin k, gapKeys g ((i : ℕ) + 1) ≤ s) ↔
        ∀ r < k, ¬ s < gapKeys g (r + 1) := by
      constructor
      · intro hi r hr
        exact not_lt.mpr (hi ⟨r, hr⟩)
      · intro hi i
        exact not_lt.mp (hi i i.isLt)
    simp only [kepArrivalCountEvent, mem_ofPred_eq, hf]
    tauto
  · rw [dif_neg h]
    have hnot : g ∉ kepArrivalCountEvent s k := fun hg => h ⟨k, hg.2⟩
    simp only [hnot, false_or, h, not_false_eq_true, and_true, eq_comm]

theorem measurable_kepArrivalCount (s : ℝ) : Measurable (kepArrivalCount s) := by
  have hhit : MeasurableSet {g : ℕ → ℝ | ∃ r : ℕ, s < gapKeys g (r + 1)} := by
    simpa only [Set.ofPred_exists, Function.comp_apply] using MeasurableSet.iUnion fun r : ℕ =>
      measurableSet_lt (measurable_const (a := s))
        ((measurable_pi_apply (r + 1)).comp measurable_gapKeys)
  have hfiber (k : ℕ) : MeasurableSet {g : ℕ → ℝ | kepArrivalCount s g = k} := by
    have he : {g : ℕ → ℝ | kepArrivalCount s g = k} =
        kepArrivalCountEvent s k ∪
          ({g : ℕ → ℝ | k = 0} ∩ {g | ¬ ∃ r : ℕ, s < gapKeys g (r + 1)}) := by
      ext g
      exact kepArrivalCount_eq_iff s g k
    rw [he]
    have hk0 : MeasurableSet {g : ℕ → ℝ | k = 0} := by
      by_cases h : k = 0 <;> simp [h]
    exact (measurableSet_kepArrivalCountEvent s k).union (hk0.inter hhit.compl)
  intro A _
  have he : kepArrivalCount s ⁻¹' A =
      ⋃ k : ℕ, ⋃ (_ : k ∈ A), {g : ℕ → ℝ | kepArrivalCount s g = k} := by
    ext g
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    exact ⟨fun hg => ⟨kepArrivalCount s g, hg, rfl⟩,
      fun ⟨k, hk, hg⟩ => hg ▸ hk⟩
  rw [he]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hfiber k

theorem kepArrivalCountEvent_pairwise (s : ℝ) :
    Pairwise (Disjoint on kepArrivalCountEvent s) := by
  intro k l hkl
  change Disjoint (kepArrivalCountEvent s k) (kepArrivalCountEvent s l)
  rw [Set.disjoint_left]
  intro g hk hl
  rcases lt_or_gt_of_ne hkl with h | h
  · exact (not_lt.mpr (hl.1 ⟨k, h⟩)) hk.2
  · exact (not_lt.mpr (hk.1 ⟨l, h⟩)) hl.2

theorem expSeqMeasure_arrival_count_event {s : ℝ} (hs : 0 < s) (k : ℕ) :
    expSeqMeasure (kepArrivalCountEvent s k) = (poissonMeasure ⟨s, hs.le⟩) {k} := by
  simpa only [preimage_univ, inter_univ, measure_univ, mul_one] using
    expSeqMeasure_arrival_window hs k MeasurableSet.univ

theorem kepArrivalCount_ae_spec {s : ℝ} (hs : 0 < s) :
    ∀ᵐ g ∂expSeqMeasure, g ∈ kepArrivalCountEvent s (kepArrivalCount s g) := by
  have hsingle : Pairwise (Disjoint on fun k : ℕ => ({k} : Set ℕ)) := by
    intro k l hkl
    exact disjoint_singleton.mpr hkl
  have hsum : (∑' k : ℕ, (poissonMeasure ⟨s, hs.le⟩) {k}) = 1 := by
    rw [← measure_iUnion hsingle (fun k => measurableSet_singleton k)]
    have hu : (⋃ k : ℕ, ({k} : Set ℕ)) = univ := by ext k; simp
    rw [hu, measure_univ]
  have hmeas : MeasurableSet (⋃ k : ℕ, kepArrivalCountEvent s k) :=
    MeasurableSet.iUnion fun k => measurableSet_kepArrivalCountEvent s k
  have hmass : expSeqMeasure (⋃ k : ℕ, kepArrivalCountEvent s k) = 1 := by
    rw [measure_iUnion (kepArrivalCountEvent_pairwise s)
      (fun k => measurableSet_kepArrivalCountEvent s k)]
    simpa only [expSeqMeasure_arrival_count_event hs] using hsum
  have hae : ∀ᵐ g ∂expSeqMeasure, g ∈ ⋃ k : ℕ, kepArrivalCountEvent s k := by
    rw [ae_iff]
    change expSeqMeasure (⋃ k : ℕ, kepArrivalCountEvent s k)ᶜ = 0
    rw [measure_compl hmeas (measure_ne_top _ _), hmass, measure_univ, tsub_self]
  filter_upwards [hae] with g hg
  obtain ⟨k, hk⟩ := mem_iUnion.mp hg
  have he := (kepArrivalCount_eq_iff s g k).mpr (Or.inl hk)
  rwa [he]

def kepArrivalWindowConfiguration (s p : ℝ) (g : ℕ → ℝ) : ℕ × (ℕ → ℝ) :=
  (kepArrivalCount s g, padScale p (kepArrivalWindowCoordinates s (kepArrivalCount s g) g))

theorem measurable_kepArrivalWindowConfiguration (s p : ℝ) :
    Measurable (kepArrivalWindowConfiguration s p) := by
  apply (measurable_kepArrivalCount s).prodMk
  apply measurable_pi_lambda
  intro t
  unfold padScale padFin kepArrivalWindowCoordinates
  have ht : MeasurableSet {g : ℕ → ℝ | t < kepArrivalCount s g} :=
    measurableSet_lt measurable_const (measurable_kepArrivalCount s)
  exact Measurable.ite ht
    (((measurable_pi_apply (t + 1)).comp measurable_gapKeys).const_mul s⁻¹ |>.const_mul p)
    measurable_const

end

end PGM
