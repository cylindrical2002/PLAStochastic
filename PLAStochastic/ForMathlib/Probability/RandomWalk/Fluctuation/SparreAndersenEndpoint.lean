import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SparreAndersenIID

/-!
# Sparre Andersen with the terminal position retained

The permutation bijection preserves the sum of all increments. Consequently,
the first argmax and the number of positive partial sums have the same joint
law with the terminal position. No Gaussian or nonlattice assumption is used.
-/

noncomputable section

open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal List

namespace SwingRepair.Fluctuation

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : ℕ → Ω → ℝ} {ν : Measure ℝ}

/-- The combinatorial identity retains any condition on the terminal sum. -/
theorem measure_posCount_endpoint_eq_measure_isFirstArgmax_endpoint [IsProbabilityMeasure μ]
    (hY : ∀ i, Measurable (Y i)) (hi : iIndepFun Y μ) (hν : ∀ i, μ.map (Y i) = ν)
    (n k : ℕ) {B : Set ℝ} (hB : MeasurableSet B) :
    μ {w | posCount (fun i => Y i w) (List.range n) = k ∧
        ((List.range n).map fun i => Y i w).sum ∈ B} =
      μ {w | IsFirstArgmax (fun i => Y i w) (List.range n) k ∧
        ((List.range n).map fun i => Y i w).sum ∈ B} := by
  set P := (List.range n).permutations.toFinset with hPdef
  have hP : ∀ p, p ∈ P ↔ p ~ List.range n := mem_permutations_range_iff n
  let QN : List ℝ → Prop := fun l => posCount id l = k ∧ l.sum ∈ B
  let QT : List ℝ → Prop := fun l => IsFirstArgmax id l k ∧ l.sum ∈ B
  have hm : Measurable (fun v : Fin n → ℝ => (List.ofFn v).sum) := by
    have he : (fun v : Fin n → ℝ => (List.ofFn v).sum) =
        fun v => psum id (List.ofFn v) n := by
      funext v
      simpa only [List.length_ofFn, List.map_id] using (psum_length id (List.ofFn v)).symm
    rw [he]
    exact measurable_psum_ofFn n n
  have hQN : MeasurableSet {v : Fin n → ℝ | QN (List.ofFn v)} := by
    exact (measurableSet_posCount_ofFn n k).inter (hB.preimage hm)
  have hQT : MeasurableSet {v : Fin n → ℝ | QT (List.ofFn v)} := by
    exact (measurableSet_isFirstArgmax_ofFn n k).inter (hB.preimage hm)
  have hN : ∀ p ∈ P, μ {w | QN (p.map fun i => Y i w)} =
      (Measure.pi fun _ : Fin n => ν) {v | QN (List.ofFn v)} := fun p hp =>
    measure_list_pred_eq hY hi hν QN hQN p (length_of_perm_range ((hP p).mp hp))
      (nodup_of_perm_range ((hP p).mp hp))
  have hT : ∀ p ∈ P, μ {w | QT (p.map fun i => Y i w)} =
      (Measure.pi fun _ : Fin n => ν) {v | QT (List.ofFn v)} := fun p hp =>
    measure_list_pred_eq hY hi hν QT hQT p (length_of_perm_range ((hP p).mp hp))
      (nodup_of_perm_range ((hP p).mp hp))
  have hsum : ∑ p ∈ P, μ {w | QN (p.map fun i => Y i w)} =
      ∑ p ∈ P, μ {w | QT (p.map fun i => Y i w)} := by
    rw [sum_measure_list_pred hY QN hQN, sum_measure_list_pred hY QT hQT, ← hPdef]
    congr 1
    funext w
    congr 1
    have hterminal : ∀ p ∈ P, (p.map fun i => Y i w).sum =
        ((List.range n).map fun i => Y i w).sum := fun p hp =>
      (((hP p).mp hp).map (fun i => Y i w)).sum_eq
    have key := card_posCount_eq_card_isFirstArgmax (fun i => Y i w) hP k
    rw [Finset.card_filter, Finset.card_filter] at key ⊢
    by_cases hb : ((List.range n).map fun i => Y i w).sum ∈ B
    · refine (Finset.sum_congr rfl fun p hp => ?_).trans
        (key.trans (Finset.sum_congr rfl fun p hp => ?_))
      · by_cases h : posCount (fun i => Y i w) p = k <;>
          simp [QN, posCount_map, hterminal p hp, hb, h]
      · by_cases h : IsFirstArgmax (fun i => Y i w) p k <;>
          simp [QT, isFirstArgmax_map_iff, hterminal p hp, hb, h]
    · rw [Finset.sum_eq_zero fun p hp => by simp [QN, hterminal p hp, hb],
        Finset.sum_eq_zero fun p hp => by simp [QT, hterminal p hp, hb]]
  rw [Finset.sum_congr rfl hN, Finset.sum_congr rfl hT, Finset.sum_const, Finset.sum_const] at hsum
  have hcard : (P.card : ℝ≥0∞) ≠ 0 := by
    have hr : List.range n ∈ P := (hP _).mpr (List.Perm.refl _)
    exact_mod_cast (Finset.card_pos.mpr ⟨_, hr⟩).ne'
  have hpi : (Measure.pi fun _ : Fin n => ν) {v | QN (List.ofFn v)} =
      (Measure.pi fun _ : Fin n => ν) {v | QT (List.ofFn v)} := by
    simp only [nsmul_eq_mul] at hsum
    exact (ENNReal.mul_right_inj hcard (ENNReal.natCast_ne_top _)).mp hsum
  have hr : List.range n ∈ P := (hP _).mpr (List.Perm.refl _)
  have eN := hN _ hr
  have eT := hT _ hr
  simp only [QN, QT, posCount_map, isFirstArgmax_map_iff] at eN eT
  rw [eN, eT]
  exact hpi

end SwingRepair.Fluctuation
