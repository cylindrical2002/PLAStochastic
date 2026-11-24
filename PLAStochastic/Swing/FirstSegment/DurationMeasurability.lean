import PLAStochastic.Swing.DenseSampling.PostFirst.ToleranceRescaling

/-! # Measurability of the actual untruncated first recording duration -/
noncomputable section
open Classical
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- The least selected natural number, with zero for the empty selection,
is measurable whenever all individual selection events are measurable. -/
theorem measurable_nat_sInf_of_measurable_events {Ω : Type*} [MeasurableSpace Ω]
    (P : Ω → ℕ → Prop) (hP : ∀ n, MeasurableSet {ω | P ω n}) :
    Measurable (fun ω => sInf {n : ℕ | P ω n}) := by
  apply measurable_to_countable'
  intro n
  have he : {ω | sInf {j : ℕ | P ω j} = n} =
      ({ω | P ω n} ∩ {ω | ∀ j < n, ¬ P ω j}) ∪
        ({ω | ∀ j, ¬ P ω j} ∩ {ω : Ω | n = 0}) := by
    ext ω
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases hp : ({j : ℕ | P ω j} : Set ℕ).Nonempty
    · rw [csInf_eq_iff hp]
      constructor
      · rintro ⟨hn, hle⟩
        exact Or.inl ⟨hn, fun j hj hjP => (not_le.mpr hj) (hle j hjP)⟩
      · rintro (⟨hn, hl⟩ | ⟨hz, _⟩)
        · exact ⟨hn, fun j hj => le_of_not_gt (fun hlt => hl j hlt hj)⟩
        · obtain ⟨j, hj⟩ := hp
          exact False.elim (hz j hj)
    · have hz : ∀ j, ¬ P ω j := by simpa only [Set.nonempty_def, Set.mem_ofPred_eq, not_exists] using hp
      have hset : {j : ℕ | P ω j} = ∅ := Set.eq_empty_iff_forall_notMem.mpr hz
      rw [hset, Nat.sInf_empty]
      simp only [hz, false_and, false_or, forall_const, not_false_eq_true, true_and, eq_comm]
  change MeasurableSet {ω | sInf {j : ℕ | P ω j} = n}
  rw [he]
  apply MeasurableSet.union
  · apply (hP n).inter
    simp only [Set.ofPred_forall, ← Set.compl_ofPred]
    exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ => (hP j).compl))
  · apply MeasurableSet.inter _ (MeasurableSet.const _)
    simp only [Set.ofPred_forall, ← Set.compl_ofPred]
    exact MeasurableSet.iInter (fun j => (hP j).compl)

theorem measurable_nativeFirstRecording (t : ℕ → ℝ) (ht : StrictMono t) (ε : ℝ) :
    Measurable (fun y : ℕ → ℝ => nativeFirstRecording t y ε) := by
  apply measurable_nat_sInf_of_measurable_events
  intro n
  exact measurableSet_lt measurable_const ((measurable_nativeStream_output t ht
    (fun j (y : ℕ → ℝ) => y j) ε (n+1) (fun j _ => measurable_pi_apply j)).fst)

/-- Actual first duration before EOF clipping, read from the first native rejection. -/
def brownianNativeFirstDuration {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ε : ℝ) (h : ℝ≥0) (ω : Ω) : ℝ :=
  (h : ℝ)*(nativeFirstRecording (fun j => (j : ℝ)*(h : ℝ))
    (fun j => B ((j : ℝ≥0)*h) ω) ε : ℝ)

theorem aemeasurable_brownianNativeFirstDuration {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B μ)
    (ε : ℝ) {h : ℝ≥0} (hh : 0 < h) : AEMeasurable (brownianNativeFirstDuration B ε h) μ := by
  have hr := (measurable_nativeFirstRecording _ (strictMono_mesh_times (by exact_mod_cast hh)) ε).comp_aemeasurable
    (aemeasurable_pi_lambda _ (fun j : ℕ => hB.aemeasurable ((j : ℝ≥0)*h)))
  exact ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp_aemeasurable hr).const_mul h

end SwingRepair
