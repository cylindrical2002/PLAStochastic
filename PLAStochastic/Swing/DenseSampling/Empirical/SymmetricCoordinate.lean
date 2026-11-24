import PLAStochastic.Swing.DenseSampling.Segments.FixedIndexLimits

/-! # A symmetric binary coordinate is independent of its unchanged partner -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {T S : Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- Joint reflection splits every measurable lifetime event equally between
both signs; marginal fairness alone is not the premise. -/
theorem symmetric_binary_joint_half
    (hval : ∀ᵐ ω ∂μ, S ω = 1 ∨ S ω = -1)
    (hsym : IdentDistrib (fun ω => (T ω, S ω)) (fun ω => (T ω, -S ω)) μ μ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    μ {ω | T ω ∈ A ∧ S ω = 1} = μ (T ⁻¹' A) / 2 ∧
      μ {ω | T ω ∈ A ∧ S ω = -1} = μ (T ⁻¹' A) / 2 := by
  have heq : μ {ω | T ω ∈ A ∧ S ω = 1} = μ {ω | T ω ∈ A ∧ S ω = -1} := by
    have hd := hsym.measure_mem_eq (hA.prod (measurableSet_singleton (1 : ℝ)))
    change μ {ω | T ω ∈ A ∧ S ω = 1} = μ {ω | T ω ∈ A ∧ -S ω = 1} at hd
    simpa only [neg_eq_iff_eq_neg] using hd
  have hnull : NullMeasurableSet {ω | T ω ∈ A ∧ S ω = -1} μ :=
    hsym.aemeasurable_fst.nullMeasurableSet_preimage (hA.prod (measurableSet_singleton (-1 : ℝ)))
  have hdis : Disjoint {ω | T ω ∈ A ∧ S ω = 1} {ω | T ω ∈ A ∧ S ω = -1} := by
    apply Set.disjoint_left.mpr
    intro ω hp hn
    have := hp.2.symm.trans hn.2
    norm_num at this
  have hunion : ({ω | T ω ∈ A ∧ S ω = 1} ∪ {ω | T ω ∈ A ∧ S ω = -1} : Set Ω) =ᵐ[μ] T ⁻¹' A := by
    filter_upwards [hval] with ω hω
    apply propext
    change (T ω ∈ A ∧ S ω = 1 ∨ T ω ∈ A ∧ S ω = -1) ↔ T ω ∈ A
    tauto
  have htotal := measure_union₀ hnull hdis.aedisjoint
  rw [measure_congr hunion, ← heq] at htotal
  have hp : μ {ω | T ω ∈ A ∧ S ω = 1} = μ (T ⁻¹' A) / 2 := by
    apply (ENNReal.eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mpr
    simpa only [two_mul] using htotal.symm
  exact ⟨hp, heq.symm.trans hp⟩

theorem symmetric_binary_fair
    (hval : ∀ᵐ ω ∂μ, S ω = 1 ∨ S ω = -1)
    (hsym : IdentDistrib (fun ω => (T ω, S ω)) (fun ω => (T ω, -S ω)) μ μ) :
    μ {ω | S ω = 1} = 1 / 2 ∧ μ {ω | S ω = -1} = 1 / 2 := by
  simpa only [mem_univ, true_and, preimage_univ, measure_univ] using
    symmetric_binary_joint_half hval hsym MeasurableSet.univ

/-- A jointly symmetric binary coordinate is independent of the unchanged
coordinate. This uses the full family of measurable first-coordinate events. -/
theorem symmetric_binary_indep
    (hval : ∀ᵐ ω ∂μ, S ω = 1 ∨ S ω = -1)
    (hsym : IdentDistrib (fun ω => (T ω, S ω)) (fun ω => (T ω, -S ω)) μ μ) :
    IndepFun T S μ := by
  have hfair := symmetric_binary_fair hval hsym
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A D hA hD
  have hjoint := symmetric_binary_joint_half hval hsym hA
  have hset (h : (1 : ℝ) ∈ D ∧ (-1 : ℝ) ∈ D) : S ⁻¹' D =ᵐ[μ] univ := by
    filter_upwards [hval] with ω hω
    apply propext
    change S ω ∈ D ↔ True
    apply iff_true_intro
    rcases hω with hω | hω
    · rw [hω]; exact h.1
    · rw [hω]; exact h.2
  by_cases hp : (1 : ℝ) ∈ D
  · by_cases hn : (-1 : ℝ) ∈ D
    · have hs := hset ⟨hp, hn⟩
      have hi := ae_eq_set_inter (EventuallyEq.rfl (f := T ⁻¹' A)) hs
      rw [measure_congr hi, measure_congr hs, inter_univ, measure_univ, mul_one]
    · have hs : S ⁻¹' D =ᵐ[μ] {ω | S ω = 1} := by
        filter_upwards [hval] with ω hω
        apply propext
        change S ω ∈ D ↔ S ω = 1
        rcases hω with hω | hω <;> rw [hω] <;> norm_num [hp, hn]
      have hi := ae_eq_set_inter (EventuallyEq.rfl (f := T ⁻¹' A)) hs
      rw [measure_congr hi, measure_congr hs, hfair.1]
      change μ {ω | T ω ∈ A ∧ S ω = 1} = _
      rw [hjoint.1, div_eq_mul_inv, one_div]
  · by_cases hn : (-1 : ℝ) ∈ D
    · have hs : S ⁻¹' D =ᵐ[μ] {ω | S ω = -1} := by
        filter_upwards [hval] with ω hω
        apply propext
        change S ω ∈ D ↔ S ω = -1
        rcases hω with hω | hω <;> rw [hω] <;> norm_num [hp, hn]
      have hi := ae_eq_set_inter (EventuallyEq.rfl (f := T ⁻¹' A)) hs
      rw [measure_congr hi, measure_congr hs, hfair.2]
      change μ {ω | T ω ∈ A ∧ S ω = -1} = _
      rw [hjoint.2, div_eq_mul_inv, one_div]
    · have hs : S ⁻¹' D =ᵐ[μ] (∅ : Set Ω) := by
        filter_upwards [hval] with ω hω
        apply propext
        change S ω ∈ D ↔ False
        rcases hω with hω | hω <;> rw [hω] <;> norm_num [hp, hn]
      have hi := ae_eq_set_inter (EventuallyEq.rfl (f := T ⁻¹' A)) hs
      rw [measure_congr hi, measure_congr hs, inter_empty, measure_empty, mul_zero]

end SwingRepair
