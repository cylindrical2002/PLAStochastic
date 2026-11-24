import PLAStochastic.ForMathlib.Probability.Kernel.Doeblin.TotalVariation

/-! # Two-step Doeblin minorization

A common component for `P ∘ₖ P` yields a unique invariant probability for `P`
and a total-variation bound at every integer time, including odd times. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory Topology
namespace SwingRepair.Doeblin
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {S : Type*} [MeasurableSpace S]

/-- The measure iteration agrees with the usual kernel power. -/
theorem iterate_eq_pow_comp (P : Kernel S S) (n : ℕ) (μ : Measure S) :
    iterate P n μ = (P^n) ∘ₘ μ := by
  induction n with
  | zero => exact (Measure.id_comp (μ := μ)).symm
  | succ n ih =>
    rw [iterate_succ, ih, Measure.comp_assoc, pow_succ']
    rfl

theorem iterate_dirac (P : Kernel S S) (n : ℕ) (x : S) :
    iterate P n (Measure.dirac x) = (P^n) x := by
  rw [iterate_eq_pow_comp]
  exact Measure.dirac_bind (P^n).measurable x

theorem iterate_two_step (P : Kernel S S) (n : ℕ) (μ : Measure S) :
    iterate (P ∘ₖ P) n μ = iterate P (2*n) μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ, ← Measure.comp_assoc, ih, Nat.mul_succ]
    rfl

theorem iterate_two_step_remainder (P : Kernel S S) (n : ℕ) (μ : Measure S) :
    iterate P n μ = iterate (P ∘ₖ P) (n/2) (iterate P (n%2) μ) := by
  rw [iterate_two_step, ← iterate_add]
  congr 1
  omega

theorem invariant_two_step_pushforward (P : Kernel S S) (π : Measure S)
    (hπ : (P ∘ₖ P).Invariant π) : (P ∘ₖ P).Invariant (P ∘ₘ π) := by
  change (P ∘ₖ P) ∘ₘ (P ∘ₘ π) = P ∘ₘ π
  have hq : P ∘ₘ (P ∘ₘ π) = π := by
    rw [Measure.comp_assoc]
    exact hπ
  rw [← Measure.comp_assoc, hq]

/-- Two-step minorization by a common finite submeasure implies uniqueness and
geometric convergence at all times. -/
theorem exists_unique_invariant_two_step (P : Kernel S S) [IsMarkovKernel P]
    (β : Measure S) [IsFiniteMeasure β] (hminor : ∀ x, β ≤ (P ∘ₖ P) x)
    (hβ : 0 < β univ) (hβ1 : β univ ≤ 1) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ P.Invariant π ∧
      (∀ μ : Measure S, IsProbabilityMeasure μ → P.Invariant μ → μ = π) ∧
      ∀ μ : Measure S, IsProbabilityMeasure μ → ∀ n : ℕ,
        totalVariation (iterate P n μ) π ≤ (1 - β univ)^(n/2) := by
  obtain ⟨π, hπprob, hπQ, huniq, hmix⟩ := exists_unique_invariant (P ∘ₖ P) β hminor hβ hβ1
  let := hπprob
  have hπP : P.Invariant π := huniq (P ∘ₘ π) inferInstance (invariant_two_step_pushforward P π hπQ)
  refine ⟨π, hπprob, hπP, ?_, ?_⟩
  · intro μ hμ hμP
    exact huniq μ hμ (hμP.comp hμP)
  · intro μ hμ n
    let := hμ
    rw [iterate_two_step_remainder P n μ]
    exact hmix (iterate P (n%2) μ) inferInstance (n/2)

/-- The usual minorization statement `α • ν ≤ P²(x,·)`, with a probability
measure `ν` and `0 < α ≤ 1`. The endpoint `α = 1` is also covered. -/
theorem exists_unique_invariant_of_two_step_minorization (P : Kernel S S) [IsMarkovKernel P]
    (ν : Measure S) [IsProbabilityMeasure ν] {α : ℝ≥0∞} (hα : 0 < α) (hα1 : α ≤ 1)
    (hminor : ∀ x, α • ν ≤ (P ∘ₖ P) x) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ P.Invariant π ∧
      (∀ μ : Measure S, IsProbabilityMeasure μ → P.Invariant μ → μ = π) ∧
      ∀ μ : Measure S, IsProbabilityMeasure μ → ∀ n : ℕ,
        totalVariation (iterate P n μ) π ≤ (1 - α)^(n/2) := by
  have hαfin : α ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hα1
  let : IsFiniteMeasure (α • ν) := ⟨by simp [Measure.smul_apply, hαfin.lt_top]⟩
  have hmass : (α • ν) univ = α := by simp
  simpa only [hmass] using exists_unique_invariant_two_step P (α • ν) hminor
    (by simpa only [hmass] using hα) (by simpa only [hmass] using hα1)

/-- The two-step geometric bound tends to zero. -/
theorem totalVariation_tendsto_zero_of_geometric {F : ℕ → ℝ≥0∞} {α : ℝ≥0∞}
    (hα : 0 < α) (hF : ∀ n, F n ≤ (1 - α)^(n/2)) : Tendsto F atTop (𝓝 0) := by
  have hpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hα.ne')
  have hlim := hpow.comp (Nat.tendsto_div_const_atTop (by norm_num : (2 : ℕ) ≠ 0))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hF

/-- A pointwise kernel-power version, uniform in the initial state, with actual
total-variation convergence in addition to the geometric estimate. -/
theorem exists_unique_invariant_uniform_two_step (P : Kernel S S) [IsMarkovKernel P]
    (ν : Measure S) [IsProbabilityMeasure ν] {α : ℝ≥0∞} (hα : 0 < α) (hα1 : α ≤ 1)
    (hminor : ∀ x, α • ν ≤ (P ∘ₖ P) x) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ P.Invariant π ∧
      (∀ μ : Measure S, IsProbabilityMeasure μ → P.Invariant μ → μ = π) ∧
      (∀ x : S, ∀ n : ℕ, totalVariation ((P^n) x) π ≤ (1 - α)^(n/2)) ∧
      Tendsto (fun n => ⨆ x : S, totalVariation ((P^n) x) π) atTop (𝓝 0) := by
  obtain ⟨π, hp, hi, hu, hb⟩ :=
    exists_unique_invariant_of_two_step_minorization P ν hα hα1 hminor
  have hpoint (x : S) (n : ℕ) : totalVariation ((P^n) x) π ≤ (1 - α)^(n/2) := by
    simpa only [iterate_dirac] using hb (Measure.dirac x) inferInstance n
  refine ⟨π, hp, hi, hu, hpoint, ?_⟩
  exact totalVariation_tendsto_zero_of_geometric hα (fun n => iSup_le fun x => hpoint x n)

end SwingRepair.Doeblin
