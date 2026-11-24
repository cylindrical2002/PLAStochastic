import PLAStochastic.ForMathlib.Probability.Process.IIDRestart.AeFiniteStoppingTime
import Mathlib.Probability.Independence.InfinitePi

/-! # The entire iid future sequence at an almost surely finite stopping time -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace SwingRepair

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {X : ℕ → Ω → ℝ}

/-- The entire fixed future, not merely each separate increment, is independent of the past. -/
theorem futureSequence_indep_incrementFiltration (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (n : ℕ) :
    Indep (MeasurableSpace.comap (fun ω (j : ℕ) => X (n + 1 + j) ω) inferInstance)
      (incrementFiltration X hX n) μ := by
  have hd : Disjoint (Set.Ioi n) (Set.Iic n) := by
    apply Set.disjoint_left.mpr
    intro i hi₁ hi₂
    change n < i at hi₁
    change i ≤ n at hi₂
    omega
  have h := indep_iSup_of_disjoint (fun k => (hX k).comap_le) hi.iIndep hd
  have hcomap :
      MeasurableSpace.comap (fun ω (j : ℕ) => X (n + 1 + j) ω) inferInstance ≤
        ⨆ i ∈ Set.Ioi n, MeasurableSpace.comap (X i) inferInstance := by
    rw [MeasurableSpace.comap_process_pi]
    refine iSup_le fun j => ?_
    exact le_iSup_of_le (n + 1 + j) (le_iSup_of_le (by simp; omega) le_rfl)
  simpa [incrementFiltration, Filtration.natural] using indep_of_indep_of_le_left h hcomap

/-- Original iid marginals determine the joint law of each entire shifted sequence. -/
theorem futureSequence_identDistrib (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ) (n : ℕ) :
    IdentDistrib (fun ω (j : ℕ) => X (n + 1 + j) ω) (fun ω (j : ℕ) => X j ω) μ μ := by
  have hshift : iIndepFun (fun j : ℕ => X (n + 1 + j)) μ :=
    hi.precomp (g := fun j : ℕ => n + 1 + j) (by intro i j hij; dsimp at hij; omega)
  refine ⟨(measurable_pi_lambda _ fun j : ℕ => hX (n + 1 + j)).aemeasurable,
    (measurable_pi_lambda _ hX).aemeasurable, ?_⟩
  rw [hshift.map_fun_eq_infinitePi_map (fun j => hX (n + 1 + j)),
    hi.map_fun_eq_infinitePi_map hX]
  congr 1
  funext j
  exact (hid (n + 1 + j)).map_eq.trans (hid j).map_eq.symm

/-- The random future sequence is measurable; no modified stopping-time claim is made. -/
theorem stoppedSequence_measurable (hX : ∀ n, Measurable (X n))
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ) :
    Measurable (fun ω (j : ℕ) => X ((τ ω).untopD 0 + 1 + j) ω) :=
  countableSelection_measurable
    (fun n => measurable_pi_lambda _ fun j : ℕ => hX (n + 1 + j))
    (hτ.measurable'.untopD 0)

/-- Full-sequence restart on every event in the original stopped sigma-algebra. -/
theorem stoppedSequence_inter_measure (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A)
    {B : Set (ℕ → ℝ)} (hB : MeasurableSet B) :
    μ (A ∩ (fun ω (j : ℕ) => X ((τ ω).untopD 0 + 1 + j) ω) ⁻¹' B) =
      μ A * μ ((fun ω (j : ℕ) => X j ω) ⁻¹' B) :=
  stoppedSelection_inter_measure_aeFinite hX
    (fun n => measurable_pi_lambda _ fun j : ℕ => hX (n + 1 + j))
    (futureSequence_indep_incrementFiltration hX hi)
    (futureSequence_identDistrib hX hi hid) hτ isFiniteK hA hB

/-- The entire post-stopping sequence has the original iid process law. -/
theorem stoppedSequence_identDistrib [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    IdentDistrib (fun ω (j : ℕ) => X ((τ ω).untopD 0 + 1 + j) ω)
      (fun ω (j : ℕ) => X j ω) μ μ := by
  refine ⟨(stoppedSequence_measurable hX hτ).aemeasurable,
    (measurable_pi_lambda _ hX).aemeasurable, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (stoppedSequence_measurable hX hτ) hB,
    Measure.map_apply (measurable_pi_lambda _ hX) hB]
  simpa using stoppedSequence_inter_measure hX hi hid hτ isFiniteK MeasurableSet.univ hB

/-- The entire post-stopping sequence is independent of the original stopped sigma-algebra. -/
theorem stoppedSequence_indep_stopped [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hid : ∀ n, IdentDistrib (X n) (X 0) μ μ)
    {τ : Ω → WithTop ℕ} (hτ : IsStoppingTime (incrementFiltration X hX) τ)
    (isFiniteK : ∀ᵐ ω ∂μ, τ ω ≠ ⊤) :
    Indep (MeasurableSpace.comap
      (fun ω (j : ℕ) => X ((τ ω).untopD 0 + 1 + j) ω) inferInstance)
      hτ.measurableSpace μ := by
  apply (Indep_iff _ _ μ).mpr
  intro C A hC hA
  rcases hC with ⟨B, hB, rfl⟩
  rw [Set.inter_comm, stoppedSequence_inter_measure hX hi hid hτ isFiniteK hA hB,
    (stoppedSequence_identDistrib hX hi hid hτ isFiniteK).measure_mem_eq hB, mul_comm]

end SwingRepair
