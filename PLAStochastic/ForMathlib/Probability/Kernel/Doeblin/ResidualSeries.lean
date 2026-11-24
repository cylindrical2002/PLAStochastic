import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Residual kernels and the explicit Doeblin invariant measure

A common finite submeasure is removed from a Markov transition. Iterating the
remaining subprobability kernel gives an explicit geometric series of measures;
its mass and invariance are proved directly. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal ProbabilityTheory Topology
namespace SwingRepair.Doeblin
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {S : Type*} [MeasurableSpace S]

/-- Push a measure through a kernel `n` times. -/
def iterate (K : Kernel S S) : ℕ → Measure S → Measure S
  | 0, μ => μ
  | n+1, μ => K ∘ₘ iterate K n μ

@[simp] theorem iterate_zero (K : Kernel S S) (μ : Measure S) : iterate K 0 μ = μ := rfl
@[simp] theorem iterate_succ (K : Kernel S S) (n : ℕ) (μ : Measure S) :
    iterate K (n+1) μ = K ∘ₘ iterate K n μ := rfl

theorem iterate_add_measure (K : Kernel S S) (n : ℕ) (μ η : Measure S) :
    iterate K n (μ+η) = iterate K n μ + iterate K n η := by
  induction n with
  | zero => simp
  | succ n ih => simp only [iterate_succ, ih, Measure.comp_add]

theorem iterate_add (K : Kernel S S) (n m : ℕ) (μ : Measure S) :
    iterate K (n+m) μ = iterate K n (iterate K m μ) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [Nat.succ_add, iterate_succ] using congrArg (fun η => K ∘ₘ η) ih

theorem iterate_comp (K : Kernel S S) (n : ℕ) (μ : Measure S) :
    iterate K n (K ∘ₘ μ) = K ∘ₘ iterate K n μ := by
  change iterate K n (iterate K 1 μ) = iterate K (n+1) μ
  rw [iterate_add]

instance iterate_isProbabilityMeasure (K : Kernel S S) [IsMarkovKernel K]
    (n : ℕ) (μ : Measure S) [IsProbabilityMeasure μ] : IsProbabilityMeasure (iterate K n μ) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => let := ih; exact inferInstanceAs (IsProbabilityMeasure (K ∘ₘ iterate K n μ))

theorem iterate_mass (K : Kernel S S) {q : ℝ≥0∞} (hK : ∀ x, K x univ = q)
    (n : ℕ) (μ : Measure S) : (iterate K n μ) univ = q ^ n * μ univ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ, Measure.bind_apply MeasurableSet.univ K.aemeasurable]
    simp only [hK, lintegral_const, ih, pow_succ', mul_assoc]

variable (P : Kernel S S)
variable (β : Measure S) [IsFiniteMeasure β]
variable (hminor : ∀ x, β ≤ P x)

/-- The substochastic residual after removing the common part. -/
def residual : Kernel S S where
  toFun x := P x - β
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp_rw [Measure.sub_apply hs (hminor _)]
    exact (P.measurable_coe hs).sub measurable_const

@[simp] theorem residual_apply (x : S) : residual P β hminor x = P x - β := rfl

theorem residual_add_common (x : S) : residual P β hminor x + β = P x :=
  Measure.sub_add_cancel_of_le (hminor x)

variable [IsMarkovKernel P]

theorem residual_mass (x : S) : residual P β hminor x univ = 1 - β univ := by
  rw [residual_apply, Measure.sub_apply MeasurableSet.univ (hminor x), measure_univ]

instance residual_isFiniteKernel : IsFiniteKernel (residual P β hminor) := by
  refine ⟨⟨1, ENNReal.one_lt_top, fun x => ?_⟩⟩
  rw [residual_mass]
  exact tsub_le_self

omit [IsMarkovKernel P] in
theorem transition_decomposition (μ : Measure S) :
    P ∘ₘ μ = residual P β hminor ∘ₘ μ + μ univ • β := by
  have hp : P = residual P β hminor + Kernel.const S β := by
    ext x s hs
    exact congrArg (fun η : Measure S => η s) (residual_add_common P β hminor x).symm
  conv_lhs => rw [hp, Measure.add_comp]
  congr 1
  exact Measure.bind_const

/-- The geometric series obtained by starting every residual excursion in the
common submeasure. -/
def invariantSeries : Measure S := Measure.sum (fun n => iterate (residual P β hminor) n β)

theorem invariantSeries_mass (hβ : 0 < β univ) (hβ1 : β univ ≤ 1) :
    invariantSeries P β hminor univ = 1 := by
  rw [invariantSeries, Measure.sum_apply _ MeasurableSet.univ]
  simp_rw [iterate_mass _ (residual_mass P β hminor)]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, ENNReal.sub_sub_cancel ENNReal.one_ne_top hβ1]
  exact ENNReal.inv_mul_cancel hβ.ne' (measure_ne_top β univ)

omit [IsMarkovKernel P] in
theorem invariantSeries_recursion :
    invariantSeries P β hminor = β + residual P β hminor ∘ₘ invariantSeries P β hminor := by
  ext s hs
  rw [invariantSeries, Measure.sum_apply _ hs, Measure.add_apply,
    Measure.bind_sum _ _ (residual P β hminor).aemeasurable, Measure.sum_apply _ hs]
  exact tsum_eq_zero_add' ENNReal.summable

theorem invariantSeries_isProbabilityMeasure (hβ : 0 < β univ) (hβ1 : β univ ≤ 1) :
    IsProbabilityMeasure (invariantSeries P β hminor) :=
  ⟨invariantSeries_mass P β hminor hβ hβ1⟩

theorem invariantSeries_invariant (hβ : 0 < β univ) (hβ1 : β univ ≤ 1) :
    P.Invariant (invariantSeries P β hminor) := by
  change P ∘ₘ invariantSeries P β hminor = _
  rw [transition_decomposition P β hminor, invariantSeries_mass P β hminor hβ hβ1, one_smul,
    add_comm, ← invariantSeries_recursion P β hminor]

end SwingRepair.Doeblin
