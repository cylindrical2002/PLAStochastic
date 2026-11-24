import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic

/-! # Bounded stopping identities retaining an infinite first-exit time -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- min(τ,n), including min(infinity,n)=n, as an ordinary natural number. -/
def capDiscreteTime (τ : WithTop ℕ) (n : ℕ) : ℕ := min n (τ.untopD n)

@[simp] theorem capDiscreteTime_zero (τ : WithTop ℕ) : capDiscreteTime τ 0 = 0 := by
  simp [capDiscreteTime]

theorem capDiscreteTime_le (τ : WithTop ℕ) (n : ℕ) : capDiscreteTime τ n ≤ n := min_le_left _ _

theorem capDiscreteTime_eq_of_lt {τ : WithTop ℕ} {n : ℕ} (h : (n : WithTop ℕ) < τ) :
    capDiscreteTime τ n = n := by
  cases τ using WithTop.recTopCoe with
  | top => simp [capDiscreteTime]
  | coe k =>
    have h' : n < k := WithTop.coe_lt_coe.mp h
    simp only [capDiscreteTime, WithTop.untopD_coe]
    exact min_eq_left h'.le

theorem capDiscreteTime_succ (τ : WithTop ℕ) (n : ℕ) :
    capDiscreteTime τ (n+1) = capDiscreteTime τ n + if (n : WithTop ℕ) < τ then 1 else 0 := by
  cases τ using WithTop.recTopCoe with
  | top => simp [capDiscreteTime]
  | coe k =>
    split_ifs with h
    · have hn : n < k := WithTop.coe_lt_coe.mp h
      simp only [capDiscreteTime, WithTop.untopD_coe]
      omega
    · have hn : ¬ n < k := fun hh => h (WithTop.coe_lt_coe.mpr hh)
      simp only [capDiscreteTime, WithTop.untopD_coe]
      omega

/-- Exact pathwise telescoping, before any martingale or integrability argument. -/
theorem capDiscreteTime_potential_sum (V : ℕ → ℝ) (τ : WithTop ℕ) (m : ℕ) :
    V (capDiscreteTime τ m) = V 0 + ∑ k ∈ Finset.range m,
      if (k : WithTop ℕ) < τ then V (k+1)-V k else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, capDiscreteTime_succ]
    by_cases h : (m : WithTop ℕ) < τ
    · rw [if_pos h, if_pos h, capDiscreteTime_eq_of_lt h]
      ring
    · rw [if_neg h, if_neg h, Nat.add_zero, add_zero]

/-- The capped time counts exactly the surviving discrete steps. -/
theorem capDiscreteTime_eq_sum (τ : WithTop ℕ) (m : ℕ) :
    (capDiscreteTime τ m : ℝ) = ∑ k ∈ Finset.range m,
      if (k : WithTop ℕ) < τ then (1 : ℝ) else 0 := by
  have h := capDiscreteTime_potential_sum (fun n => (n : ℝ)) τ m
  simpa only [Nat.cast_zero, zero_add, Nat.cast_add, Nat.cast_one, add_sub_cancel_left] using h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {τ : Ω → WithTop ℕ}

theorem capDiscreteTime_measurable (hτ : Measurable τ) (m : ℕ) :
    Measurable (fun ω => capDiscreteTime (τ ω) m) := measurable_const.min (hτ.untopD m)

/-- A stopped integrable process is integrable at every bounded discrete horizon. -/
theorem capDiscreteTime_potential_integrable (hτ : Measurable τ)
    {V : ℕ → Ω → ℝ} (hV : ∀ n, Integrable (V n) μ) (m : ℕ) :
    Integrable (fun ω => V (capDiscreteTime (τ ω) m) ω) μ := by
  have hi (k : ℕ) : Integrable (fun ω => if (k : WithTop ℕ) < τ ω then V (k+1) ω-V k ω else 0) μ := by
    apply (((hV (k+1)).sub (hV k)).indicator
      (measurableSet_lt (measurable_const (a := (k : WithTop ℕ))) hτ)).congr
    exact Eventually.of_forall (fun ω => by simp only [Set.indicator_apply, Pi.sub_apply]; rfl)
  have hs := (hV 0).add (integrable_finsetSum (Finset.range m) (fun k _ => hi k))
  apply hs.congr
  apply Eventually.of_forall
  intro ω
  exact (capDiscreteTime_potential_sum (fun n => V n ω) (τ ω) m).symm

/-- The expected potential equals its initial expectation plus the actual stopped step drifts. -/
theorem integral_capDiscreteTime_potential (hτ : Measurable τ)
    {V : ℕ → Ω → ℝ} (hV : ∀ n, Integrable (V n) μ) (m : ℕ) :
    (∫ ω, V (capDiscreteTime (τ ω) m) ω ∂μ) = (∫ ω, V 0 ω ∂μ) +
      ∑ k ∈ Finset.range m, ∫ ω,
        if (k : WithTop ℕ) < τ ω then V (k+1) ω-V k ω else 0 ∂μ := by
  have hi (k : ℕ) : Integrable (fun ω => if (k : WithTop ℕ) < τ ω then V (k+1) ω-V k ω else 0) μ := by
    apply (((hV (k+1)).sub (hV k)).indicator
      (measurableSet_lt (measurable_const (a := (k : WithTop ℕ))) hτ)).congr
    exact Eventually.of_forall (fun ω => by simp only [Set.indicator_apply, Pi.sub_apply]; rfl)
  calc
    _ = ∫ ω, V 0 ω + ∑ k ∈ Finset.range m,
      if (k : WithTop ℕ) < τ ω then V (k+1) ω - V k ω else 0 ∂μ :=
        integral_congr_ae (Eventually.of_forall (fun ω => capDiscreteTime_potential_sum (fun n => V n ω) (τ ω) m))
    _ = _ := ?_
  rw [integral_add (hV 0) (integrable_finsetSum (Finset.range m) (fun k _ => hi k)),
    integral_finsetSum _ (fun k _ => hi k)]

/-- Expected capped exit time is the finite sum of the true survival probabilities. -/
theorem integral_capDiscreteTime [IsProbabilityMeasure μ] (hτ : Measurable τ) (m : ℕ) :
    (∫ ω, (capDiscreteTime (τ ω) m : ℝ) ∂μ) = ∑ k ∈ Finset.range m, μ.real {ω | (k : WithTop ℕ) < τ ω} := by
  simp_rw [capDiscreteTime_eq_sum]
  have hi (k : ℕ) : Integrable (fun ω => if (k : WithTop ℕ) < τ ω then (1 : ℝ) else 0) μ := by
    apply ((integrable_const (1 : ℝ) (μ := μ)).indicator
      (measurableSet_lt (measurable_const (a := (k : WithTop ℕ))) hτ)).congr
    exact Eventually.of_forall (fun ω => by simp only [Set.indicator_apply]; rfl)
  rw [integral_finsetSum _ (fun k _ => hi k)]
  apply Finset.sum_congr rfl
  intro k _
  have hs := measurableSet_lt (measurable_const (a := (k : WithTop ℕ))) hτ
  have he := integral_indicator (μ := μ) hs (f := fun _ : Ω => (1 : ℝ))
  simpa only [Set.indicator_apply, mem_ofPred_eq, setIntegral_const, smul_eq_mul, mul_one] using! he

end SwingRepair
