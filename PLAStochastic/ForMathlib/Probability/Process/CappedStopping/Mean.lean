import PLAStochastic.ForMathlib.Probability.Process.CappedStopping.Identities

/-! # Finite exit time and actual expectation from bounded capped expectations -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem capDiscreteTime_monotone (τ : WithTop ℕ) : Monotone (capDiscreteTime τ) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [capDiscreteTime_succ]
  exact Nat.le_add_right _ _

/-- Capped times recover every finite value in the extended nonnegative reals. -/
theorem iSup_capDiscreteTime_coe (k : ℕ) :
    (⨆ m : ℕ, (capDiscreteTime (k : WithTop ℕ) m : ℝ≥0∞)) = k := by
  apply le_antisymm
  · apply iSup_le
    intro m
    exact_mod_cast (show capDiscreteTime (k : WithTop ℕ) m ≤ k by change min m k ≤ k; exact min_le_right _ _)
  · have hk := le_iSup (fun m : ℕ => (capDiscreteTime (k : WithTop ℕ) m : ℝ≥0∞)) k
    have he : capDiscreteTime (k : WithTop ℕ) k = k := by
      change min k k = k
      exact min_self k
    rw [he] at hk
    exact hk

@[simp] theorem iSup_capDiscreteTime_top :
    (⨆ m : ℕ, (capDiscreteTime ⊤ m : ℝ≥0∞)) = ⊤ := by
  simpa only [capDiscreteTime, WithTop.untopD_top, min_self] using ENNReal.iSup_natCast

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {τ : Ω → WithTop ℕ}

theorem capDiscreteTime_integrable [IsFiniteMeasure μ] (hτ : Measurable τ) (m : ℕ) :
    Integrable (fun ω => (capDiscreteTime (τ ω) m : ℝ)) μ := by
  apply (integrable_const (m : ℝ)).mono'
  · exact ((measurable_from_nat (f := fun k : ℕ => (k : ℝ))).comp (capDiscreteTime_measurable hτ m)).aestronglyMeasurable
  · exact Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast capDiscreteTime_le (τ ω) m)

/-- No finiteness assumption on τ is needed: uniform capped expectations prove
that τ is finite almost surely, integrable, and satisfies the same mean bound. -/
theorem discreteTime_ae_finite_integrable_mean_le_of_cap_bound [IsFiniteMeasure μ]
    (hτ : Measurable τ) {C : ℝ}
    (hC : ∀ m : ℕ, (∫ ω, (capDiscreteTime (τ ω) m : ℝ) ∂μ) ≤ C) :
    (∀ᵐ ω ∂μ, τ ω ≠ ⊤) ∧ Integrable (fun ω => (((τ ω).untopD 0 : ℕ) : ℝ)) μ ∧
      (∫ ω, (((τ ω).untopD 0 : ℕ) : ℝ) ∂μ) ≤ C := by
  let F : Ω → ℝ≥0∞ := fun ω => ⨆ m : ℕ, (capDiscreteTime (τ ω) m : ℝ≥0∞)
  have hm (m : ℕ) : Measurable (fun ω => (capDiscreteTime (τ ω) m : ℝ≥0∞)) :=
    (measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0∞))).comp (capDiscreteTime_measurable hτ m)
  have hF : Measurable F := Measurable.iSup hm
  have hi : (∫⁻ ω, F ω ∂μ) ≤ ENNReal.ofReal C := by
    rw [show (∫⁻ ω, F ω ∂μ) = ⨆ m : ℕ, ∫⁻ ω, (capDiscreteTime (τ ω) m : ℝ≥0∞) ∂μ from
      lintegral_iSup hm (fun i j hij ω => by exact_mod_cast capDiscreteTime_monotone (τ ω) hij)]
    apply iSup_le
    intro m
    have he := ofReal_integral_eq_lintegral_ofReal (capDiscreteTime_integrable (μ := μ) hτ m)
      (Eventually.of_forall (fun ω => Nat.cast_nonneg (α := ℝ) (capDiscreteTime (τ ω) m)))
    simp only [ENNReal.ofReal_natCast] at he
    rw [← he]
    exact ENNReal.ofReal_le_ofReal (hC m)
  have hfinite : (∫⁻ ω, F ω ∂μ) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi
  have haf := ae_lt_top hF hfinite
  have heq (ω : Ω) : (F ω).toReal = (((τ ω).untopD 0 : ℕ) : ℝ) := by
    dsimp only [F]
    cases τ ω using WithTop.recTopCoe with
    | top => simp only [iSup_capDiscreteTime_top, ENNReal.toReal_top, WithTop.untopD_top, Nat.cast_zero]
    | coe k =>
      exact (congrArg ENNReal.toReal (iSup_capDiscreteTime_coe k)).trans (ENNReal.toReal_natCast k)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [haf] with ω hω
    intro ht
    simp only [F, ht, iSup_capDiscreteTime_top, lt_self_iff_false] at hω
  · exact (integrable_toReal_of_lintegral_ne_top hF.aemeasurable hfinite).congr (Eventually.of_forall heq)
  · have hC0 : 0 ≤ C := by simpa only [capDiscreteTime_zero, Nat.cast_zero, integral_zero] using hC 0
    rw [← integral_congr_ae (Eventually.of_forall heq), integral_toReal hF.aemeasurable haf]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hi).trans_eq (ENNReal.toReal_ofReal hC0)

end SwingRepair
