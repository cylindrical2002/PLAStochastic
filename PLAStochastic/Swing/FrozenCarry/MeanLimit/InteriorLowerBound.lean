import PLAStochastic.Swing.FrozenCarry.Interior.IndexRange
import PLAStochastic.Swing.FrozenCarry.DurationTail.UniformMeanBound
import PLAStochastic.Swing.FrozenCarry.Path.SlopeLaw
import PLAStochastic.ForMathlib.Probability.Moments.NatMeanTailSumLower

/-! # The mean dominates any interior range sum of survival probabilities

Almost every path has a finite maximal prefix, so the `WithTop`-valued survival
events agree almost everywhere with the natural-valued ones and the finite tail
partial sums are dominated by the mean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenPrefixLength_ae_ne_top
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w E : ℝ) :
    ∀ᵐ ω ∂μ, frozenPrefixLength X w E ω ≠ ⊤ := by
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hX hi hG w,
    frozenSlopeMagnitude_positive_ae hX hi hG w] with ω hv hA
  exact frozenPrefixLength_finite_of_magnitude hv hA.2 E

/-- Off the null set of infinite prefixes the two survival events agree. -/
theorem frozenPrefixLength_tail_measureReal_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w E : ℝ) (n : ℕ) :
    μ.real {ω | ((n+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω} =
      μ.real {ω | n < (frozenPrefixLength X w E ω).untopD 0} := by
  refine (measureReal_congr (Filter.eventuallyEq_set.mpr ?_)).symm
  filter_upwards [frozenPrefixLength_ae_ne_top hX hi hG w E] with ω hω
  cases ht : frozenPrefixLength X w E ω using WithTop.recTopCoe with
  | top => exact absurd ht hω
  | coe k =>
      simp only [WithTop.untopD_coe]
      constructor
      · intro h
        have hnk : n < k := h
        exact WithTop.coe_le_coe.mpr hnk
      · intro h
        have hk : n+1 ≤ k := WithTop.coe_le_coe.mp h
        show n < k
        omega

/-- Every range of survival probabilities below the horizon is dominated by the
mean prefix length. -/
theorem frozen_range_sum_le_mean
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) {E : ℝ} (hE : 0 < E)
    {a b : ℕ} (ha : 1 ≤ a) :
    (∑ n ∈ Finset.Ico a b,
        μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}) ≤
      ∫ ω, frozenPrefixLengthReal X w E ω ∂μ := by
  have := hi.isProbabilityMeasure
  set K : Ω → ℕ := fun ω => (frozenPrefixLength X w E ω).untopD 0 with hKdef
  have hKm : Measurable K := (frozenPrefixLength_measurable hX w E).untopD 0
  have hKi : Integrable (fun ω => (K ω : ℝ)) μ :=
    frozenPrefixLengthReal_integrable hX hi hG w hE
  have hfull := sum_tail_le_integral_natCast hKm hKi (b-1)
  have hshift : (∑ n ∈ Finset.Ico 1 b,
      μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}) =
      ∑ j ∈ Finset.range (b-1), μ.real {ω | j < K ω} := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 1+j = j+1 from Nat.add_comm 1 j]
    exact frozenPrefixLength_tail_measureReal_eq hX hi hG w E j
  have hsub : (∑ n ∈ Finset.Ico a b,
      μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}) ≤
      ∑ n ∈ Finset.Ico 1 b, μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => measureReal_nonneg)
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    exact Finset.mem_Ico.mpr ⟨le_trans ha h1, h2⟩
  calc _ ≤ ∑ n ∈ Finset.Ico 1 b, μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} := hsub
    _ = ∑ j ∈ Finset.range (b-1), μ.real {ω | j < K ω} := hshift
    _ ≤ _ := hfull

end SwingRepair
