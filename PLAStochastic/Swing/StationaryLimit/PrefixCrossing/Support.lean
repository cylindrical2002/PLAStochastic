import PLAStochastic.Swing.StationaryLimit.LowerBridge.UniformBudget
import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.SubstituteIntegral

/-!
# Quantitative support for the prefix substitute

The random lower-bridge event records only positivity of the crossing level.
For the uniform renewal estimate one needs a quantitative lower bound.  The
explicit affine budget already used in the lower-bridge probability proof
gives one: on its good event the crossing level is at least the incoming
budget `E`.  This file exposes that arithmetic as a separate support
certificate, together with the induced compact positive support for the
prefix-state law.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {Ω : Type*} [MeasurableSpace Ω]

theorem gaussianNegativeCarryAffineEnvelopeEvent_measurableSet
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n)) (c R : ℝ) :
    MeasurableSet (gaussianNegativeCarryAffineEnvelopeEvent X c R) := by
  have hset : gaussianNegativeCarryAffineEnvelopeEvent X c R =
      ⋂ n : ℕ, {ω | |cumulativeSamples X n ω| ≤
        R + (c / 2) * ((n : ℝ) + 1)} := by
    ext ω
    simp [gaussianNegativeCarryAffineEnvelopeEvent]
  rw [hset]
  refine MeasurableSet.iInter (fun n => ?_)
  have hright : Measurable (fun _ : Ω => R + (c / 2) * ((n : ℝ) + 1)) :=
    measurable_const
  exact measurableSet_le (cumulativeSamples_measurable hX n).abs hright

theorem prefixCrossingUniformBudgetEvent_measurableSet
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (_E _r : ℝ) (J : ℕ) (K δ M C q : ℝ) :
    MeasurableSet (prefixCrossingUniformBudgetEvent X _E _r J K δ M C q) := by
  unfold prefixCrossingUniformBudgetEvent
  exact (swingEarlySlopeGood_measurableSet hX K δ M (J - 1)).inter
    (gaussianNegativeCarryAffineEnvelopeEvent_measurableSet hX (2 * q) C)

omit [MeasurableSpace Ω] in
theorem prefixCrossing_level_ge_E_of_uniform_budget
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ) (ω : Ω)
    (hJ : 1 ≤ J) {K δ M C q : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ M) (hr : |r| ≤ K)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J - 1))
    (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1))
    (hbudget :
      41 * K + 69 * C + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E) :
    E ≤ prefixCrossingLevel X E r J ω := by
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M) ω hJ hδ hgood hr
  have ha : prefixCrossingSlope X r J ω ≤ M := hbounds.2
  have hJcast : ((J - 1 : ℕ) : ℝ) + 1 = (J : ℝ) := by
    rw [Nat.cast_sub hJ]
    push_cast
    ring
  have hWJ := hW (J - 1)
  rw [hJcast] at hWJ
  have hlow : -(C + q * (J : ℝ)) ≤ cumulativeSamples X (J - 1) ω := by
    have habs := neg_le_abs (cumulativeSamples X (J - 1) ω)
    linarith
  have hK : 0 ≤ K := by
    exact (abs_nonneg r).trans (by
      have hr' := (abs_le.mp hr).2
      linarith)
  have hrK : -K ≤ -r := by
    have hr' := (abs_le.mp hr).2
    linarith
  dsimp [prefixCrossingLevel]
  nlinarith [hbudget]

omit [MeasurableSpace Ω] in
theorem prefixCrossingUniformBudgetEvent_subset_parameter_support
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ M C q : ℝ} (hJ : 1 ≤ J)
    (hδ : 0 < δ) (hM : 0 ≤ M)
    (hr : |r| ≤ K) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hbudget :
      41 * K + 69 * C + 69 * q * (J : ℝ) +
          14 * M * (J : ℝ) + 7 * M + 21 * q ≤ E) :
    prefixCrossingUniformBudgetEvent X E r J K δ M C q ⊆
      {ω | prefixCrossingSlope X r J ω ∈ Icc δ M ∧
        E ≤ prefixCrossingLevel X E r J ω} := by
  intro ω hω
  rcases hω with ⟨hgood, henv⟩
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M) ω hJ hδ hgood hr
  have hW : ∀ n : ℕ,
      |cumulativeSamples X n ω| ≤ C + q * ((n : ℝ) + 1) := by
    intro n
    simpa [gaussianNegativeCarryAffineEnvelopeEvent] using henv n
  have hlevel := prefixCrossing_level_ge_E_of_uniform_budget
    (X := X) E r J ω hJ hδ hM hr hgood hC hq hW hbudget
  exact ⟨⟨hbounds.1, hbounds.2⟩, hlevel⟩

/-! The support event itself is an intersection of the early-slope and affine
envelope events.  Exporting its complement bound separately is useful for the
state-local substitute estimate: the lower-bridge theorem only bounds the
complement of the larger bridge event, which is the opposite inclusion. -/
theorem prefixCrossingUniformBudgetEvent_compl_measure_le_of_components
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ M C q α β : ℝ}
    (hα : μ.real (swingEarlySlopeGood X K δ M (J - 1))ᶜ ≤ α)
    (hβ : μ.real (gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) C)ᶜ ≤ β) :
    μ.real (prefixCrossingUniformBudgetEvent X E r J K δ M C q)ᶜ ≤ α + β := by
  let A : Set Ω := swingEarlySlopeGood X K δ M (J - 1)
  let B : Set Ω := gaussianNegativeCarryAffineEnvelopeEvent X (2 * q) C
  have hAB : μ.real (A ∩ B)ᶜ ≤ μ.real Aᶜ + μ.real Bᶜ := by
    have hsub : (A ∩ B)ᶜ ⊆ Aᶜ ∪ Bᶜ := by
      intro ω hω
      by_cases hAω : ω ∈ A
      · right
        intro hBω
        exact hω ⟨hAω, hBω⟩
      · left
        exact hAω
    calc
      μ.real (A ∩ B)ᶜ ≤ μ.real (Aᶜ ∪ Bᶜ) :=
        measureReal_mono hsub (measure_ne_top μ _)
      _ ≤ μ.real Aᶜ + μ.real Bᶜ := measureReal_union_le _ _
  have hident :
      prefixCrossingUniformBudgetEvent X E r J K δ M C q = A ∩ B := by
    rfl
  rw [hident]
  exact hAB.trans (add_le_add hα hβ)

end SwingRepair
