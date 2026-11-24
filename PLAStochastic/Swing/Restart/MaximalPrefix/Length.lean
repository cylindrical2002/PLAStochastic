import PLAStochastic.Swing.Restart.MaximalPrefix.ConditionalBlocks

/-! # The actual maximal feasible prefix, retaining infinity until it is ruled out -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- Maximal feasible native prefix for an arbitrary selected anchor.
The first failed test at index k checks sample k+1, so the accepted length is k. -/
def nativePrefixLength {Ω : Type*} (D : ℕ → Ω → ℝ) (Q : Ω → ℝ) (E : ℝ) : Ω → WithTop ℕ :=
  hittingAfter (fun k ω => ¬ nativePrefixFeasible (fun j => (j : ℝ))
    (fun j => D j ω) E 0 (k + 1) (Q ω)) {True} 0

theorem nativePrefixLength_le_iff {Ω : Type*} (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (E : ℝ) (ω : Ω) (n : ℕ) :
    nativePrefixLength D Q E ω ≤ n ↔ ∃ j ≤ n,
      ¬ nativePrefixFeasible (fun k => (k : ℝ)) (fun k => D k ω) E 0 (j + 1) (Q ω) := by
  simpa [nativePrefixLength] using
    (hittingAfter_le_iff (u := fun k ω => ¬ nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => D j ω) E 0 (k + 1) (Q ω)) (s := {True}) (n := 0) (i := n) (ω := ω))

theorem le_nativePrefixLength_iff {Ω : Type*} (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (E : ℝ) (ω : Ω) (n : ℕ) :
    (n : WithTop ℕ) ≤ nativePrefixLength D Q E ω ↔
      nativePrefixFeasible (fun k => (k : ℝ)) (fun k => D k ω) E 0 n (Q ω) := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, zero_le, true_iff]
    exact ⟨0, by simp [feasibleSlope]⟩
  | succ n =>
    have hsucc : ((n + 1 : ℕ) : WithTop ℕ) ≤ nativePrefixLength D Q E ω ↔
        (n : WithTop ℕ) < nativePrefixLength D Q E ω := by
      cases nativePrefixLength D Q E ω using WithTop.recTopCoe with
      | top => simp
      | coe k => exact WithTop.coe_le_coe.trans (Nat.succ_le_iff.trans WithTop.coe_lt_coe.symm)
    rw [hsucc, lt_iff_not_ge, nativePrefixLength_le_iff]
    constructor
    · intro h
      by_contra hn
      exact h ⟨n, le_rfl, hn⟩
    · rintro ⟨a, ha⟩ ⟨j, hj, hrej⟩
      apply hrej
      refine ⟨a, fun k hk => ha k ?_⟩
      have hk' := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩

theorem one_le_nativePrefixLength {Ω : Type*} (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    {E : ℝ} (hE : 0 ≤ E) (ω : Ω) : (1 : WithTop ℕ) ≤ nativePrefixLength D Q E ω := by
  apply (le_nativePrefixLength_iff D Q E ω 1).mpr
  refine ⟨D 1 ω - Q ω, ?_⟩
  intro k hk
  have hk1 : k = 1 := by have := Finset.mem_Icc.mp hk; omega
  subst k
  simpa only [Nat.cast_one, Nat.cast_zero, sub_zero, mul_one, add_sub_cancel,
    sub_self, abs_zero] using hE

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem nativePrefixLength_measurable (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable (D k)) (hQ : Measurable Q) (E : ℝ) :
    Measurable (nativePrefixLength D Q E) := by
  have hs : IsStoppingTime (Filtration.const ℕ mΩ le_rfl) (nativePrefixLength D Q E) := by
    apply Adapted.isStoppingTime_hittingAfter
    · intro n
      exact (@measurableSet_setOfPred Ω mΩ _).mp
        (nativePrefixFeasible_measurableSet _ (fun _ _ h => Nat.cast_lt.mpr h)
          D E 0 (n + 1) (by omega) hQ (fun k _ => hD k)).compl
    · exact measurableSet_singleton True
  exact hs.measurable'

/-- The paper's conditional tail, expressed using the actual maximal prefix N. -/
theorem nativePrefixLength_conditional_three_point_bound
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hfresh : Indep (incrementIndexSpace X Set.univ) m μ)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable[mΩ] (D k)) (hQ : Measurable[m] Q)
    {n : ℕ} (hn : 1 ≤ n) (hDp : ∀ k ≤ n, Measurable[m] (D k))
    (hshift : ∀ ω k, D (n + k) ω = D n ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r b : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    μ[({ω | ((n + 2 * r * b : ℕ) : WithTop ℕ) ≤ nativePrefixLength D Q E ω}).indicator
      (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ]
      ({ω | (n : WithTop ℕ) ≤ nativePrefixLength D Q E ω}).indicator
        (fun _ => gaussianBlockPass.toReal ^ b) := by
  let : MeasurableSpace Ω := mΩ
  simpa only [le_nativePrefixLength_iff] using
    nativePrefix_conditional_three_point_bound hX hi hG hm hfresh D Q hD hQ hn hDp hshift hE r b hr

/-- Uniform block tail: the carried first value and selected anchor cancel exactly.
Their sizes and even their joint law do not enter this bound. -/
theorem nativePrefixLength_three_point_tail
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hshift : ∀ ω k, D (1 + k) ω = D 1 ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r b : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    μ {ω | ((1 + 2 * r * b : ℕ) : WithTop ℕ) ≤ nativePrefixLength D Q E ω} ≤
      gaussianBlockPass ^ b := by
  apply le_trans _ (nativeGaussianBlocksPassed_probability_le hX hi hG hE 0 r b hr)
  apply measure_mono
  intro ω hω j hj
  obtain ⟨a, ha⟩ := (le_nativePrefixLength_iff D Q E ω (1 + 2 * r * b)).mp hω
  simp only [Nat.zero_add]
  apply affine_fit_three_point_block ω (x := D 1 ω) (q := Q ω + a) (a := a)
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  have hmul := Nat.mul_le_mul_left (2 * r) (show j + 1 ≤ b by omega)
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hmem : 1 + k ∈ Finset.Icc (0 + 1) (1 + 2 * r * b) :=
    Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  calc
    |D 1 ω + cumulativeSamples X k ω - (Q ω + a) - a * (k : ℝ)| =
        |D (1 + k) ω - (Q ω + a * ((1 + k : ℕ) : ℝ))| := by
      rw [hshift]
      push_cast
      congr 1
      ring
    _ ≤ E := by simpa only [Nat.cast_zero, sub_zero] using! ha (1 + k) hmem

/-- Infinity was retained in N's definition and is now ruled out by the proved Gaussian tail. -/
theorem nativePrefixLength_ae_finite
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hshift : ∀ ω k, D (1 + k) ω = D 1 ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    ∀ᵐ ω ∂μ, nativePrefixLength D Q E ω ≠ ⊤ := by
  have hz : μ {ω | nativePrefixLength D Q E ω = ⊤} = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one gaussianBlockPass_lt_one)
    intro b
    apply le_trans _ (nativePrefixLength_three_point_tail hX hi hG D Q hshift hE r b hr)
    apply measure_mono
    intro ω hω
    change ((1 + 2 * r * b : ℕ) : WithTop ℕ) ≤ nativePrefixLength D Q E ω
    rw [show nativePrefixLength D Q E ω = ⊤ from hω]
    exact le_top
  simpa only [ae_iff, not_not] using hz

end SwingRepair
