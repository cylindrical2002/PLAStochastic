import PLAStochastic.Swing.Restart.MaximalPrefix.BlockProductProbabilities
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! # Conditional Gaussian block bounds with arbitrary carried history -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- A proved consequence of fresh-future independence, not a survival-law assumption.
The past event A can encode an arbitrary input history and selected carried anchor. -/
theorem conditional_indicator_le_gaussianBlocks (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hfresh : Indep (incrementIndexSpace X Set.univ) m μ)
    {E : ℝ} (hE : 0 < E) (n r b : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ))
    {A S : Set Ω} (hA : MeasurableSet[m] A) (hS : MeasurableSet[mΩ] S)
    (hsub : S ⊆ A ∩ nativeGaussianBlocksPassed X E n r b) :
    μ[S.indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ]
      A.indicator (fun _ => gaussianBlockPass.toReal ^ b) := by
  let : MeasurableSpace Ω := mΩ
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  let F := nativeGaussianBlocksPassed X E n r b
  have hF : MeasurableSet[incrementIndexSpace X Set.univ] F :=
    incrementIndexSpace_mono (Set.subset_univ _) _ (nativeGaussianBlocksPassed_measurable_in E n r b)
  have hFambient : MeasurableSet[mΩ] F := incrementIndexSpace_le hX Set.univ _ hF
  have hFi : Integrable (F.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const _).indicator hFambient
  have hFstrong : StronglyMeasurable[incrementIndexSpace X Set.univ]
      (F.indicator (fun _ => (1 : ℝ))) := by
    let := incrementIndexSpace X Set.univ
    exact (measurable_const.indicator hF).stronglyMeasurable
  have hcond := condExp_indep_eq (incrementIndexSpace_le hX Set.univ) hm hFstrong hfresh
  have hmean : (∫ ω, F.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real F := by
    rw [integral_indicator hFambient, setIntegral_const]
    simp only [smul_eq_mul, mul_one]
  rw [hmean] at hcond
  have hpull := condExp_indicator hFi hA
  have hmono : μ[S.indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ]
      μ[A.indicator (F.indicator (fun _ => (1 : ℝ))) | m] := by
    apply condExp_mono ((integrable_const _).indicator hS)
      (hFi.indicator (hm _ hA))
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ S
    · have ha := (hsub hω).1
      have hf : ω ∈ F := (hsub hω).2
      simp only [Set.indicator_of_mem hω, Set.indicator_of_mem ha, Set.indicator_of_mem hf]
      rfl
    · rw [Set.indicator_of_notMem hω]
      simp only [Set.indicator]
      split_ifs <;> norm_num
  have hprob : μ.real F ≤ gaussianBlockPass.toReal ^ b := by
    have hb := ENNReal.toReal_mono (ENNReal.pow_ne_top
      (ne_top_of_lt (gaussianBlockPass_lt_one.trans ENNReal.one_lt_top)))
      (nativeGaussianBlocksPassed_probability_le hX hi hG hE n r b hr)
    simpa only [measureReal_def, ENNReal.toReal_pow] using hb
  filter_upwards [hmono, hpull, hcond] with ω hmo hpu hco
  apply hmo.trans
  rw [hpu]
  by_cases ha : ω ∈ A
  · simp only [Set.indicator_of_mem ha]
    rw [hco]
    exact hprob
  · simp only [Set.indicator_of_notMem ha]
    rfl

/-- The conditional three-point estimate for the actual finite native prefix,
with arbitrary measurable history, selected anchor, and carried current value.
Only the future increments are assumed fresh and standard Gaussian. -/
theorem nativePrefix_conditional_three_point_bound
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (hfresh : Indep (incrementIndexSpace X Set.univ) m μ)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable[mΩ] (D k)) (hQ : Measurable[m] Q)
    {n : ℕ} (hn : 1 ≤ n) (hDp : ∀ k ≤ n, Measurable[m] (D k))
    (hshift : ∀ ω k, D (n + k) ω = D n ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r b : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    μ[({ω | nativePrefixFeasible (fun j => (j : ℝ)) (fun j => D j ω)
      E 0 (n + 2 * r * b) (Q ω)}).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ]
      ({ω | nativePrefixFeasible (fun j => (j : ℝ)) (fun j => D j ω) E 0 n (Q ω)}).indicator
        (fun _ => gaussianBlockPass.toReal ^ b) := by
  let : MeasurableSpace Ω := mΩ
  have ht : StrictMono (fun j : ℕ => (j : ℝ)) := fun _ _ h => Nat.cast_lt.mpr h
  have hA : MeasurableSet[m] {ω | nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => D j ω) E 0 n (Q ω)} := by
    let : MeasurableSpace Ω := m
    exact nativePrefixFeasible_measurableSet _ ht D E 0 n (by omega) hQ
      (fun k hk => hDp k (Finset.mem_Icc.mp hk).2)
  have hS : MeasurableSet[mΩ] {ω | nativePrefixFeasible (fun j => (j : ℝ))
      (fun j => D j ω) E 0 (n + 2 * r * b) (Q ω)} :=
    nativePrefixFeasible_measurableSet _ ht D E 0 (n + 2 * r * b) (by omega)
      (hQ.mono hm le_rfl) (fun k _ => hD k)
  apply conditional_indicator_le_gaussianBlocks hX hi hG hm hfresh hE 0 r b hr hA hS
  intro ω hω
  obtain ⟨a, ha⟩ := hω
  constructor
  · refine ⟨a, fun k hk => ha k ?_⟩
    have hk' := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩
  · intro j hj
    simp only [Nat.zero_add]
    apply affine_fit_three_point_block ω (x := D n ω) (q := Q ω + a * (n : ℝ)) (a := a)
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hj' : j + 1 ≤ b := by omega
    have hmul := Nat.mul_le_mul_left (2 * r) hj'
    rw [Nat.mul_add, Nat.mul_one] at hmul
    have hmem : n + k ∈ Finset.Icc (0 + 1) (n + 2 * r * b) :=
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    calc
      |D n ω + cumulativeSamples X k ω - (Q ω + a * (n : ℝ)) - a * (k : ℝ)| =
          |D (n + k) ω - (Q ω + a * ((n + k : ℕ) : ℝ))| := by
        rw [hshift]
        push_cast
        congr 1
        ring
      _ ≤ E := by simpa only [Nat.cast_zero, sub_zero] using! ha (n + k) hmem

end SwingRepair
