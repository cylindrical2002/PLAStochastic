import PLAStochastic.Swing.StationaryLimit.PrefixCrossing.LocalErrorBridge
import PLAStochastic.Swing.FrozenCarry.Interior.GoodTail

/-!
# Deterministic lower-bridge interfaces

The lower-bridge probability estimate is still a separate input to the native
kernel theorem.  These small wrappers expose the consequences of the already
proved early-slope localization event that are repeatedly needed by that
estimate: the prefix slope is in its compact interval and every later carried
point lies below the same lower cone.  No probability or asymptotic claim is
made here.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def finiteCumulativeEnvelope (X : ℕ → Ω → ℝ) (J : ℕ) (Q : ℝ) : Set Ω :=
  {ω | ∀ n < J, |cumulativeSamples X n ω| ≤ Q}

theorem finiteCumulativeEnvelope_compl_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {J : ℕ} (hJ : 0 < J) {Q : ℝ} (hQ : 0 ≤ Q) :
    μ.real (finiteCumulativeEnvelope X J Q)ᶜ ≤
      2 * (J : ℝ) * Real.exp (-Q^2/(2*(J : ℝ))) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hcover : (finiteCumulativeEnvelope X J Q)ᶜ ⊆
      ⋃ n ∈ Finset.range J, {ω | Q ≤ |cumulativeSamples X n ω|} := by
    intro ω hω
    have hfail : ¬ ∀ n < J, |cumulativeSamples X n ω| ≤ Q := by
      simpa [finiteCumulativeEnvelope] using hω
    push Not at hfail
    obtain ⟨n, hn, hbad⟩ := hfail
    refine mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨Finset.mem_range.mpr hn, ?_⟩⟩
    exact hbad.le
  have hterm (n : ℕ) (hn : n ∈ Finset.range J) :
      μ.real {ω | Q ≤ |cumulativeSamples X n ω|} ≤
        2 * Real.exp (-Q^2/(2*(J : ℝ))) := by
    by_cases hn0 : n = 0
    · subst n
      by_cases hQpos : 0 < Q
      · have hempty : {ω | Q ≤ |cumulativeSamples X 0 ω|} = ∅ := by
          ext ω
          simp only [cumulativeSamples_zero, abs_zero, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false]
          exact not_le.mpr hQpos
        rw [hempty, measureReal_empty]
        positivity
      · have hQzero : Q = 0 := le_antisymm (le_of_not_gt hQpos) hQ
        have hone : μ.real {ω | Q ≤ |cumulativeSamples X 0 ω|} ≤ 1 :=
          measureReal_le_one
        rw [hQzero]
        norm_num
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
      have hnle : (n : ℝ) ≤ J := by
        exact_mod_cast (Finset.mem_range.mp hn).le
      have htail := cumulativeSamples_abs_tail_bound hX hi hG n hQ
      refine htail.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hden := div_le_div_of_nonneg_left (sq_nonneg Q)
        (by positivity : 0 < 2*(n : ℝ))
        (by nlinarith : 2*(n : ℝ) ≤ 2*(J : ℝ))
      have hexp := Real.exp_le_exp.mpr (neg_le_neg hden)
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hexp
  calc
    μ.real (finiteCumulativeEnvelope X J Q)ᶜ ≤
        μ.real (⋃ n ∈ Finset.range J,
          {ω | Q ≤ |cumulativeSamples X n ω|}) :=
      measureReal_mono hcover (measure_ne_top μ _)
    _ ≤ ∑ n ∈ Finset.range J,
          μ.real {ω | Q ≤ |cumulativeSamples X n ω|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ n ∈ Finset.range J,
          2 * Real.exp (-Q^2/(2*(J : ℝ))) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hterm n hn
    _ = 2 * (J : ℝ) * Real.exp (-Q^2/(2*(J : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

omit [MeasurableSpace Ω] in
theorem finiteCumulativeEnvelope_controls_prefix
    {X : ℕ → Ω → ℝ} {J : ℕ} {Q : ℝ} {ω : Ω}
    (hω : ω ∈ finiteCumulativeEnvelope X J Q) :
    ∀ i ∈ Finset.Icc 1 (J-1),
      |cumulativeSamples X (i-1) ω| ≤ Q := by
  intro i hi
  have hiI := Finset.mem_Icc.mp hi
  exact hω (i-1) (by omega)

omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_bounds_of_earlySlopeGood
    {X : ℕ → Ω → ℝ} {r K δ M : ℝ} {J : ℕ} (ω : Ω)
    (hJ : 1 ≤ J) (hδ : 0 < δ)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hr : |r| ≤ K) :
    δ ≤ prefixCrossingSlope X r J ω ∧
      prefixCrossingSlope X r J ω ≤ M := by
  have hloc := swingEarlySlope_localization (X := X) (K₀ := K)
    (δ := δ) (M := M) (J := J-1) hδ hgood hr
  rw [prefixCrossingSlope_eq_early (X := X) (r := r) (J := J) hJ]
  exact ⟨by linarith [hloc.2.1], by linarith [hloc.2.2]⟩

omit [MeasurableSpace Ω] in
theorem prefixCrossingSlope_pos_of_earlySlopeGood
    {X : ℕ → Ω → ℝ} {r K δ M : ℝ} {J : ℕ} (ω : Ω)
    (hJ : 1 ≤ J) (hδ : 0 < δ)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hr : |r| ≤ K) :
    0 < prefixCrossingSlope X r J ω := by
  exact lt_of_lt_of_le hδ
    (prefixCrossingSlope_bounds_of_earlySlopeGood ω hJ hδ hgood hr).1

omit [MeasurableSpace Ω] in
theorem prefixCrossing_lower_future_of_earlySlopeGood_unbounded
    {X : ℕ → Ω → ℝ} {E r K δ M : ℝ} {J : ℕ} (ω : Ω)
    (hJ : 1 ≤ J) (hδ : 0 < δ)
    (hgood : ω ∈ swingEarlySlopeGood X K δ M (J-1))
    (hr : |r| ≤ K) :
    ∀ i : ℕ, J ≤ i →
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ prefixCrossingSlope X r J ω := by
  intro i hi
  exact prefixCrossing_lower_future_of_earlySlopeGood
    (X := X) (E := E) (r := r) (K := K) (δ := δ) (M := M)
    (J := J) (N := i) ω hJ hi hδ hgood hr i
      (Finset.mem_Icc.mpr ⟨hi, le_rfl⟩)

/-! The next event records only the finite envelope and first-passage checks
that are not consequences of `swingEarlySlopeGood`.  The slope upper bound,
positivity, lower-cone inequalities, and an attaining prefix point are all
recovered deterministically in the inclusion theorem below. -/

def prefixCrossingLowerBridgeEnvelopeEvent
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    (K δ Q M η : ℝ) : Set Ω :=
  {ω | ω ∈ swingEarlySlopeGood X K δ M (J-1) ∧
    (∀ i ∈ Finset.Icc 1 (J-1),
      |cumulativeSamples X (i-1) ω| ≤ Q) ∧
    ∃ k : ℕ,
      1 ≤ J - 1 + k ∧
      (∀ i ∈ Finset.Icc 1 (J - 1 + k),
        |cumulativeSamples X (i-1) ω| ≤ Q + η * (i : ℝ)) ∧
      3 * (E-r+Q) / (2 * ((J - 1 + k : ℕ) : ℝ) + 1) + η ≤
        prefixCrossingSlope X r J ω ∧
      0 < prefixCrossingSlope X r J ω ∧
      0 < prefixCrossingLevel X E r J ω ∧
      prefixCrossingSlope X r J ω ≤ E ∧
      (∃ m : ℕ,
        prefixCrossingLevel X E r J ω <
          gaussianDriftWalk
            (negIncrements (fun q => X (J - 1 + q))) 0
            (prefixCrossingSlope X r J ω) m ω) ∧
      gaussianWalkPassage
        (negIncrements (fun q => X (J - 1 + q)))
        (prefixCrossingSlope X r J ω)
        (prefixCrossingLevel X E r J ω) ω = k}

omit [MeasurableSpace Ω] in
theorem prefixCrossingLowerBridgeEnvelopeEvent_subset
    {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ Q M η : ℝ} (hJ : 1 ≤ J) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hr : |r| ≤ K) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hbudget : M * (J : ℝ) ≤ 2*E - K - Q) :
    prefixCrossingLowerBridgeEnvelopeEvent (X := X) E r J K δ Q M η ⊆
      prefixCrossingLowerBridgeEventRandom X E r J := by
  intro ω hω
  rcases hω with ⟨hgood, hWprefix, k, hN, hWglobal, hlsbound,
    ha, hb, haE, hcross, hpass⟩
  have hbounds := prefixCrossingSlope_bounds_of_earlySlopeGood
    (X := X) (r := r) (K := K) (δ := δ) (M := M)
    (J := J) ω hJ hδ hgood hr
  have hA : prefixCrossingSlope X r J ω ≤ M := hbounds.2
  have hlower_all := prefixCrossing_lower_future_of_earlySlopeGood_unbounded
    (X := X) (E := E) (r := r) (K := K) (δ := δ) (M := M)
    (J := J) ω hJ hδ hgood hr
  have hlower_future : ∀ i ∈ Finset.Icc J (J - 1 + k),
      slopeLower (i : ℝ) (nativeCarriedSamples X (fun _ => E-r) i ω)
        0 0 E ≤ prefixCrossingSlope X r J ω := by
    intro i hi
    exact hlower_all i (Finset.mem_Icc.mp hi).1
  have hi₀ := prefixCrossingSlope_attained_lower_cone
    (X := X) (E := E) (r := r) (J := J) hJ ω
  exact prefixCrossingLowerBridgeEventRandom_of_envelopes
    (X := X) E r J k ω hJ hE hN hr hK hQ hM hη hA hWprefix hbudget hWglobal
    hlsbound hlower_future hi₀ ha hb haE hcross hpass

theorem prefixCrossingLowerBridgeEventRandom_compl_measure_le_envelope_compl
    [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ} (E r : ℝ) (J : ℕ)
    {K δ Q M η : ℝ} (hJ : 1 ≤ J) (hδ : 0 < δ) (hE : 0 ≤ E)
    (hr : |r| ≤ K) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hbudget : M * (J : ℝ) ≤ 2*E - K - Q) :
    μ.real (prefixCrossingLowerBridgeEventRandom X E r J)ᶜ ≤
      μ.real (prefixCrossingLowerBridgeEnvelopeEvent (X := X) E r J K δ Q M η)ᶜ := by
  exact measureReal_mono
    (Set.compl_subset_compl.mpr
      (prefixCrossingLowerBridgeEnvelopeEvent_subset E r J hJ hδ hE hr hK hQ hM hη
        hbudget))
    (measure_ne_top μ _)

end SwingRepair
