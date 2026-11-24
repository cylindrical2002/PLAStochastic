import PLAStochastic.Swing.FrozenCarry.NegativeCarry.LogBound
import PLAStochastic.Swing.Restart.Chain.MarkovLaw
import PLAStochastic.Swing.FirstSegment.LowerRejectionReflection
import PLAStochastic.Swing.FirstSegment.MarginAntiConcentration

/-! # Bridging the restart kernel mean to the frozen-carry mean

The restart chain records the actual carry `x`; the conditional-mean estimates
of Appendix C are stated for the allowance `w = x+E`.  The two maximal-prefix
lengths are pathwise equal, and the mean is symmetric under reflecting the
carry, so the negative-carry bound applies to `|x|`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

omit mΩ in
/-- The allowance and carry parameterisations describe the same actual cone. -/
theorem frozenPrefixFeasible_iff_restart (X : ℕ → Ω → ℝ) (E x : ℝ) (k : ℕ) (ω : Ω) :
    nativePrefixFeasible (fun j => (j : ℝ))
        (fun j => nativeCarriedSamples X (fun _ => x+E) j ω) E 0 (k+1) E ↔
      nativePrefixFeasible (fun j => (j : ℝ))
        (fun j => nativeCarriedSamples X (fun _ => x) j ω) E 0 (k+1) 0 := by
  constructor <;> rintro ⟨m, hm⟩ <;> refine ⟨m, fun j hj => ?_⟩ <;>
    have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1 <;>
    have hval := hm j hj <;>
    obtain ⟨i, rfl⟩ : ∃ i, j = i+1 := ⟨j-1, by omega⟩ <;>
    simp only [nativeCarriedSamples_succ, Nat.cast_zero, sub_zero] at hval ⊢
  · have he : x+cumulativeSamples X i ω-(0+m*((i+1 : ℕ) : ℝ)) =
        x+E+cumulativeSamples X i ω-(E+m*((i+1 : ℕ) : ℝ)) := by ring
    rw [he]
    exact hval
  · have he : x+E+cumulativeSamples X i ω-(E+m*((i+1 : ℕ) : ℝ)) =
        x+cumulativeSamples X i ω-(0+m*((i+1 : ℕ) : ℝ)) := by ring
    rw [he]
    exact hval

omit mΩ in
/-- Pathwise equality of the two maximal-prefix lengths. -/
theorem frozenPrefixLength_eq_nativeRestartLength (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) :
    frozenPrefixLength X (x+E) E ω = nativeRestartLength X E x ω := by
  unfold frozenPrefixLength nativeRestartLength nativePrefixLength
  congr 1
  funext k ω'
  exact congrArg Not (propext (frozenPrefixFeasible_iff_restart X E x k ω'))

omit mΩ in
theorem frozenPrefixLengthReal_eq_nativeRestartLengthNat (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) :
    frozenPrefixLengthReal X (x+E) E ω = (nativeRestartLengthNat X E x ω : ℝ) := by
  unfold frozenPrefixLengthReal nativeRestartLengthNat nativePrefixLengthNat
  rw [frozenPrefixLength_eq_nativeRestartLength X E x ω]
  rfl

/-- The restart kernel mean is the frozen-carry mean at the shifted allowance. -/
theorem nativeRestartMean_eq_frozen (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E x : ℝ) :
    nativeRestartMean X μ E x = ∫ ω, frozenPrefixLengthReal X (x+E) E ω ∂μ := by
  unfold nativeRestartMean
  exact (integral_congr_ae (Eventually.of_forall
    (fun ω => frozenPrefixLengthReal_eq_nativeRestartLengthNat X E x ω))).symm

/-! ## Reflection symmetry of the restart mean -/

omit mΩ in
theorem nativeCarriedSamples_neg_carry (X : ℕ → Ω → ℝ) (x : ℝ) (ω : Ω) :
    (fun j => nativeCarriedSamples (negIncrements X) (fun _ => -x) j ω) =
      (fun j => -(nativeCarriedSamples X (fun _ => x) j ω)) := by
  funext j
  cases j with
  | zero => simp [nativeCarriedSamples]
  | succ i =>
    simp only [nativeCarriedSamples_succ, cumulativeSamples_neg]
    ring

omit mΩ in
/-- Pathwise reflection of the actual maximal restart prefix. -/
theorem nativeRestartLength_neg (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) :
    nativeRestartLength (negIncrements X) E (-x) ω = nativeRestartLength X E x ω := by
  unfold nativeRestartLength nativePrefixLength
  congr 1
  funext k ω'
  refine congrArg Not (propext ?_)
  rw [nativeCarriedSamples_neg_carry X x ω']
  simpa using nativePrefixFeasible_neg (fun j => (j : ℝ))
    (fun j => nativeCarriedSamples X (fun _ => x) j ω') E 0 (k+1) 0

omit mΩ in
theorem nativeRestartLengthNat_neg (X : ℕ → Ω → ℝ) (E x : ℝ) (ω : Ω) :
    nativeRestartLengthNat (negIncrements X) E (-x) ω = nativeRestartLengthNat X E x ω := by
  unfold nativeRestartLengthNat nativePrefixLengthNat
  rw [show nativePrefixLength (nativeCarriedSamples (negIncrements X) (fun _ => -x)) (fun _ => 0) E ω
      = nativeRestartLength (negIncrements X) E (-x) ω from rfl,
    nativeRestartLength_neg X E x ω]
  rfl

/-- Negating every increment preserves the law of the whole iid Gaussian sequence. -/
theorem negSequence_identDistrib (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    IdentDistrib (fun ω (j : ℕ) => -X j ω) (fun ω (j : ℕ) => X j ω) μ μ := by
  have hneg : ∀ n, Measurable (fun ω => -X n ω) := fun n => (hX n).neg
  have hineg : iIndepFun (fun n ω => -X n ω) μ := by
    simpa only [Function.comp_def] using hi.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hGneg : ∀ n, μ.map (fun ω => -X n ω) = gaussianReal 0 1 := by
    intro n
    calc
      μ.map (fun ω => -X n ω) = Measure.map ((fun x : ℝ => -x) ∘ X n) μ := by rfl
      _ = Measure.map (fun x : ℝ => -x) (μ.map (X n)) := (Measure.map_map measurable_neg (hX n)).symm
      _ = Measure.map (fun x : ℝ => -x) (gaussianReal 0 1) := by rw [hG n]
      _ = gaussianReal 0 1 := by rw [gaussianReal_map_neg]; simp
  refine ⟨(measurable_pi_lambda _ hneg).aemeasurable, (measurable_pi_lambda _ hX).aemeasurable, ?_⟩
  rw [hineg.map_fun_eq_infinitePi_map hneg, hi.map_fun_eq_infinitePi_map hX]
  congr 1
  funext j
  rw [hGneg j, hG j]

/-- The actual conditional segment mean depends on the carry only through `|x|`. -/
theorem nativeRestartMean_neg [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (E x : ℝ) :
    nativeRestartMean X μ E (-x) = nativeRestartMean X μ E x := by
  set φ : (ℕ → ℝ) → ℝ := fun z => (nativeRestartLengthNat nativeIncrementCoordinates E (-x) z : ℝ)
    with hφdef
  have hφ : Measurable φ := by
    have h := nativeRestartLengthNat_measurable nativeIncrementCoordinates
      nativeIncrementCoordinates_measurable E
    exact (measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp
      (h.comp ((measurable_const (a := -x)).prodMk measurable_id))
  have hid := (negSequence_identDistrib hX hi hG).comp hφ
  have hint := hid.integral_eq
  have hlhs : (∫ ω, φ (fun j => -X j ω) ∂μ) = nativeRestartMean X μ E x := by
    unfold nativeRestartMean
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    show (nativeRestartLengthNat (negIncrements X) E (-x) ω : ℝ) = _
    rw [nativeRestartLengthNat_neg X E x ω]
  have hrhs : (∫ ω, φ (fun j => X j ω) ∂μ) = nativeRestartMean X μ E (-x) := rfl
  calc
    nativeRestartMean X μ E (-x) = ∫ ω, φ (fun j => X j ω) ∂μ := hrhs.symm
    _ = ∫ ω, φ (fun j => -X j ω) ∂μ := by
      simpa only [Function.comp_def] using hint.symm
    _ = nativeRestartMean X μ E x := hlhs

/-! ## The actual first carried state and its margin -/

/-- The restart mean at any carry equals the frozen mean at the output margin. -/
theorem nativeRestartMean_eq_frozen_margin [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (E x : ℝ) :
    nativeRestartMean X μ E x = ∫ ω, frozenPrefixLengthReal X (E-|x|) E ω ∂μ := by
  rcases le_or_gt x 0 with hx | hx
  · rw [abs_of_nonpos hx, nativeRestartMean_eq_frozen X μ E x]
    congr 1
    funext ω
    congr 1
    ring
  · rw [abs_of_pos hx, ← nativeRestartMean_neg hX hi hG E x,
      nativeRestartMean_eq_frozen X μ E (-x)]
    congr 1
    funext ω
    congr 1
    ring

/-- The state after the first actual recording is the genuine first carried value. -/
theorem nativeRestartRecordingState_one_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    ∀ᵐ ω ∂μ, nativeRestartRecordingState X E 1 ω = nativeFirstNext X E ω := by
  filter_upwards [nativeRestartRecordingState_succ_ae hX hi hG hE 0] with ω hω
  rw [hω, nativeRestartRecordingState_zero, nativeRecordingTime_zero]
  rfl

/-- The second actual segment has mean `E[g_E(R_1)]` for the genuine first margin. -/
theorem secondSegment_mean_eq
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) :
    (∫ ω, (nativeRecordingDurationNat X E 1 ω : ℝ) ∂μ) =
      ∫ ω, (∫ ω', frozenPrefixLengthReal X (nativeFirstMargin X E ω) E ω' ∂μ) ∂μ := by
  have hprob := hi.isProbabilityMeasure
  have hmap : (∫ x, nativeRestartMean X μ E x ∂μ.map (nativeRestartRecordingState X E 1)) =
      ∫ ω, nativeRestartMean X μ E (nativeRestartRecordingState X E 1 ω) ∂μ := by
    rw [integral_map (nativeRestartRecordingState_measurable hX E 1).aemeasurable
      (nativeRestartMean_measurable hX E).aestronglyMeasurable]
  rw [nativeRecordingDurationNat_mean hX hi hG hE 1, hmap]
  refine integral_congr_ae ?_
  filter_upwards [nativeRestartRecordingState_one_ae hX hi hG hE] with ω hω
  rw [hω, nativeRestartMean_eq_frozen_margin hX hi hG E (nativeFirstNext X E ω)]
  rfl

end SwingRepair
