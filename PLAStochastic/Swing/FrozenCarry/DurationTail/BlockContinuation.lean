import PLAStochastic.Swing.FrozenCarry.DurationTail.BridgeTail

/-! Continuing the actual frozen tail by fresh three-point blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenPrefixLength_measurable (hX : ∀ n, Measurable (X n)) (w E : ℝ) :
    Measurable (frozenPrefixLength X w E) :=
  nativePrefixLength_measurable _ _ (nativeCarriedSamples_measurable hX measurable_const) measurable_const E

theorem frozenPrefixLength_tail_measurable (hX : ∀ n, Measurable (X n)) (w E : ℝ) (n : ℕ) :
    MeasurableSet {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω} :=
  measurableSet_le measurable_const (frozenPrefixLength_measurable hX w E)

/-- The geometric continuation retains the small probability of surviving to its actual start. -/
theorem frozenPrefixLength_block_continuation
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w : ℝ) {E : ℝ} (hE : 0 < E) {n : ℕ} (hn : 1 ≤ n) (b : ℕ) :
    μ.real {ω | ((n+2*⌈8*E^2⌉₊*b : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}*gaussianBlockPass.toReal^b := by
  have := hi.isProbabilityMeasure
  have hc := nativeCarriedPrefix_conditional_bound hX hi hG (m := ⊥) bot_le
    (indep_bot_right _) (x := fun _ => w) (Q := fun _ => E) measurable_const measurable_const hn hE b
  have hA := frozenPrefixLength_tail_measurable hX w E n
  have hB := frozenPrefixLength_tail_measurable hX w E (n+2*⌈8*E^2⌉₊*b)
  have hm : nativeCarriedHistory X (fun _ => w) ⊥ n ≤ mΩ := by
    rw [nativeCarriedHistory_eq (show Measurable[⊥] (fun _ : Ω => w) from measurable_const), bot_sup_eq]
    exact incrementIndexSpace_le hX _
  have hh := integral_mono_ae integrable_condExp
    ((integrable_const (gaussianBlockPass.toReal^b)).indicator hA) hc
  rw [integral_condExp hm] at hh
  dsimp only [frozenPrefixLength] at hA hB hh ⊢
  rw [integral_indicator_const _ hB, integral_indicator_const _ hA,
    smul_eq_mul, smul_eq_mul, mul_one] at hh
  exact hh


theorem frozenPrefixLength_block_continuation_enn
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w : ℝ) {E : ℝ} (hE : 0 < E) {n : ℕ} (hn : 1 ≤ n) (b : ℕ) :
    μ {ω | ((n+2*⌈8*E^2⌉₊*b : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω} ≤
      μ {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}*gaussianBlockPass^b := by
  have := hi.isProbabilityMeasure
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ?_).mp
  · simpa only [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_pow] using
      frozenPrefixLength_block_continuation hX hi hG w hE hn b
  · exact ENNReal.mul_ne_top (measure_ne_top _ _)
      (ENNReal.pow_ne_top (ne_top_of_lt (gaussianBlockPass_lt_one.trans ENNReal.one_lt_top)))

end SwingRepair
