import PLAStochastic.Swing.FrozenCarry.DurationTail.MeanArithmetic
import PLAStochastic.Swing.FrozenCarry.DurationTail.BlockContinuation
import PLAStochastic.ForMathlib.Probability.Moments.NatMeanHeadTailSplit
import PLAStochastic.Swing.FrozenCarry.Path.LengthLimit

/-! The actual frozen Gaussian segment has the uniform E log(e E) conditional mean bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenPrefixLengthReal_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) {E : ℝ} (hE : 0 < E) :
    Integrable (frozenPrefixLengthReal X w E) μ := by
  exact nativePrefixLengthNat_integrable hX hi hG
    (nativeCarriedSamples X (fun _ => w)) (fun _ => E)
    (nativeCarriedSamples_measurable hX measurable_const) measurable_const
    (fun ω k => by simpa using nativeCarriedSamples_shift X (fun _ => w) (n := 1) (by omega) ω k)
    hE _ (Nat.le_ceil (8*E^2))

omit mΩ in
theorem frozenPrefixLength_nat_tail_subset (X : ℕ → Ω → ℝ) (w E : ℝ) (n : ℕ) :
    {ω | n < (frozenPrefixLength X w E ω).untopD 0} ⊆
      {ω | ((n+1 : ℕ) : WithTop ℕ) ≤ frozenPrefixLength X w E ω} := by
  intro ω hω
  cases ht : frozenPrefixLength X w E ω using WithTop.recTopCoe with
  | top => simp [ht]
  | coe k =>
    simp only [Set.mem_ofPred_eq, ht, WithTop.untopD_coe] at hω
    change ((n+1 : ℕ) : WithTop ℕ) ≤ _
    rw [ht]
    exact (WithTop.coe_le_coe.mpr (show n+1 ≤ k by omega) :
      ((n+1 : ℕ) : WithTop ℕ) ≤ (k : WithTop ℕ))

theorem frozenPrefixLength_mean_head_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) {E : ℝ} (hE : 1 ≤ E) :
    (∑ j ∈ Finset.range ⌈E^2⌉₊, μ.real {ω | j < (frozenPrefixLength X w E ω).untopD 0}) ≤
      frozenHarmonicTailConstant*(1+max w 0)*E * (1+Real.log (⌈E^2⌉₊ : ℝ)) := by
  have := hi.isProbabilityMeasure
  calc
    _ ≤ ∑ j ∈ Finset.range ⌈E^2⌉₊,
        frozenHarmonicTailConstant*(1+max w 0)*E/(j+1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j hj
      exact (measureReal_mono (frozenPrefixLength_nat_tail_subset X w E j)).trans
        (frozenPrefixLength_harmonic_tail hX hi hG w hE (by omega) (by
          have hjn : j+1 ≤ ⌈E^2⌉₊ := by simpa using hj
          exact (by exact_mod_cast hjn : (j+1 : ℕ) ≤ (⌈E^2⌉₊ : ℝ)).trans (frozen_cutoff_le hE)))
    _ = frozenHarmonicTailConstant*(1+max w 0)*E*(harmonic ⌈E^2⌉₊ : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Nat.cast_add,
        Nat.cast_one, div_eq_mul_inv, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by
      have := frozenHarmonicTailConstant_pos
      have := le_max_right w 0
      positivity)


theorem frozenPrefixLength_mean_tail_split
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) {E : ℝ} (hE : 0 < E)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ ω, frozenPrefixLengthReal X w E ω ∂μ) ≤
      (∑ j ∈ Finset.range n, μ.real {ω | j < (frozenPrefixLength X w E ω).untopD 0})+
      2*(⌈8*E^2⌉₊ : ℝ)*μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}/
        (1-gaussianBlockPass.toReal) := by
  have := hi.isProbabilityMeasure
  have hrp : 0 < 2*⌈8*E^2⌉₊ := Nat.mul_pos (by omega) (Nat.ceil_pos.mpr (by positivity))
  have hh := integral_natCast_le_head_add_weighted_tail
    ((frozenPrefixLength_measurable hX w E).untopD 0)
    (frozenPrefixLengthReal_integrable hX hi hG w hE) n hrp gaussianBlockPass_lt_one
    (measure_ne_top μ {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}) (fun k => ?_)
  · simpa only [Nat.cast_mul, Nat.cast_ofNat, Measure.real] using! hh
  · apply le_trans (measure_mono ?_) (frozenPrefixLength_block_continuation_enn hX hi hG w hE hn k)
    intro ω hω
    cases ht : frozenPrefixLength X w E ω using WithTop.recTopCoe with
    | top => simp [ht]
    | coe l =>
      simp only [Set.mem_ofPred_eq, ht, WithTop.untopD_coe] at hω
      change ((n+2*⌈8*E^2⌉₊*k : ℕ) : WithTop ℕ) ≤ _
      rw [ht]
      exact (WithTop.coe_le_coe.mpr (show n+2*⌈8*E^2⌉₊*k ≤ l by omega) :
        ((n+2*⌈8*E^2⌉₊*k : ℕ) : WithTop ℕ) ≤ (l : WithTop ℕ))

theorem frozen_block_ratio_lt_one : gaussianBlockPass.toReal < 1 := by
  have hh := ENNReal.toReal_strict_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) gaussianBlockPass_lt_one
  simpa only [ENNReal.toReal_one] using hh

def frozenUniformMeanConstant : ℝ :=
  frozenHarmonicTailConstant*(2+18/(1-gaussianBlockPass.toReal))

theorem frozenUniformMeanConstant_pos : 0 < frozenUniformMeanConstant := by
  have := frozenHarmonicTailConstant_pos
  have := frozen_block_ratio_lt_one
  unfold frozenUniformMeanConstant
  positivity

/-- The uniform conditional-duration bound, now for the actual maximal frozen segment.
It holds for all carried values, and even all budgets E≥1. -/
theorem frozenPrefixLength_uniform_mean_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) {E : ℝ} (hE : 1 ≤ E) :
    (∫ ω, frozenPrefixLengthReal X w E ω ∂μ) ≤
      frozenUniformMeanConstant*E*(1+max w 0)*Real.log (Real.exp 1*E) := by
  have := hi.isProbabilityMeasure
  have hEp : 0 < E := by linarith
  have hn := frozen_cutoff_pos hE
  have hnR : (0 : ℝ) < ⌈E^2⌉₊ := by exact_mod_cast hn
  have hq : 0 < 1-gaussianBlockPass.toReal := sub_pos.mpr frozen_block_ratio_lt_one
  have hp := frozenPrefixLength_harmonic_tail hX hi hG w hE hn (frozen_cutoff_le hE)
  have hs := frozenPrefixLength_mean_tail_split hX hi hG w hEp (Nat.one_le_iff_ne_zero.mpr hn.ne')
  have hh := frozenPrefixLength_mean_head_bound hX hi hG w hE
  let B : ℝ := frozenHarmonicTailConstant*(1+max w 0)*E
  let Z : ℝ := Real.log (Real.exp 1*E)
  have hB : 0 ≤ B := by dsimp [B]; have := frozenHarmonicTailConstant_pos; have := le_max_right w 0; positivity
  have hz : 1 ≤ Z := frozen_log_scale_ge_one hE
  have ht : 2*(⌈8*E^2⌉₊ : ℝ)*μ.real {ω | (⌈E^2⌉₊ : WithTop ℕ) ≤ frozenPrefixLength X w E ω}/
      (1-gaussianBlockPass.toReal) ≤ 18*B/(1-gaussianBlockPass.toReal) := by
    calc
      _ ≤ 2*(⌈8*E^2⌉₊ : ℝ)*(B/(⌈E^2⌉₊ : ℝ))/(1-gaussianBlockPass.toReal) := by gcongr
      _ = (2*(⌈8*E^2⌉₊ : ℝ)/(⌈E^2⌉₊ : ℝ))*B/(1-gaussianBlockPass.toReal) := by ring
      _ ≤ _ := by gcongr; exact frozen_block_cutoff_ratio_le hE
  have hhead : (∑ j ∈ Finset.range ⌈E^2⌉₊, μ.real {ω | j < (frozenPrefixLength X w E ω).untopD 0}) ≤
      2*B*Z := by
    calc
      _ ≤ B*(1+Real.log (⌈E^2⌉₊ : ℝ)) := hh
      _ ≤ B*(2*Z) := mul_le_mul_of_nonneg_left (frozen_cutoff_log_le hE) hB
      _ = _ := by ring
  have htail : 18*B/(1-gaussianBlockPass.toReal) ≤ 18*B/(1-gaussianBlockPass.toReal)*Z :=
    le_mul_of_one_le_right (by positivity) hz
  calc
    _ ≤ 2*B*Z+18*B/(1-gaussianBlockPass.toReal) := by linarith
    _ ≤ 2*B*Z+18*B/(1-gaussianBlockPass.toReal)*Z := by linarith
    _ = _ := by dsimp [B, Z, frozenUniformMeanConstant]; ring

end SwingRepair
