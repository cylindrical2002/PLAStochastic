import PLAStochastic.Swing.FrozenCarry.DurationTail.UniformMeanBound
import PLAStochastic.ForMathlib.NumberTheory.Harmonic.ReciprocalSumLogRatio

/-! Harmonic survival mass on an interval beginning at the linear scale. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenPrefixLength_harmonic_interval
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) {E : ℝ}
    (hE : 1 ≤ E) {k m : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m)
    (hmE : (m : ℝ) ≤ E^2+1) :
    (∑ j ∈ Finset.Ico k m,
      μ.real {ω | j < (frozenPrefixLength X w E ω).untopD 0}) ≤
      frozenHarmonicTailConstant*(1+max w 0)*E *
        Real.log ((m : ℝ)/(k : ℝ)) := by
  have hprob := hi.isProbabilityMeasure
  have hsum : (∑ j ∈ Finset.Ico k m,
      μ.real {ω | j < (frozenPrefixLength X w E ω).untopD 0}) ≤
      ∑ j ∈ Finset.Ico k m,
        frozenHarmonicTailConstant*(1+max w 0)*E/((j+1 : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjk : k ≤ j := (Finset.mem_Ico.mp hj).1
    have hjm : j < m := (Finset.mem_Ico.mp hj).2
    have hj1 : 0 < j+1 := by omega
    have hj1E : ((j+1 : ℕ) : ℝ) ≤ E^2+1 := by
      have h : j+1 ≤ m := by omega
      have hcast : ((j+1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      exact hcast.trans hmE
    have ht := frozenPrefixLength_harmonic_tail hX hi hG w hE hj1 hj1E
    have htail := (measureReal_mono (frozenPrefixLength_nat_tail_subset X w E j)).trans ht
    exact htail
  · calc
      _ ≤ ∑ j ∈ Finset.Ico k m,
          frozenHarmonicTailConstant*(1+max w 0)*E/((j+1 : ℕ) : ℝ) := hsum
      _ = frozenHarmonicTailConstant*(1+max w 0)*E *
          (∑ j ∈ Finset.Ico k m, ((j+1 : ℕ) : ℝ)⁻¹) := by
        simp only [div_eq_mul_inv]
        rw [Finset.mul_sum]
      _ ≤ _ := by
        have hC : 0 ≤ frozenHarmonicTailConstant*(1+max w 0)*E := by
          have hc := frozenHarmonicTailConstant_pos
          have hw := le_max_right w 0
          positivity
        gcongr
        exact reciprocal_sum_Ico_le_log_ratio hk hkm
end SwingRepair
