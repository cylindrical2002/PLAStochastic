import PLAStochastic.ForMathlib.Probability.Moments.NatWeightedBlockTail
import PLAStochastic.ForMathlib.Probability.Process.CappedStopping.Mean

/-! A finite head and weighted geometric continuation bound the actual natural-valued mean. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_natCast_le_head_add_weighted_tail [IsProbabilityMeasure μ]
    {K : Ω → ℕ} (hK : Measurable K) (hKi : Integrable (fun ω => (K ω : ℝ)) μ)
    (n : ℕ) {L : ℕ} (hL : 0 < L) {q A : ℝ≥0∞} (hq : q < 1) (hA : A ≠ ⊤)
    (htail : ∀ k : ℕ, μ {ω | L*k < K ω-n} ≤ A*q^k) :
    (∫ ω, (K ω : ℝ) ∂μ) ≤
      (∑ j ∈ Finset.range n, μ.real {ω | j < K ω})+(L : ℝ)*A.toReal/(1-q.toReal) := by
  have hR : Measurable (fun ω => K ω-n) := (measurable_from_nat : Measurable (fun k : ℕ => k-n)).comp hK
  have hRi : Integrable (fun ω => ((K ω-n : ℕ) : ℝ)) μ := by
    apply hKi.mono' (measurable_from_nat.comp hR).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      dsimp only [Function.comp_def]
      rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast Nat.sub_le (K ω) n)
  have hT : Measurable (fun ω => (K ω : WithTop ℕ)) := measurable_from_nat.comp hK
  have hc := capDiscreteTime_integrable (μ := μ) hT n
  have he (ω : Ω) : (K ω : ℝ) = (capDiscreteTime (K ω : WithTop ℕ) n : ℝ)+((K ω-n : ℕ) : ℝ) := by
    have hh := Nat.sub_add_min_cancel (K ω) n
    dsimp only [capDiscreteTime, WithTop.untopD_coe]
    exact_mod_cast (show K ω = min n (K ω)+(K ω-n) by omega)
  rw [integral_congr_ae (ae_of_all _ he), integral_add hc hRi, integral_capDiscreteTime hT]
  have hs : (∑ k ∈ Finset.range n, μ.real {ω | (k : WithTop ℕ) < (K ω : WithTop ℕ)}) =
      ∑ k ∈ Finset.range n, μ.real {ω | k < K ω} := by
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    ext ω
    exact WithTop.coe_lt_coe
  rw [hs]
  have hh := integral_natCast_le_weighted_geometric_block_tail hR hL hq hA htail
  linarith

end SwingRepair
