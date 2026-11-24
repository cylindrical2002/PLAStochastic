import PLAStochastic.ForMathlib.Probability.Moments.NatGeometricBlockTail

/-! Geometric continuation bounds with the probability of reaching the block start retained. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_natCast_le_weighted_geometric_block_tail
    {K : Ω → ℕ} (hK : Measurable K) {L : ℕ} (hL : 0 < L) {q A : ℝ≥0∞}
    (htail : ∀ k : ℕ, μ {ω | L*k < K ω} ≤ A*q^k) :
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) ≤ (L : ℝ≥0∞)*A/(1-q) := by
  let S : ℕ → Set Ω := fun k => {ω | L*k < K ω}
  let F : ℕ → Ω → ℝ≥0∞ := fun k => (S k).indicator (fun _ => 1)
  have hS (k : ℕ) : MeasurableSet (S k) := measurableSet_lt measurable_const hK
  have hF (k : ℕ) : Measurable (F k) := measurable_const.indicator (hS k)
  calc
    _ ≤ ∫⁻ ω, (L : ℝ≥0∞)*∑' k : ℕ, F k ω ∂μ := by
      apply lintegral_mono
      intro ω
      simpa only [F, S, Set.indicator_apply, Set.mem_ofPred_eq] using nat_le_block_tail_sum (K ω) L hL
    _ = (L : ℝ≥0∞)*∑' k : ℕ, μ {ω | L*k < K ω} := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_tsum (fun k => (hF k).aemeasurable)]
      congr 1
      apply tsum_congr
      intro k
      exact lintegral_indicator_fun_one (hS k)
    _ ≤ (L : ℝ≥0∞)*∑' k : ℕ, A*q^k := mul_le_mul_right (ENNReal.tsum_le_tsum htail) _
    _ = _ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]; simp only [div_eq_mul_inv, mul_assoc]

theorem integral_natCast_le_weighted_geometric_block_tail
    {K : Ω → ℕ} (hK : Measurable K) {L : ℕ} (hL : 0 < L) {q A : ℝ≥0∞}
    (hq : q < 1) (hA : A ≠ ⊤) (htail : ∀ k : ℕ, μ {ω | L*k < K ω} ≤ A*q^k) :
    (∫ ω, (K ω : ℝ) ∂μ) ≤ (L : ℝ)*A.toReal/(1-q.toReal) := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => Nat.cast_nonneg (K ω)))
    (measurable_from_nat.comp hK).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  have hfin : (L : ℝ≥0∞)*A/(1-q) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (by simp) hA) (tsub_pos_of_lt hq).ne'
  have hh := ENNReal.toReal_mono hfin (lintegral_natCast_le_weighted_geometric_block_tail hK hL htail)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_sub_of_le hq.le (by simp), ENNReal.toReal_one] using hh

end SwingRepair
