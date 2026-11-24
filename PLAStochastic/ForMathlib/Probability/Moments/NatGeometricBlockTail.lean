import PLAStochastic.ForMathlib.Probability.Moments.NatGeometricEvenTail

noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair

/-- Counting thresholds in blocks of length L bounds every natural number, without an extra 1. -/
theorem nat_le_block_tail_sum (m L : ℕ) (hL : 0 < L) :
    (m : ℝ≥0∞) ≤ (L : ℝ≥0∞) * ∑' k : ℕ, if L * k < m then (1 : ℝ≥0∞) else 0 := by
  by_cases hm : m = 0
  · simp [hm]
  have hcount : (((m - 1) / L + 1 : ℕ) : ℝ≥0∞) ≤
      ∑' k : ℕ, if L * k < m then (1 : ℝ≥0∞) else 0 := by
    have heq : (∑ k ∈ Finset.range ((m - 1) / L + 1),
        if L * k < m then (1 : ℝ≥0∞) else 0) = ((m - 1) / L + 1 : ℕ) := by
      calc
        _ = ∑ _k ∈ Finset.range ((m - 1) / L + 1), (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [if_pos]
          have hk' : k ≤ (m - 1) / L := by have := Finset.mem_range.mp hk; omega
          have hkL := Nat.mul_le_mul_left L hk'
          have hdiv := Nat.mul_div_le (m - 1) L
          omega
        _ = ((m - 1) / L + 1 : ℕ) := by simp
    rw [← heq]
    exact ENNReal.sum_le_tsum _
  have hnat : m ≤ L * ((m - 1) / L + 1) := by
    have hmod := Nat.mod_lt (m - 1) hL
    have heq := Nat.div_add_mod (m - 1) L
    rw [Nat.mul_add, Nat.mul_one]
    omega
  apply le_trans (show (m : ℝ≥0∞) ≤ (L : ℝ≥0∞) * (((m - 1) / L + 1 : ℕ) : ℝ≥0∞) by
    exact_mod_cast hnat)
  exact mul_le_mul_right hcount _

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A uniform geometric block tail gives the exact L/(1-q) upper bound for the nonnegative mean. -/
theorem lintegral_natCast_le_geometric_block_tail
    {K : Ω → ℕ} (hK : Measurable K) {L : ℕ} (hL : 0 < L) {q : ℝ≥0∞}
    (htail : ∀ k : ℕ, μ {ω | L * k < K ω} ≤ q ^ k) :
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) ≤ (L : ℝ≥0∞) / (1 - q) := by
  let S : ℕ → Set Ω := fun k => {ω | L * k < K ω}
  let F : ℕ → Ω → ℝ≥0∞ := fun k => (S k).indicator (fun _ => 1)
  have hS (k : ℕ) : MeasurableSet (S k) := measurableSet_lt measurable_const hK
  have hF (k : ℕ) : Measurable (F k) := measurable_const.indicator (hS k)
  calc
    (∫⁻ ω, (K ω : ℝ≥0∞) ∂μ) ≤ ∫⁻ ω, (L : ℝ≥0∞) * ∑' k : ℕ, F k ω ∂μ := by
      apply lintegral_mono
      intro ω
      simpa only [F, S, Set.indicator_apply, Set.mem_ofPred_eq] using nat_le_block_tail_sum (K ω) L hL
    _ = (L : ℝ≥0∞) * ∑' k : ℕ, μ {ω | L * k < K ω} := by
      rw [lintegral_const_mul' _ _ (by simp), lintegral_tsum (fun k => (hF k).aemeasurable)]
      congr 1
      apply tsum_congr
      intro k
      exact lintegral_indicator_fun_one (hS k)
    _ ≤ (L : ℝ≥0∞) * ∑' k : ℕ, q ^ k := mul_le_mul_right (ENNReal.tsum_le_tsum htail) _
    _ = (L : ℝ≥0∞) / (1 - q) := by rw [ENNReal.tsum_geometric, div_eq_mul_inv]

/-- The Gaussian block estimate is strong enough to prove integrability, independently of any limit theorem. -/
theorem integrable_natCast_of_geometric_block_tail
    {K : Ω → ℕ} (hK : Measurable K) {L : ℕ} (hL : 0 < L) {q : ℝ≥0∞} (hq : q < 1)
    (htail : ∀ k : ℕ, μ {ω | L * k < K ω} ≤ q ^ k) :
    Integrable (fun ω => (K ω : ℝ)) μ := by
  have hmeas : Measurable (fun ω => (K ω : ℝ)) := measurable_from_nat.comp hK
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simp only [Real.norm_eq_abs, Nat.abs_cast, ENNReal.ofReal_natCast]
  apply lt_of_le_of_lt (lintegral_natCast_le_geometric_block_tail hK hL htail)
  exact ENNReal.div_lt_top (by simp) (tsub_pos_of_lt hq).ne'

/-- The exact real-valued expectation upper bound L/(1-q). -/
theorem integral_natCast_le_geometric_block_tail
    {K : Ω → ℕ} (hK : Measurable K) {L : ℕ} (hL : 0 < L) {q : ℝ≥0∞} (hq : q < 1)
    (htail : ∀ k : ℕ, μ {ω | L * k < K ω} ≤ q ^ k) :
    (∫ ω, (K ω : ℝ) ∂μ) ≤ (L : ℝ) / (1 - q.toReal) := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => Nat.cast_nonneg (K ω))
    (measurable_from_nat.comp hK).aestronglyMeasurable]
  simp only [ENNReal.ofReal_natCast]
  have hb := ENNReal.toReal_mono (ne_of_lt (ENNReal.div_lt_top
    (show (L : ℝ≥0∞) ≠ ⊤ by simp) (tsub_pos_of_lt hq).ne'))
    (lintegral_natCast_le_geometric_block_tail hK hL htail)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_sub_of_le hq.le (by simp), ENNReal.toReal_one] using hb

end SwingRepair
