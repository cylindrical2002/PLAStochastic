import PLAStochastic.Swing.FrozenCarry.NegativeCarry.EndpointTail

/-! A coarse large-c branch for the negative-carry mean decomposition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenPrefixLength_negative_mean_large_c
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c E : ℝ} (hc : 1 ≤ c) (hE : 1 ≤ E) :
    (∫ ω, frozenPrefixLengthReal X (-c) E ω ∂μ) ≤ 25*E := by
  have hcp : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hEp : 0 < E := lt_of_lt_of_le zero_lt_one hE
  let m : ℕ := ⌈4*E/c⌉₊
  have hmpos : 0 < m := by
    dsimp [m]
    exact Nat.ceil_pos.mpr (by positivity)
  have hcut : 4*E ≤ c*(m : ℝ) := by
    have hceil : 4*E/c ≤ (⌈4*E/c⌉₊ : ℝ) := Nat.le_ceil _
    have hbase : 4*E ≤ c*(⌈4*E/c⌉₊ : ℝ) := by
      have hh := (div_le_iff₀ hcp).mp hceil
      nlinarith [hh]
    simpa [m] using hbase
  have hh := frozenPrefixLength_negative_mean_head hX hi hG hcp hEp hmpos hcut
  have hsum : (∑ j ∈ Finset.range m,
      μ.real {ω | j < (frozenPrefixLength X (-c) E ω).untopD 0}) ≤ (m : ℝ) := by
    have := hi.isProbabilityMeasure
    calc
      _ ≤ ∑ _j ∈ Finset.range m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact measureReal_le_one (μ := μ)
      _ = (m : ℝ) := by simp
  have hmE : (m : ℝ) ≤ 5*E := by
    dsimp [m]
    have hceil' : (⌈4*E/c⌉₊ : ℝ) < 4*E/c + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one (by positivity : 0 ≤ 4*E/c)
    have hratio : 4*E/c ≤ 4*E := by
      exact (div_le_iff₀ hcp).mpr (by nlinarith [hE])
    nlinarith [le_of_lt hceil', hratio]
  have htail : 2*(1+8/c^2) ≤ 18 := by
    have hc2 : 1 ≤ c^2 := by nlinarith [sq_nonneg (c-1)]
    have hi2 : 8/c^2 ≤ 8 := by
      exact (div_le_iff₀ (sq_pos_of_pos hcp)).mpr (by nlinarith [hc2])
    nlinarith
  calc
    _ ≤ (m : ℝ) + 18 := hh.trans (add_le_add hsum htail)
    _ ≤ 25*E := by nlinarith [hmE, hE]

end SwingRepair
