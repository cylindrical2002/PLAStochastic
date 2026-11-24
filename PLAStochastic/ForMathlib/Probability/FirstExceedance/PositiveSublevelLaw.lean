import PLAStochastic.ForMathlib.Probability.FirstExceedance.ClosedTailLaw

/-!
# Positive finite sublevels determine an extended probability law

The zero atom is recovered by continuity of measure from above. The infinity
atom is retained; the total mass is fixed by the probability-measure hypothesis.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace BrownianAffine

theorem measure_eq_of_positive_nnreal_sublevels (μ ν : Measure ℝ≥0∞)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ r : ℝ≥0, r ≠ 0 → μ (Iic (r : ℝ≥0∞)) = ν (Iic (r : ℝ≥0∞))) : μ = ν := by
  have hzero : μ (Iic (0 : ℝ≥0∞)) = ν (Iic (0 : ℝ≥0∞)) := by
    let s : ℕ → Set ℝ≥0∞ := fun n => Iic (((n + 1 : ℕ) : ℝ≥0∞)⁻¹)
    have hs : Antitone s := by
      intro i j hij
      apply Iic_subset_Iic.mpr
      exact ENNReal.inv_le_inv.mpr (by exact_mod_cast Nat.add_le_add_right hij 1)
    have hset : Iic (0 : ℝ≥0∞) = ⋂ n, s n := by
      ext x
      simp only [mem_Iic, mem_iInter, s]
      constructor
      · intro hx n
        exact hx.trans bot_le
      · intro hx
        apply ge_of_tendsto
          (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
        exact Eventually.of_forall hx
    have heach (n : ℕ) : μ (s n) = ν (s n) := by
      have hn : ((n + 1 : ℕ) : ℝ≥0) ≠ 0 := by positivity
      have hh := h (((n + 1 : ℕ) : ℝ≥0)⁻¹) (inv_ne_zero hn)
      simpa only [ENNReal.coe_inv hn, ENNReal.coe_natCast, s] using! hh
    rw [hset, hs.measure_iInter (fun _ => measurableSet_Iic.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩,
      hs.measure_iInter (μ := ν) (fun _ => measurableSet_Iic.nullMeasurableSet)
      ⟨0, measure_ne_top _ _⟩]
    exact iInf_congr heach
  apply Measure.ext_of_Iic
  intro a
  by_cases ha : a = ∞
  · simp [ha]
  · lift a to ℝ≥0 using ha
    by_cases ha₀ : a = 0
    · simpa only [ha₀, ENNReal.coe_zero] using hzero
    · exact h a ha₀

theorem identDistrib_of_positive_nnreal_sublevels {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {μ : Measure Ω} {ν : Measure Ξ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X : Ω → ℝ≥0∞} {Y : Ξ → ℝ≥0∞}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (h : ∀ r : ℝ≥0, r ≠ 0 →
      μ {ω | X ω ≤ (r : ℝ≥0∞)} = ν {ω | Y ω ≤ (r : ℝ≥0∞)}) :
    IdentDistrib X Y μ ν := by
  have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX
  have : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY
  refine ⟨hX, hY, measure_eq_of_positive_nnreal_sublevels _ _ ?_⟩
  intro r hr
  rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iic,
    Measure.map_apply_of_aemeasurable hY measurableSet_Iic]
  exact h r hr

end BrownianAffine
