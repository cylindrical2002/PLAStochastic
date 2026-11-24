import PLAStochastic.Index.GEP.Kernel.FarSlope.Dirac
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedFixed
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.DiracTail

/-! # Physical-weight Dirac tails on the logarithmic input window -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1400000

/-- On the forced large-slope range the entire actual Dirac time series,
including the two outer Green products, retains exponential width decay. -/
theorem kernel_regLaw_weighted_dirac_far_infinite (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ c K : ℝ, 0 < ρ ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
      ∀ w s x : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → 0 < x → 2 * x ≤ w + 1 →
        Summable (kernelWeightedDiracTailTerm ν f w s x) ∧
        (∑' m, kernelWeightedDiracTailTerm ν f w s x m) ≤ K * w ^ 16 * Real.exp (-c * w) := by
  obtain ⟨c', B, hc', hB, hpin⟩ := kernel_regLaw_dirac_pin_large_slope D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρo, Os, Ol, hρo, hOs, hOl, ho⟩ := kernel_regLaw_physical_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  let c := c' / 2
  have hc : 0 < c := half_pos hc'
  refine ⟨min ρo (c' / 8), c / 2, Ol * B * (3 * (1 + 1 / (c / 2)) ^ 4),
    lt_min hρo (by positivity), by positivity, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe w s x hw hs0 hs hx hax
  have hw0 : 0 < w := by linarith
  let a := (w + 1) / x
  have ha2 : 2 ≤ a := (le_div_iff₀ hx).mpr hax
  have ha : 0 < a := by linarith
  have hso : s ≤ ρo / w ^ 2 := hs.trans (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  have hsc : s ≤ c' / 8 := by
    have hh := (le_div_iff₀ (show 0 < w ^ 2 by positivity)).mp hs
    have hm := min_le_right ρo (c' / 8)
    have hw2 := mul_le_mul_of_nonneg_left (show 1 ≤ w ^ 2 by nlinarith) hs0
    nlinarith
  have houter := ho ν hν w s a hw hs0 hso ha
  rw [if_neg (by linarith : ¬ a ≤ 1 / 2)] at houter
  have hp (m : ℕ) : Real.exp (s * (((m : ℝ) + 1) + 1) / a) * kernelDiracPin ν f w (m + 1) x ≤
      (B * Real.exp (-(c / 2) * w)) * Real.exp (-(c / 2) * ((m : ℝ) + 1)) := by
    by_cases hcross : w ≤ (m : ℝ) + 1
    · have hh0 := hpin ν hν f hf hf0 hfD hfz hfe w x hw hx hax (m + 1) (by omega)
      have hwt := kernel_fixed_time_weight_absorb (show 1 / 2 ≤ a by linarith)
        hs0 hsc (show 1 ≤ (m : ℝ) + 1 by nlinarith [Nat.cast_nonneg (α := ℝ) m]) (X := 0)
      have hh1 := mul_le_mul_of_nonneg_left hh0 (Real.exp_nonneg (s * (((m : ℝ) + 1) + 1) / a))
      have hh : Real.exp (s * (((m : ℝ) + 1) + 1) / a) * kernelDiracPin ν f w (m + 1) x ≤
          B * Real.exp (-c * ((m : ℝ) + 1)) := by
        apply hh1.trans
        simpa only [zero_sub, neg_mul, Nat.cast_add, Nat.cast_one, mul_left_comm] using mul_le_mul_of_nonneg_left hwt hB.le
      have hs := kernel_far_time_width_split hc.le hcross
      exact hh.trans ((mul_le_mul_of_nonneg_left hs hB.le).trans_eq (by ring))
    · unfold kernelDiracPin
      rw [kernel_density_up_zero_shift hν hθ hvlo hfz ha (by omega : 1 ≤ m + 1)
        (by push_cast; linarith), zero_div, mul_zero]
      positivity
  have hnonneg := kernelWeightedDiracTailTerm_nonneg ν hf0 s hw0.le hx.le
  have hsum (N : ℕ) : (∑ m ∈ Finset.range N, kernelWeightedDiracTailTerm ν f w s x m) ≤
      (Ol * B * (3 * (1 + 1 / (c / 2)) ^ 4)) * w ^ 16 * Real.exp (-(c / 2) * w) := by
    have hh : (∑ m ∈ Finset.range N, kernelWeightedDiracTailTerm ν f w s x m) ≤
        (Ol * w ^ 6) * (B * Real.exp (-(c / 2) * w)) * ((2 + w) * (1 + 1 / (c / 2)) ^ 4) := by
      calc
        _ ≤ (Ol * w ^ 6) * (B * Real.exp (-(c / 2) * w)) *
            ∑ m ∈ Finset.range N, ((m : ℝ) + 1 + w) * Real.exp (-(c / 2) * ((m : ℝ) + 1)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro m hm
          have hh := mul_le_mul houter (mul_le_mul_of_nonneg_left (hp m) (show 0 ≤ (m : ℝ) + 1 + w by positivity))
            (mul_nonneg (by positivity) (mul_nonneg (Real.exp_nonneg _) (kernelDiracPin_nonneg ν hf0 w (m + 1) hx.le))) (by positivity)
          exact hh.trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left (kernel_single_exp_sum_le (half_pos hc) hw0.le N) (by positivity)
    have ht : (2 + w) * (1 + 1 / (c / 2)) ^ 4 ≤ 3 * (1 + 1 / (c / 2)) ^ 4 * w := by
      have := mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith) (show 0 ≤ (1 + 1 / (c / 2)) ^ 4 by positivity)
      nlinarith
    have hh' := hh.trans (mul_le_mul_of_nonneg_left ht (by positivity))
    have hw16 : w ^ 7 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
    have hlast := mul_le_mul_of_nonneg_left hw16
      (show 0 ≤ Ol * B * (3 * (1 + 1 / (c / 2)) ^ 4) * Real.exp (-(c / 2) * w) by positivity)
    apply hh'.trans
    convert hlast using 1 <;> ring
  exact ⟨summable_of_sum_range_le hnonneg hsum, Real.tsum_le_of_sum_range_le hnonneg hsum⟩

end
end PGM
