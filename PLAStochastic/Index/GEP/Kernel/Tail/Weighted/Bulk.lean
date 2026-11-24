import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.OuterGreen
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.PinLength

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1400000

/-- Finite absolute IF budget for one orientation. The other pin's reward is
the majorant `M+w` for either exact linear facet coefficient. -/
def kernelWeightedPairTailSum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (w s a t y z : ℝ)
    (L R M : ℕ) : ℝ :=
  ∑ l ∈ Finset.range L, ∑ r ∈ Finset.range R, ∑ m ∈ Finset.range M,
    (((m : ℝ) + 1 + w) *
      (Real.exp (s * ((l : ℝ) + r + (m + 1) + 1) / a) *
        (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
          krDens (Icc 0 w) ν f 1 a (m + 1) z y)))

theorem kernelWeightedPairTailSum_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (s a t y z : ℝ) (L R M : ℕ) :
    0 ≤ kernelWeightedPairTailSum ν f w s a t y z L R M := by
  apply Finset.sum_nonneg
  intro l hl
  apply Finset.sum_nonneg
  intro r hr
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (by positivity) (mul_nonneg (Real.exp_nonneg _)
    (mul_nonneg (kernelMarkedFullDens_nonneg ν hf0 _ _ _ _ _ _ _) (krDens_nonneg ν hf0 _ _ _)))

theorem measurable_kernelWeightedPairTailSum (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (w s t y z : ℝ) (L R M : ℕ) :
    Measurable (fun a => kernelWeightedPairTailSum ν f w s a t y z L R M) := by
  apply Finset.measurable_sum
  intro l hl
  apply Finset.measurable_sum
  intro r hr
  apply Finset.measurable_sum
  intro m hm
  exact measurable_const.mul
    (((measurable_const.div measurable_id).exp).mul ((measurable_kernelMarkedFullDens_param ν measurableSet_Icc hf measurable_const measurable_id
      measurable_const measurable_const measurable_const l r).mul
      (measurable_krDens_param ν measurableSet_Icc hf measurable_const measurable_id
        measurable_const measurable_const (m + 1))))

/-- A full marked-pair exponential bound immediately controls its genuine
three-index finite absolute IF budget. -/
theorem kernelWeightedPairTailSum_le_of_exp (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    {w s a t y z u C : ℝ} (hw : 0 ≤ w) (hu : 0 < u) (hC : 0 ≤ C)
    (hb : ∀ l r m : ℕ, Real.exp (s * ((l : ℝ) + r + (m + 1) + 1) / a) *
      (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
      krDens (Icc 0 w) ν f 1 a (m + 1) z y) ≤
        C * Real.exp (-u * ((l : ℝ) + r + (m + 1)))) (L R M : ℕ) :
    kernelWeightedPairTailSum ν f w s a t y z L R M ≤ C * ((2 + w) * (1 + 1 / u) ^ 4) := by
  have hh : kernelWeightedPairTailSum ν f w s a t y z L R M ≤ C *
      (∑ l ∈ Finset.range L, ∑ r ∈ Finset.range R, ∑ m ∈ Finset.range M,
        (((m : ℝ) + 1 + w) * Real.exp (-u * ((l : ℝ) + r + (m + 1))))) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro l hl
    apply Finset.sum_le_sum
    intro r hr
    apply Finset.sum_le_sum
    intro m hm
    have hm' := mul_le_mul_of_nonneg_left (hb l r m) (show 0 ≤ (m : ℝ) + 1 + w by positivity)
    exact hm'.trans_eq (by ring)
  exact hh.trans (mul_le_mul_of_nonneg_left (kernel_triple_exp_sum_le hu hw L R M) hC)


/-- Actual physical weights on both outer rows and on the closed pair. The
class fixes `ρ` first; the arbitrary input exponent only affects the further
eventual bound `s ≤ σ`. The width exponent remains the fixed integer 16. -/
theorem kernel_regLaw_weighted_bulk_tail_budget (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : ℝ, 0 < ζ → ∃ σ Ks Kl : ℝ,
      0 < σ ∧ 0 < Ks ∧ 0 < Kl ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → s ≤ σ → 0 ≤ t →
        ∀ y z : ℝ, ∀ L R M : ℕ, ∀ a : ℝ, 0 < a →
          kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z L R M ≤
            if a ≤ 1 / 2 then Ks * w ^ 16 * Real.exp (ζ * t)
            else Kl * w ^ 16 * a⁻¹ ^ 2 := by
  obtain ⟨k, K, hk, hK, hpair⟩ := kernel_regLaw_weighted_pair_polynomial D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρ, Os, Ol, hρ, hOs, hOl, houter⟩ := kernel_regLaw_physical_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ρ (k / 16), lt_min hρ (by positivity), ?_⟩
  intro ζ hζ
  obtain ⟨c, S, hc, hS, hdata⟩ := hpair ζ hζ
  refine ⟨c / 2, Os * S * (3 * (1 + 1 / c) ^ 4),
    Ol * K * (3 * (1 + 4 / k) ^ 4), by positivity, by positivity, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hp⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w s t hw hs0 hs hsσ ht y z L R M a ha
  have hw0 : 0 < w := by linarith
  have hso : s ≤ ρ / w ^ 2 := hs.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  have hsp : s ≤ k / (16 * w ^ 2) := by
    apply hs.trans
    convert div_le_div_of_nonneg_right (min_le_right ρ (k / 16)) (sq_nonneg w) using 1
    ring
  have hbound (l r m : ℕ) :
      Real.exp (s * ((l : ℝ) + r + (m + 1) + 1) / a) *
        (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z * krDens (Icc 0 w) ν f 1 a (m + 1) z y) ≤
        if a ≤ 1 / 2 then S * Real.exp (ζ * t) * Real.exp (-c * ((l : ℝ) + r + (m + 1)))
        else K * w * a⁻¹ ^ 2 * Real.exp (-(k / (4 * w ^ 2)) * ((l : ℝ) + r + (m + 1))) := by
    by_cases hlr : 1 ≤ l + r
    · simpa only [Nat.cast_add, Nat.cast_one] using hp w s a t hw hs0 hsσ hsp ha ht y z l r (m + 1) hlr (by omega)
    · have hl : l = 0 := by omega
      have hr : r = 0 := by omega
      simp only [hl, hr, kernelMarkedFullDens, zero_mul, mul_zero]
      split_ifs <;> positivity
  have ho := houter ν hν w s a hw hs0 hso ha
  by_cases halo : a ≤ 1 / 2
  · rw [if_pos halo] at ho ⊢
    have hb (l r m : ℕ) := hbound l r m
    simp only [if_pos halo] at hb
    have hh := kernelWeightedPairTailSum_le_of_exp ν f hw0.le hc (by positivity) hb L R M
    have ht' : (2 + w) * (1 + 1 / c) ^ 4 ≤ 3 * (1 + 1 / c) ^ 4 * w := by
      have h := mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith) (show 0 ≤ (1 + 1 / c) ^ 4 by positivity)
      exact h.trans_eq (by ring)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left ht' (by positivity))
    have hh'' := mul_le_mul ho hh' (kernelWeightedPairTailSum_nonneg ν hf0 hw0.le s a t y z L R M) (by positivity)
    have hw316 : w ^ 3 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
    have hlast := mul_le_mul_of_nonneg_left hw316
      (show 0 ≤ Os * S * (3 * (1 + 1 / c) ^ 4) * Real.exp (ζ * t) by positivity)
    apply hh''.trans
    convert hlast using 1 <;> ring
  · rw [if_neg halo] at ho ⊢
    have hu : 0 < k / (4 * w ^ 2) := by positivity
    have hb (l r m : ℕ) := hbound l r m
    simp only [if_neg halo] at hb
    have hh := kernelWeightedPairTailSum_le_of_exp ν f hw0.le hu (by positivity) hb L R M
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (kernel_time_sum_polynomial hk hw) (by positivity))
    have hh'' := mul_le_mul ho hh' (kernelWeightedPairTailSum_nonneg ν hf0 hw0.le s a t y z L R M) (by positivity)
    exact hh''.trans_eq (by ring)

end
end PGM
