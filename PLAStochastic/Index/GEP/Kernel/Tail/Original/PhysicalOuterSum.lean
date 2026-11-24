import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputBlocks
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.OuterGreen

/-! # Summing the genuine physical outside rows at every positive slope -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem measurable_kernelPhysicalOuterPairAt (ν : ProbabilityMeasure ℝ) (w s : ℝ)
    (u v : ℕ) : Measurable (fun a => kernelPhysicalOuterPairAt ν w s a u v) := by
  unfold kernelPhysicalOuterPairAt
  apply Measurable.add <;> apply Measurable.mul <;>
    apply measurable_kernelPhysicalSurv_param ν measurableSet_Icc <;> fun_prop

theorem kernel_regLaw_physical_outer_summable (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w s a : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w^2 → 0 < a →
      ∀ β a' : ℝ, (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a) → ∀ y : ℝ,
        Summable (fun n : ℕ => kernelPhysicalSurv (Icc 0 w) ν β a' s n y) := by
  obtain ⟨ρs, Ks, hρs, _, hsmall⟩ :=
    kernel_regLaw_weighted_outer_green_extreme D θ vlo vhi hD hθ hvlo
  obtain ⟨ρl, Kl, hρl, _, hlarge⟩ :=
    kernel_regLaw_weighted_outer_green_large D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ρl (min ρs 1), lt_min hρl (lt_min hρs (by norm_num)), ?_⟩
  intro ν hν w s a hw hs0 hs ha β a' hdir y
  have hw0 : 0 < w := by linarith
  have hs' := (le_div_iff₀ (sq_pos_of_pos hw0)).mp hs
  have hsρ : s ≤ ρs := by
    have hh := (min_le_right ρl (min ρs 1)).trans (min_le_left _ _)
    have hsw := mul_le_mul_of_nonneg_left (show 1 ≤ w ^ 2 by nlinarith) hs0
    nlinarith
  have hsw : s ≤ 1 / w := by
    apply (le_div_iff₀ hw0).mpr
    have hh := (min_le_right ρl (min ρs 1)).trans (min_le_right _ _)
    have hsw := mul_le_mul_of_nonneg_left (show w ≤ w ^ 2 by nlinarith) hs0
    linarith
  have hsl : s ≤ ρl / w ^ 2 := hs.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  by_cases halo : a ≤ 1 / 2
  · simpa only [zero_add] using
      (hsmall ν hν 0 w a hw ha (Or.inl halo) β a' hdir s hs0 hsρ hsw y).1
  · simpa only [zero_add] using
      (hlarge ν hν 0 w a hw (le_of_lt (lt_of_not_ge halo)) β a' hdir s hs0 hsl y).1

/-- The original two-contact physical exterior mass equals the two genuine
Green products, with a class-fixed physical weight chosen before tail exponents. -/
theorem kernel_regLaw_physical_outer_pair_sum (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w s a : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w^2 → 0 < a →
        (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν w s a u v)) =
          ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a) := by
  obtain ⟨ρ, hρ, hb⟩ := kernel_regLaw_physical_outer_summable D θ vlo vhi hD hθ hvlo hv
  refine ⟨ρ, hρ, ?_⟩
  intro ν hν w s a hw hs0 hs ha
  have hP (y : ℝ) := hb ν hν w s a hw hs0 hs ha 1 a (Or.inl ⟨rfl,rfl⟩) y
  have hN (y : ℝ) := hb ν hν w s a hw hs0 hs ha (-1) (-a) (Or.inr ⟨rfl,rfl⟩) y
  unfold kernelPhysicalOuterPairAt kernelPhysicalOuterWeight
  simp_rw [ENNReal.ofReal_add
      (mul_nonneg (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _))
      (mul_nonneg (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _) (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _)),
    ENNReal.ofReal_mul (kernelPhysicalSurv_nonneg _ _ _ _ _ _ _),
    ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _) (hN 0),
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _) (hP 0),
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _) (hN w),
    ← ENNReal.ofReal_tsum_of_nonneg (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _) (hP w),
    ← ENNReal.ofReal_mul (tsum_nonneg (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _)),
    ← ENNReal.ofReal_mul (tsum_nonneg (fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _)),
    ← ENNReal.ofReal_add
      (mul_nonneg (tsum_nonneg fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _)
        (tsum_nonneg fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _))
      (mul_nonneg (tsum_nonneg fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _)
        (tsum_nonneg fun n => kernelPhysicalSurv_nonneg _ _ _ _ _ n _))]

end
end PGM
