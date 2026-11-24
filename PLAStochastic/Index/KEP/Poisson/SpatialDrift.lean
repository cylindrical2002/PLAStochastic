import PLAStochastic.Index.KEP.Poisson.ParentState

/-!
# The paid spatial coefficient of the original parent state kernel

The intensity-profile constant is separated from the two-thirds ratio of
the actual reference span to the Poisson intensity parameter. The remaining
state factor is exactly the observed cumulative physical gap.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory

theorem kepPoisson_parent_step_spatial_drift {f : ℝ → ℝ} {flo fhi L : ℝ}
    (hf : KepIntensityProfile f flo fhi L) :
    ∃ B E : ℝ, 0 ≤ B ∧ kepReferenceClassicalThreshold ≤ E ∧
      ∀ eps, E ≤ eps → ∀ n, 0 < n → ∀ j, 0 ≤ kepReferenceSpan eps j →
        ∀ r, (∀ y, measureHellinger (kepPoissonLayerMeasure hf eps n y j) (kepReferenceLaw eps j) ≤ r) →
          ∀ x S, measureHellinger (kepPoissonParentStepKernel hf eps n x j S) (kepReferenceLaw eps j) ≤
            r + (B * eps ^ 98 * (kepReferenceSpan eps j / n) ^ (2 / 3 : ℝ)) * |S| ^ (2 / 3 : ℝ) := by
  obtain ⟨K, E, hK, hE, hs⟩ := kepPoisson_parent_step_comparison hf
  have hA : 0 ≤ L / flo ^ 2 := div_nonneg hf.lip_nonneg (sq_nonneg flo)
  refine ⟨K * (L / flo ^ 2) ^ (2 / 3 : ℝ), E,
    mul_nonneg hK.le (Real.rpow_nonneg hA _), hE, ?_⟩
  intro eps he n hn j hm r hchild x S
  have h := hs eps he n hn j hm r hchild x S
  have hr : 0 ≤ kepReferenceSpan eps j / n := div_nonneg hm hn.le
  rw [Real.mul_rpow (mul_nonneg hA hr) (abs_nonneg S), Real.mul_rpow hA hr] at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end

end PGM
