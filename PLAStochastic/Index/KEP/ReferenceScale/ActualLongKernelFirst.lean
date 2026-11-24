import PLAStochastic.Index.KEP.ReferenceScale.LongKernelFirst
import PLAStochastic.Index.KEP.ReferenceScale.KernelFirstDecay

/-!
# Actual first-derivative factors in the reference pin graphs

One common band class supplies both the short spectral estimate and the long
regular/remainder estimate. Its constants precede epsilon and the layer. The
regular part of the long factor has no input derivative norm; the product with
a short first derivative therefore avoids an unsuppressed linear second norm.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_first_short_long_uniform :
    ∃ D vlo vhi eps0 : ℝ, 0 < D ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ w a σ : ℝ, 1 ≤ w → 1 / 2 ≤ a → a ≤ 2 →
        (σ = 1 ∨ σ = -1) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        (∀ n : ℕ, ∀ x y : ℝ,
          |truncatedConvolution 0 w (kepStepSpatialFirst f' σ (σ * a))
            (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j) f σ (σ * a) (n + 2) x z) y| ≤
              12 * D * Real.sqrt (1 + kepReferenceSecondNorm eps j) *
                Real.sqrt (krLam D vlo vhi w) ^ n) ∧
        (∀ m k : ℕ, 8 ≤ k → ∀ x y : ℝ,
          |truncatedConvolution 0 w (kepStepSpatialFirst f' σ (σ * a))
            (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j) f σ (σ * a)
              (m + k + 2) x z) y| ≤
                kepLongFirstBudget D vlo vhi w k
                  (3 * Real.sqrt (1 + kepReferenceSecondNorm eps j))) := by
  obtain ⟨D, θ, vlo, vhi, K, L, e0, hD, -, hvlo, hvhi, -, -, he0, hband⟩ :=
    kepReferenceBand_uniform
  refine ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, ?_⟩
  intro eps he heps j hj w a σ hw ha ha2 hσ
  dsimp only
  obtain ⟨hf, hr⟩ := hband eps he heps j hj w a hw ha ha2
  have H : KrBand D θ vlo vhi K L (kepReferenceLaw eps j)
      (kepReferenceDensity heps hj).density w w a σ (σ * a) := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using hf
    · simpa only [neg_one_mul] using hr
  have hc := kepReferenceDensity_classical heps hj
  constructor
  · intro n x y
    apply (krDens_first_spectral_bound (kepReferenceLaw eps j) H hc.2.2.2.2.1 n x y).trans
    have hfirst := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (kepReferenceFirstNorm_le_sqrt heps hj)
        (by positivity : 0 ≤ 4 * D))
      (by positivity : 0 ≤ Real.sqrt (krLam D vlo vhi w) ^ n)
    convert hfirst using 1
    ring
  · intro m k hk x y
    apply (krDens_first_long_uniform_bound (kepReferenceDensity heps hj)
      (kepReferenceLaw eps j) H
      (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
      (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
      hc.2.2.2.1 hc.2.2.2.2.1 hc.2.1 hc.2.2.1 m k hk x y).trans
    unfold kepLongFirstBudget
    apply add_le_add le_rfl
    have hR := kepLongUniformRemainder_nonneg D vlo vhi w k
    have hcoef : 0 ≤ 2 * Real.sqrt (2 * D) * kepLongUniformRemainder D vlo vhi w k := by
      positivity
    convert mul_le_mul_of_nonneg_left (kepReferenceFirstNorm_le_sqrt heps hj) hcoef using 1 <;> ring

end

end PGM
