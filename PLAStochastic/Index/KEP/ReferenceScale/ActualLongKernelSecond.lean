import PLAStochastic.Index.KEP.ReferenceScale.LongKernelSecond
import PLAStochastic.Index.KEP.ReferenceScale.ReferenceBand

/-!
# The long second-derivative estimate on the actual Exp reference orbit

The constants are independent of the reference layer. The actual continuous
Gamma density, its classical derivatives and its class-uniform killed-band
data are all supplied by proved orbit theorems. This is an endpoint kernel
estimate, before graph summation and the uniform output recurrence.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_second_long_uniform :
    ∃ D vlo vhi eps0 : ℝ, 0 < D ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ w a : ℝ, 1 ≤ w → 1 / 2 ≤ a → a ≤ 2 →
        ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ m k : ℕ, 8 ≤ k → ∀ x y : ℝ,
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        ∃ v : ℝ,
          HasDerivAt (truncatedConvolution 0 w (kepStepSpatialFirst f' σ (σ * a))
            (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j) f σ (σ * a)
              (m + k + 2) x z)) v y ∧
          |v| ≤
            (D / |σ * a|) * kepLongRowVarBudget (kepReferenceLaw eps j) f
              D vlo vhi w σ (σ * a) m k x *
              (((∫ t, |f' t|) / |σ * a|) +
                w * (|kepStepSpatialFirst f' σ (σ * a) y| +
                  |kepStepSpatialFirst f' σ (σ * a) (y - w)|)) +
            ((∫ t, |f'' t|) / |σ * a| ^ 2) * Real.sqrt (D / |σ * a|) *
              kepLongRowRemBudget (kepReferenceLaw eps j) f
                D vlo vhi w σ (σ * a) m k x := by
  obtain ⟨D, θ, vlo, vhi, K, L, e0, hD, -, hvlo, hvhi, -, -, he0, hband⟩ :=
    kepReferenceBand_uniform
  refine ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, ?_⟩
  intro eps he heps j hj w a hw ha ha2 σ hσ m k hk x y
  dsimp only
  have hc := kepReferenceDensity_classical heps hj
  obtain ⟨hforward, hreverse⟩ := hband eps he heps j hj w a hw ha ha2
  have H : KrBand D θ vlo vhi K L (kepReferenceLaw eps j)
      (kepReferenceDensity heps hj).density w w a σ (σ * a) := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using hforward
    · simpa only [neg_one_mul] using hreverse
  exact hasDerivAt_kepFinalConvolutionFirst_long_bound
    (kepReferenceDensity heps hj) (kepReferenceLaw eps j) H
    (continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt)
    (continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt)
    hc.2.2.2.1 hc.2.2.2.2.1 hc.2.2.2.2.2.1 hc.2.1 hc.2.2.1 m k hk x y

end

end PGM
