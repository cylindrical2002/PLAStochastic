import PLAStochastic.Index.KEP.ReferenceScale.BridgeSecondFluxBudget

/-!
# Actual uniform budgets for all differentiated internal transport pins

All density, derivative and killed-band inputs are discharged on the unchanged
reference orbit. The class constants precede epsilon, layer and bridge length.
The single derivative budget is the square root of the actual input second norm.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_bridge_flux_uniform :
    ∃ C κ eps0 : ℝ, 1 ≤ C ∧ 0 < κ ∧ κ ≤ 1 ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        ∀ w : ℝ, 2 ≤ w →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let p := kepLogStep f σ
        let p' := kepLogStepFirst f' σ
        let q := kepLogStepSlope f f' σ
        let r := κ / (2 * w ^ 2)
        let J := Real.sqrt (1 + kepReferenceSecondNorm eps j)
        ∀ n : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
          kepLogSlopeNorm (fun s => kepFixedBridgeSlope p q w s n x y) ≤
            8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J * Real.exp (-r * (n + 1 : ℕ)) ∧
          kepLogSlopeNorm (fun s => kepBridgeFluxRight p p' w σ s n x y) ≤
            2 * (n : ℝ) * (w + (n + 1 : ℕ)) * C ^ 2 * J *
              Real.exp (-r * (n + 1 : ℕ)) ∧
          kepLogSlopeNorm (fun s => kepBridgeFluxSlope p q w σ s n x y) ≤
            32 * (n : ℝ) * (w + (n + 1 : ℕ)) ^ 3 * C ^ 3 * J *
              Real.exp (-r * (n + 1 : ℕ)) := by
  obtain ⟨C, κ, e0, hC, hκ, hκ1, he0, hbound⟩ :=
    kepReference_bridge_first_full_length_uniform
  refine ⟨C, κ, e0, hC, hκ, hκ1, he0, ?_⟩
  intro eps he heps j hj σ hσ w hw
  dsimp only
  have hb := hbound eps he heps j hj σ hσ w hw
  have hc := kepReferenceDensity_classical heps hj
  have hcf := continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt
  have hcf' := continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt
  have hp := continuous_kepLogStep hcf σ
  have hp' := continuous_kepLogStepFirst hcf' σ
  have hq := continuous_kepLogStepSlope hcf hcf' σ
  have hd := hasDerivAt_kepLogStep_right hc.2.1 σ
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hward := kepLogStepSlope_eq (f := (kepReferenceDensity heps hj).density)
    (f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)) hσ2
  have hJ : 1 ≤ Real.sqrt (1 + kepReferenceSecondNorm eps j) :=
    Real.one_le_sqrt.mpr (by linarith [kepReferenceSecondNorm_nonneg eps j])
  intro n x y hx hy
  exact ⟨kepFixedBridgeSlope_boundary_average hp hp' hd hσ hward
      (by linarith) hC hJ hb.1 hb.2 n hx hy,
    kepBridgeFluxRight_boundary_average hp hp' hσ (by linarith) (by linarith)
      hb.1 hb.2 n hx hy,
    kepBridgeFluxSlope_boundary_average hp hp' hq hd hσ hward
      (by linarith) hC hJ hb.1 hb.2 n hx hy⟩

end

end PGM
