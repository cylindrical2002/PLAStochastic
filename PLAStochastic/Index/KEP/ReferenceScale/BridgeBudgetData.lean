import PLAStochastic.Index.KEP.ReferenceScale.BridgeSecondAverage

/-!
# The proved common class data for all actual bridge coefficients

This bundles the one-step identities and the pointwise/first integral bounds
with the same constants and killed rate. All higher pin bounds are derived
from these data. The actual orbit supplies the data unconditionally.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

structure KepKilledBridgeBudget (σ : ℝ) (p p' q : ℝ → ℝ → ℝ) (w C J r : ℝ) : Prop where
  orientation : σ = 1 ∨ σ = -1
  width_nonneg : 0 ≤ w
  constant_ge_one : 1 ≤ C
  first_ge_one : 1 ≤ J
  continuous_step : Continuous (Function.uncurry p)
  continuous_spatial : Continuous (Function.uncurry p')
  continuous_slope : Continuous (Function.uncurry q)
  spatial_derivative : ∀ s t, HasDerivAt (p s) (p' s t) t
  ward : ∀ s t, q s t = -p s t + (σ - t) * p' s t
  pointwise : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), ∀ n : ℕ,
    ∀ x ∈ Icc (0 : ℝ) w, ∀ y ∈ Icc (0 : ℝ) w,
    |kepFixedBridge p w s n x y| ≤ C * Real.exp (-r * (n + 1 : ℕ))
  first : ∀ n : ℕ, ∀ x y : ℝ, (x = 0 ∨ x = w) → (y = 0 ∨ y = w) →
    kepLogSlopeNorm (fun s => kepFixedBridgeRight p p' w s n x y) ≤
      C * J * Real.exp (-r * (n + 1 : ℕ))

namespace KepKilledBridgeBudget

variable {σ w C J r : ℝ} {p p' p'' q : ℝ → ℝ → ℝ}

theorem slope (H : KepKilledBridgeBudget σ p p' q w C J r)
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepFixedBridgeSlope p q w s n x y) ≤
      8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J * Real.exp (-r * (n + 1 : ℕ)) :=
  kepFixedBridgeSlope_boundary_average H.continuous_step H.continuous_spatial
    H.spatial_derivative H.orientation H.ward H.width_nonneg H.constant_ge_one
    H.first_ge_one H.pointwise H.first n hx hy

theorem fluxRight (H : KepKilledBridgeBudget σ p p' q w C J r)
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepBridgeFluxRight p p' w σ s n x y) ≤
      2 * (n : ℝ) * (w + (n + 1 : ℕ)) * C ^ 2 * J * Real.exp (-r * (n + 1 : ℕ)) :=
  kepBridgeFluxRight_boundary_average H.continuous_step H.continuous_spatial
    H.orientation H.width_nonneg (by have := H.constant_ge_one; linarith)
    H.pointwise H.first n hx hy

theorem fluxSlope (H : KepKilledBridgeBudget σ p p' q w C J r)
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepBridgeFluxSlope p q w σ s n x y) ≤
      32 * (n : ℝ) * (w + (n + 1 : ℕ)) ^ 3 * C ^ 3 * J * Real.exp (-r * (n + 1 : ℕ)) :=
  kepBridgeFluxSlope_boundary_average H.continuous_step H.continuous_spatial
    H.continuous_slope H.spatial_derivative H.orientation H.ward H.width_nonneg
    H.constant_ge_one H.first_ge_one H.pointwise H.first n hx hy

theorem second (H : KepKilledBridgeBudget σ p p' q w C J r)
    (hp'' : Continuous (Function.uncurry p''))
    (n : ℕ) {x y : ℝ} (hx : x = 0 ∨ x = w) (hy : y = 0 ∨ y = w) :
    kepLogSlopeNorm (fun s => kepFixedBridgeSlopeSecondWard p p' p'' q w σ s n x y) ≤
      (w + (n + 1 : ℕ)) ^ 2 * kepLogSlopeNorm (fun s => kepFixedBridgeRight p p'' w s n x y) +
        kepBridgeSecondRemainderBudget C J w n * Real.exp (-r * (n + 1 : ℕ)) :=
  kepFixedBridgeSlopeSecondWard_boundary_average H.continuous_step H.continuous_spatial
    hp'' H.continuous_slope H.orientation H.width_nonneg
    (by have := H.constant_ge_one; linarith) (by have := H.first_ge_one; linarith)
    H.pointwise H.first (fun m u v hu hv => H.fluxRight m hu hv)
    (fun m u v hu hv => H.fluxSlope m hu hv) n hx hy

end KepKilledBridgeBudget

theorem kepReference_killed_bridge_budget_uniform :
    ∃ C κ eps0 : ℝ, 1 ≤ C ∧ 0 < κ ∧ κ ≤ 1 ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ w : ℝ, 2 ≤ w →
          let f := (kepReferenceDensity heps hj).density
          let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
          KepKilledBridgeBudget σ (kepLogStep f σ) (kepLogStepFirst f' σ) (kepLogStepSlope f f' σ)
            w C (Real.sqrt (1 + kepReferenceSecondNorm eps j)) (κ / (2 * w ^ 2)) := by
  obtain ⟨C, κ, e0, hC, hκ, hκ1, he0, hbound⟩ := kepReference_bridge_first_full_length_uniform
  refine ⟨C, κ, e0, hC, hκ, hκ1, he0, ?_⟩
  intro eps he heps j hj σ hσ w hw
  have hb := hbound eps he heps j hj σ hσ w hw
  have hc := kepReferenceDensity_classical heps hj
  have hf := continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt
  have hf' := continuous_iff_continuousAt.mpr fun t => (hc.2.2.1 t).continuousAt
  have hσ2 : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  exact ⟨hσ, by linarith, hC,
    Real.one_le_sqrt.mpr (by linarith [kepReferenceSecondNorm_nonneg eps j]),
    continuous_kepLogStep hf σ, continuous_kepLogStepFirst hf' σ,
    continuous_kepLogStepSlope hf hf' σ, hasDerivAt_kepLogStep_right hc.2.1 σ,
    kepLogStepSlope_eq hσ2, hb.1, hb.2⟩

end

end PGM
