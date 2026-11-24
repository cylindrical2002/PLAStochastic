import PLAStochastic.Swing.Entrance.Grid.Area

/-!
# Almost sure entrance limits under the exact Brownian coupling

Let `B` be a Brownian motion and `X_E = normalizedMeshIncrement B h_E`, `h_E = E^{-2}`, the
exact grid coupling, so that `entrancePath X_E ω = E B(· h_E)`. Almost surely, as `E → ∞`
over `ℝ≥0`:

* the adaptive cut `τ` is eventually finite and `τ / E² → σ` (E6);
* `E a_{τ-1}`, `E b_{τ-1}` and `E β` converge to the pinch slope `m_*` (E6), (E9);
* the refreshed side `s_E` eventually equals the terminal sign `s` (E9);
* the reflected grid area at the cut converges to `I = s ∫_0^σ t (B_t - m_* t) dt` (E20);
* the native first duration satisfies `N / E² → σ`.

All limits are pathwise on one full-measure event that does not depend on `E`.
-/

open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology

namespace SwingRepair

noncomputable section

theorem tendsto_max_one_atTop :
    Tendsto (fun E : ℝ≥0 => ((max E 1 : ℝ≥0) : ℝ)) atTop atTop :=
  NNReal.tendsto_coe_atTop.mpr (tendsto_atTop_mono (fun E => le_max_left E 1) tendsto_id)

/-- The deterministic entrance limits of the rescaled grid path of an entrance-regular path,
along all budgets `E → ∞` in `ℝ≥0`. -/
theorem entranceGridPath_limits {f : C(ℝ, ℝ)} {σ : ℝ≥0} (hr : EntranceRegular f σ) :
    (∀ᶠ E : ℝ≥0 in atTop, entranceCut (entranceGridPath f E) E ≠ ⊤) ∧
    Tendsto (fun E : ℝ≥0 => ((entranceCut (entranceGridPath f E) E).toNat : ℝ) / (E : ℝ) ^ 2)
      atTop (𝓝 (entrancePinch f)) ∧
    Tendsto (fun E : ℝ≥0 => (E : ℝ) * entranceLower (entranceGridPath f E) E
      ((entranceCut (entranceGridPath f E) E).toNat - 1)) atTop (𝓝 (entranceSlope f)) ∧
    Tendsto (fun E : ℝ≥0 => (E : ℝ) * entranceUpper (entranceGridPath f E) E
      ((entranceCut (entranceGridPath f E) E).toNat - 1)) atTop (𝓝 (entranceSlope f)) ∧
    Tendsto (fun E : ℝ≥0 => (E : ℝ) * entranceFrozenSlope (entranceGridPath f E) E
      (entranceCut (entranceGridPath f E) E).toNat) atTop (𝓝 (entranceSlope f)) ∧
    (∀ᶠ E : ℝ≥0 in atTop, entranceSide (entranceGridPath f E) E
      (entranceCut (entranceGridPath f E) E).toNat = entranceSign f) ∧
    Tendsto (fun E : ℝ≥0 => entranceGridArea (entranceGridPath f E) E
      (entranceCut (entranceGridPath f E) E).toNat) atTop (𝓝 (entranceArea f)) ∧
    Tendsto (fun E : ℝ≥0 => (nativeFirstRecording (fun n => (n : ℝ)) (entranceGridPath f E) E : ℝ) /
      (E : ℝ) ^ 2) atTop (𝓝 (entrancePinch f)) := by
  have hE1 : ∀ E : ℝ≥0, 1 ≤ max E 1 := fun E => le_max_right E 1
  have hE := tendsto_max_one_atTop
  have hge : ∀ᶠ E : ℝ≥0 in atTop, max E 1 = E := by
    filter_upwards [eventually_ge_atTop 1] with E hE
    exact max_eq_left hE
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [eventually_cut_le hr hE1 hE, hge] with E hi hm
    obtain ⟨n, hn, _⟩ := hi
    rw [hm] at hn
    rw [hn]
    exact ENat.natCast_ne_top n
  · refine (tendsto_cut_div_sq hr hE1 hE).congr' ?_
    filter_upwards [hge] with E hm
    rw [hm]
  · refine (tendsto_mul_entranceLower_prev hr hE1 hE).congr' ?_
    filter_upwards [hge] with E hm
    rw [hm]
  · refine (tendsto_mul_entranceUpper_prev hr hE1 hE).congr' ?_
    filter_upwards [hge] with E hm
    rw [hm]
  · refine (tendsto_mul_entranceFrozenSlope hr hE1 hE).congr' ?_
    filter_upwards [hge] with E hm
    rw [hm]
  · filter_upwards [eventually_entranceSide_eq hr hE1 hE, hge] with E hs hm
    rw [hm] at hs
    exact hs
  · refine (tendsto_entranceGridArea hr hE1 hE).congr' ?_
    filter_upwards [hge] with E hm
    rw [hm]
  · refine (tendsto_unitRecording_div_sq hr hE1 hE).congr' ?_
    filter_upwards [hge] with E hm
    rw [hm]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The entrance limits (E6), (E9), (E20) under the exact Brownian coupling, almost surely. -/
theorem entrance_coupled_limits_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ,
      (∀ᶠ E : ℝ≥0 in atTop, entranceCut
        (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E ≠ ⊤) ∧
      Tendsto (fun E : ℝ≥0 => ((entranceCut
          (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E).toNat : ℝ) /
        (E : ℝ) ^ 2) atTop (𝓝 (entrancePinch (processPath B ω))) ∧
      Tendsto (fun E : ℝ≥0 => (E : ℝ) * entranceLower
          (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E
          ((entranceCut (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
            E).toNat - 1)) atTop (𝓝 (entranceSlope (processPath B ω))) ∧
      Tendsto (fun E : ℝ≥0 => (E : ℝ) * entranceUpper
          (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E
          ((entranceCut (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
            E).toNat - 1)) atTop (𝓝 (entranceSlope (processPath B ω))) ∧
      Tendsto (fun E : ℝ≥0 => (E : ℝ) * entranceFrozenSlope
          (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E
          (entranceCut (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
            E).toNat) atTop (𝓝 (entranceSlope (processPath B ω))) ∧
      (∀ᶠ E : ℝ≥0 in atTop, entranceSide
          (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E
          (entranceCut (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
            E).toNat = entranceSign (processPath B ω)) ∧
      Tendsto (fun E : ℝ≥0 => entranceGridArea
          (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω) E
          (entranceCut (entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω)
            E).toNat) atTop (𝓝 (entranceArea (processPath B ω))) ∧
      Tendsto (fun E : ℝ≥0 => (nativeFirstDuration
          (normalizedMeshIncrement B (gaussianBudgetMesh E)) E ω : ℝ) / (E : ℝ) ^ 2) atTop
        (𝓝 (entrancePinch (processPath B ω))) := by
  filter_upwards [EntranceRegular.ae_brownian hB] with ω hω
  obtain ⟨hc, hz, σ, hr⟩ := hω
  have hp : ∀ E : ℝ≥0, entrancePath (normalizedMeshIncrement B (gaussianBudgetMesh E)) ω =
      entranceGridPath (processPath B ω) E := fun E => entrancePath_normalizedMesh B E ω hc hz
  have hd : ∀ E : ℝ≥0, nativeFirstDuration (normalizedMeshIncrement B (gaussianBudgetMesh E)) E ω
      = nativeFirstRecording (fun n => (n : ℝ)) (entranceGridPath (processPath B ω) E) E := by
    intro E
    rw [← hp E]
    rfl
  simp only [hp, hd]
  exact entranceGridPath_limits hr

end

end SwingRepair
