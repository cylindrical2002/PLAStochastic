import PLAStochastic.Swing.Transient.MarginMoments
import PLAStochastic.Swing.StationaryLimit.MarginKernel.FiniteBudget
import PLAStochastic.Swing.StationaryLimit.MarginKernel.InvariantExistence
import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.IntegralPassage

/-! # The transient reflected-margin laws `ρ_{j,E}`

`app:transientconvergence`: the margin after segment `j` of the actual stream is
`R_{j,E} = E - |X_j|`, with law `ρ_{j,E} = σ_{j,E} ∘ (y ↦ E - |y|)⁻¹`, where
`σ_{j,E}` is the actual state law of `TransientMarginMoments`.  This file records

* the Markov recursion `ρ_{j+1,E} = ρ_{j,E} K_E` through the finite-budget margin
  kernel `K_E = nativeFiniteMarginKernel`, proved for an *arbitrary* input law by
  the reflection symmetry of the restart kernel (this is the intertwining used
  for the invariant law in `FiniteMarginKernel`, now without invariance);
* the uniform moment bounds `∫ |r|^k dρ_{j,E} ≤ transientMarginMomentBound (j-1) k`;
* the mean identity `E N_{j+1}/(E log E) = ∫ g_E/(E log E) dρ_{j,E}`, the
  non-stationary form of `nativeRestart_normalizedMean_eq_margin_integral`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-! ### The intertwining `(Pσ)φ⁻¹ = (σφ⁻¹) K_E` for an arbitrary input law -/

/-- The reflection quotient of the restart kernel intertwines with the finite
margin kernel on every input law: `(P_E σ) ∘ φ⁻¹ = K_E (σ ∘ φ⁻¹)`. -/
theorem nativeRestartKernel_comp_map_finiteMargin [SFinite μ] [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E)
    (σ : Measure ℝ) [SFinite σ] :
    (nativeRestartKernel X μ E ∘ₘ σ).map (finiteMarginMap E) =
      nativeFiniteMarginKernel X μ E ∘ₘ σ.map (finiteMarginMap E) := by
  let P := nativeRestartKernel X μ E
  let φ := finiteMarginMap E
  let K := nativeFiniteMarginKernel X μ E
  have hφ : Measurable φ := measurable_finiteMarginMap E
  have hP : IsMarkovKernel P := nativeRestartKernel_isMarkov hX E
  change (P ∘ₘ σ).map φ = K ∘ₘ σ.map φ
  apply Measure.ext
  intro A hA
  have hpoint : ∀ x : ℝ, K (φ x) A = P x (φ ⁻¹' A) := by
    intro x
    rw [show K = nativeFiniteMarginKernel X μ E from rfl,
      show P = nativeRestartKernel X μ E from rfl,
      nativeFiniteMarginKernel_at_image hX hi hG hE x,
      Measure.map_apply (measurable_finiteMarginMap E) hA]
  have hKmeas : Measurable (fun r : ℝ => K r A) := Kernel.measurable_coe K hA
  rw [Measure.map_apply hφ hA, Measure.bind_apply (hA.preimage hφ) (Kernel.aemeasurable P),
    Measure.bind_apply hA (Kernel.aemeasurable K), lintegral_map hKmeas hφ]
  exact (lintegral_congr fun x => hpoint x).symm

/-! ### The transient margin laws -/

/-- `ρ_{j,E}`: the law of the reflected margin `E - |X_j|` after `j` recorded
segments of the actual stream. -/
def nativeTransientMarginLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (E : ℝ) (j : ℕ) : Measure ℝ :=
  (nativeTransientLaw X μ E j).map (finiteMarginMap E)

theorem nativeTransientMarginLaw_eq_stationaryMarginLaw (E : ℝ) (j : ℕ) :
    nativeTransientMarginLaw X μ E j = stationaryMarginLaw E (nativeTransientLaw X μ E j) := rfl

theorem nativeTransientMarginLaw_isProbability [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E : ℝ) (j : ℕ) :
    IsProbabilityMeasure (nativeTransientMarginLaw X μ E j) := by
  have : IsProbabilityMeasure (nativeTransientLaw X μ E j) :=
    nativeTransientLaw_isProbability hX E j
  exact Measure.isProbabilityMeasure_map (measurable_finiteMarginMap E).aemeasurable

/-- `ρ_{j,E}` as a probability measure. -/
def nativeTransientMarginProb {X : ℕ → Ω → ℝ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E : ℝ) (j : ℕ) : ProbabilityMeasure ℝ :=
  ⟨nativeTransientMarginLaw X μ E j, nativeTransientMarginLaw_isProbability hX E j⟩

@[simp] theorem nativeTransientMarginProb_coe [IsProbabilityMeasure μ]
    (hX : ∀ n, Measurable (X n)) (E : ℝ) (j : ℕ) :
    (nativeTransientMarginProb μ hX E j : Measure ℝ) = nativeTransientMarginLaw X μ E j := rfl

/-- **The Markov recursion** `ρ_{j+1,E} = ρ_{j,E} K_E`. -/
theorem nativeTransientMarginLaw_succ [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (j : ℕ) :
    nativeTransientMarginLaw X μ E (j+1) =
      nativeFiniteMarginKernel X μ E ∘ₘ nativeTransientMarginLaw X μ E j := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have : IsProbabilityMeasure (nativeTransientLaw X μ E j) := nativeTransientLaw_isProbability hX E j
  rw [nativeTransientMarginLaw, nativeTransientLaw_succ hX hi hG hE j,
    nativeRestartKernel_comp_map_finiteMargin hX hi hG hE]
  rfl

/-- `ρ_{j+1,E} = ρ_{1,E} K_E^j`. -/
theorem nativeTransientMarginLaw_eq_iterate [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (j : ℕ) :
    nativeTransientMarginLaw X μ E (j+1) =
      (fun ρ : Measure ℝ => nativeFiniteMarginKernel X μ E ∘ₘ ρ)^[j]
        (nativeTransientMarginLaw X μ E 1) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ← ih]
    exact nativeTransientMarginLaw_succ hX hi hG hE (j+1)

/-! ### Uniform moments of `ρ_{j,E}` -/

/-- `eq:transient-fullmoments` read on the margin laws: for `j ≥ 1` and `k ≥ 1`,
`∫ |r|^k dρ_{j,E} ≤ transientMarginMomentBound (j-1) k`, uniformly in the budget. -/
theorem nativeTransientMarginLaw_abs_pow_le [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Integrable (fun r : ℝ => |r|^k) (nativeTransientMarginLaw X μ E (j+1)) ∧
      (∫ r, |r|^k ∂(nativeTransientMarginLaw X μ E (j+1))) ≤ transientMarginMomentBound j k := by
  obtain ⟨hint, hle⟩ := nativeTransientLaw_margin_pow_le hX hi hG hE j hk
  have hφ : Measurable (finiteMarginMap E) := measurable_finiteMarginMap E
  have hf : AEStronglyMeasurable (fun r : ℝ => |r|^k) (nativeTransientMarginLaw X μ E (j+1)) :=
    (continuous_abs.pow k).aestronglyMeasurable
  have hcomp : (fun r : ℝ => |r|^k) ∘ finiteMarginMap E = fun y : ℝ => |E-abs y|^k := by
    funext y
    rfl
  constructor
  · rw [nativeTransientMarginLaw, integrable_map_measure hf hφ.aemeasurable, hcomp]
    exact hint
  · rw [nativeTransientMarginLaw, integral_map hφ.aemeasurable hf]
    exact hle

/-- The first absolute moment of every `ρ_{j+1,E}` is bounded by
`transientMarginMomentBound j 1`, uniformly in the budget. -/
theorem nativeTransientMarginLaw_abs_le [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (j : ℕ) :
    Integrable (fun r : ℝ => |r|) (nativeTransientMarginLaw X μ E (j+1)) ∧
      (∫ r, |r| ∂(nativeTransientMarginLaw X μ E (j+1))) ≤ transientMarginMomentBound j 1 := by
  have h := nativeTransientMarginLaw_abs_pow_le hX hi hG hE j (k := 1) le_rfl
  simpa only [pow_one] using h

/-- The `ℝ≥0∞` form used by the tightness lemma. -/
theorem nativeTransientMarginLaw_lintegral_abs_le [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ}
    (hE : stationaryScaleThreshold ≤ E) (j : ℕ) :
    (∫⁻ r, ENNReal.ofReal |r| ∂(nativeTransientMarginLaw X μ E (j+1))) ≤
      ENNReal.ofReal (transientMarginMomentBound j 1) := by
  obtain ⟨hint, hle⟩ := nativeTransientMarginLaw_abs_le hX hi hG hE j
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun r => abs_nonneg r)]
  exact ENNReal.ofReal_le_ofReal hle

/-! ### The mean identity -/

/-- `E N_{j+1}/(E log E) = ∫ g_E/(E log E) dρ_{j,E}`: the normalised mean of the
`(j+1)`-st actual segment is the normalised frozen mean averaged over `ρ_{j,E}`. -/
theorem nativeRecordingDurationNat_normalizedMean_eq_margin_integral [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {E : ℝ} (hE : 0 < E) (j : ℕ) :
    (∫ ω, (nativeRecordingDurationNat X E j ω : ℝ) ∂μ) / (E * Real.log E) =
      ∫ r, normalizedFrozenMean X μ E r ∂(nativeTransientMarginLaw X μ E j) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have : IsProbabilityMeasure (nativeTransientLaw X μ E j) := nativeTransientLaw_isProbability hX E j
  rw [nativeRecordingDurationNat_mean_transientLaw hX hi hG hE j,
    nativeTransientMarginLaw_eq_stationaryMarginLaw]
  exact nativeRestart_normalizedMean_eq_margin_integral hX hi hG

end SwingRepair
