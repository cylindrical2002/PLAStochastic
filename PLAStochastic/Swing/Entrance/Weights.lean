import PLAStochastic.Swing.Entrance.Grid.Coupling
import PLAStochastic.Swing.Entrance.Grid.Measurability
import PLAStochastic.Swing.Entrance.Brownian.AreaNonzero
import PLAStochastic.Swing.Entrance.SignWeights

/-! # The selection weights of the entrance law

The reflected grid area at the adaptive cut, `I_E^- = E^{-5} ∑_{i ≤ τ} i (s y_i - s β i)`, is a
measurable function of the increment sequence. Under the exact Brownian coupling it converges
almost surely to the Brownian selection area `I` (E20), which vanishes with probability zero
(E25). Hence, for thresholds `c_E → 0`,

`P(I_E^- > c_E) → θ = P(I > 0)`,  `P(I_E^- < -c_E) → 1 - θ`,

and, since these are probabilities of events of the increment sequence, the same limits hold for
every iid standard Gaussian sequence on any probability space.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology
namespace SwingRepair

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The reflected grid area at the adaptive cut, as a function of the increment sequence. -/
def entranceCutArea (E : ℝ) (x : ℕ → ℝ) : ℝ :=
  entranceGridArea (entrancePath nativeIncrementCoordinates x) E
    (entranceCut (entrancePath nativeIncrementCoordinates x) E).toNat

theorem measurable_entranceCutArea (E : ℝ) : Measurable (entranceCutArea E) := by
  have hY : ∀ n, Measurable fun x : ℕ → ℝ => entrancePath nativeIncrementCoordinates x n :=
    fun n => by
      unfold entrancePath cumulativeSamples
      exact Finset.measurable_sum _ fun k _ => nativeIncrementCoordinates_measurable k
  refine measurable_at_entranceCut hY E
    (g := fun n x => entranceGridArea (entrancePath nativeIncrementCoordinates x) E n) fun n => ?_
  have hside : Measurable fun x : ℕ → ℝ =>
      entranceSide (entrancePath nativeIncrementCoordinates x) E n :=
    Measurable.ite (measurableSet_entranceRefreshesLower hY E n) measurable_const measurable_const
  have hfrozen := measurable_entranceFrozenSlope hY E n
  unfold entranceGridArea
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => measurable_const.mul ?_)
  exact (hside.mul (hY i)).sub ((hside.mul hfrozen).mul measurable_const)

/-- **Selection weights on the Brownian coupling.** -/
theorem tendsto_entranceCutArea_sign_brownian {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B μ) {c : ℝ≥0 → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun E : ℝ≥0 => μ.real {ω | c E < entranceCutArea E
        (fun k => normalizedMeshIncrement B (gaussianBudgetMesh E) k ω)}) atTop
        (𝓝 entranceSelectionProb) ∧
      Tendsto (fun E : ℝ≥0 => μ.real {ω | entranceCutArea E
        (fun k => normalizedMeshIncrement B (gaussianBudgetMesh E) k ω) < -c E}) atTop
        (𝓝 (1 - entranceSelectionProb)) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  set I : Ω → ℝ := fun ω => entranceArea (processPath B ω)
  set J : ℝ≥0 → Ω → ℝ := fun E ω =>
    entranceCutArea E (fun k => normalizedMeshIncrement B (gaussianBudgetMesh E) k ω)
  have hJ : ∀ E, AEMeasurable (J E) μ := by
    intro E
    by_cases hE : gaussianBudgetMesh E = 0
    · simp only [J, hE]
      refine (measurable_entranceCutArea _).comp_aemeasurable (aemeasurable_pi_lambda _ ?_)
      intro k
      simp only [normalizedMeshIncrement, NNReal.coe_zero, Real.sqrt_zero, div_zero]
      exact aemeasurable_const
    · exact (measurable_entranceCutArea _).comp_aemeasurable (aemeasurable_pi_lambda _ fun k =>
        (normalizedMeshIncrement_hasLaw hB.toIsPreBrownianReal _ hE k).aemeasurable)
  have hconv : ∀ᵐ ω ∂μ, Tendsto (fun E => J E ω) atTop (𝓝 (I ω)) := by
    filter_upwards [entrance_coupled_limits_ae hB] with ω hω
    exact hω.2.2.2.2.2.2.1
  have h0 : μ {ω | I ω = 0} = 0 := by
    have := entranceArea_ne_zero_ae hB
    rw [ae_iff] at this
    simpa only [ne_eq, not_not] using this
  obtain ⟨hpos, hneg⟩ :=
    tendsto_measure_sign_of_ae (aemeasurable_entranceArea hB) hJ hc hconv h0
  refine ⟨?_, ?_⟩
  · rw [← measureReal_entranceArea_pos hB, measureReal_def]
    exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hpos
  · rw [← measureReal_entranceArea_neg hB, measureReal_def]
    exact (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hneg

/-- **Selection weights.**  For every iid standard Gaussian sequence and thresholds `c_E → 0`,
`P(I_E^- > c_E) → θ` and `P(I_E^- < -c_E) → 1 - θ`, where `I_E^-` is the reflected grid area at
the adaptive cut. -/
theorem tendsto_entranceCutArea_sign {X : ℕ → Ω → ℝ} {μ : Measure Ω}
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {c : ℝ≥0 → ℝ} (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto (fun E : ℝ≥0 => μ.real {ω | c E < entranceCutArea E (fun k => X k ω)}) atTop
        (𝓝 entranceSelectionProb) ∧
      Tendsto (fun E : ℝ≥0 => μ.real {ω | entranceCutArea E (fun k => X k ω) < -c E}) atTop
        (𝓝 (1 - entranceSelectionProb)) := by
  obtain ⟨hpos, hneg⟩ := tendsto_entranceCutArea_sign_brownian isBrownianReal_canonicalBrownian hc
  have hid : ∀ E : ℝ≥0, 1 ≤ E → IdentDistrib (fun ω (k : ℕ) => X k ω)
      (fun ω (k : ℕ) => normalizedMeshIncrement canonicalBrownian (gaussianBudgetMesh E) k ω)
      μ canonicalPreBrownianMeasure := fun E hE =>
    identDistrib_gaussian_mesh_sequence (fun n => (hX n).aemeasurable) hi hG
      isBrownianReal_canonicalBrownian.toIsPreBrownianReal _ (gaussianBudgetMesh_ne_zero hE)
  refine ⟨hpos.congr' ?_, hneg.congr' ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with E hE
    have := (hid E hE).measure_mem_eq (measurableSet_lt measurable_const
      (measurable_entranceCutArea (E : ℝ)) : MeasurableSet {x : ℕ → ℝ | c E < entranceCutArea E x})
    simp only [measureReal_def]
    exact congrArg ENNReal.toReal this.symm
  · filter_upwards [eventually_ge_atTop 1] with E hE
    have := (hid E hE).measure_mem_eq (measurableSet_lt (measurable_entranceCutArea (E : ℝ))
      measurable_const : MeasurableSet {x : ℕ → ℝ | entranceCutArea E x < -c E})
    simp only [measureReal_def]
    exact congrArg ENNReal.toReal this.symm

end SwingRepair
