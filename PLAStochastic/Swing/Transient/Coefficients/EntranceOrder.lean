import PLAStochastic.Swing.Transient.Coefficients.PairOrder
import PLAStochastic.Swing.Ladder.ZeroDrift.PairLaw

/-! # The entrance slope law lies above the boundary row

The entrance law is the mixture `ρ = θ Law(-O) + (1 - θ) Law(-(U + O))` of the zero-drift
equilibrium pair `(U, O)`. Its first component is the boundary overshoot law
`𝖡(0) = Law(-O)`, so its slope law is the boundary row `T(0, ·) = 𝖡(0)𝖠`. The second
component lies above it by the pair order (`U ≥ 0`). Mixtures preserve the order, hence

`T(0, ·) ≤ α₂ = ρ𝖠`

against every Lipschitz slope test monotone on `(0, ∞)`, the hypothesis of the parity brackets.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
open LeadingCoefficient KernelLimit SlopeEvaluation

variable {Ω : Type*} [MeasurableSpace Ω] {X : ℕ → Ω → ℝ} {μ : Measure Ω}

/-- The boundary row is the slope law of the zero-drift overshoot margin `-O`. -/
theorem swingSlopeChainKernel_zero_eq [SFinite μ] (hX : ∀ n, Measurable (X n)) :
    swingSlopeChainKernel X μ 0 = slopeStationaryLaw X μ
      ((equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)).map (fun o => -o)) := by
  rw [swingSlopeChainKernel, Kernel.comp_apply, swingOvershootKernel_apply hX, slopeStationaryLaw,
    swingOvershootMeasure]
  simp only [zero_sub]

/-- The slope law of a two-point mixture of margin laws is the mixture of the slope laws. -/
theorem slopeStationaryLaw_mixture (a b : ℝ≥0∞) (ν₁ ν₂ : Measure ℝ) :
    slopeStationaryLaw X μ (a • ν₁ + b • ν₂) =
      a • slopeStationaryLaw X μ ν₁ + b • slopeStationaryLaw X μ ν₂ := by
  simp only [slopeStationaryLaw, Measure.comp_add, Measure.comp_smul]

/-- **Entrance order from the equilibrium pair.**  Let `π` be a pair law with `U ≥ 0`,
integrable coordinates, second marginal `Law(O)` the zero-drift equilibrium overshoot law and
`Law(U + O)` the size-biased ladder-height law. Then `T(0, ·) ≤ ρ𝖠`. -/
theorem slopeTestLE_zero_entranceLaw_of_pair [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {π : Measure (ℝ × ℝ)} [IsProbabilityMeasure π] (hπ : ∀ᵐ p ∂π, 0 ≤ p.1)
    (h₁ : Integrable (fun p : ℝ × ℝ => p.1) π) (h₂ : Integrable (fun p : ℝ × ℝ => p.2) π)
    (hsnd : π.map Prod.snd = equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0))
    (hsum : π.map (fun p => p.1 + p.2) = sizeBiasedLaw (gaussianAscendingLadderLaw X μ 0))
    (hθ0 : 0 ≤ entranceSelectionProb) (hθ1 : entranceSelectionProb ≤ 1) :
    SlopeTestLE (swingSlopeChainKernel X μ 0) (slopeStationaryLaw X μ (entranceLaw X μ)) := by
  have hprob : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  set ν₁ : Measure ℝ := π.map fun p => -p.2 with hν₁
  set ν₂ : Measure ℝ := π.map fun p => -(p.1 + p.2) with hν₂
  have hm₁ : Measurable fun p : ℝ × ℝ => -p.2 := measurable_snd.neg
  have hm₂ : Measurable fun p : ℝ × ℝ => -(p.1 + p.2) := (measurable_fst.add measurable_snd).neg
  have e₁ : (equilibriumOvershootLaw (gaussianAscendingLadderLaw X μ 0)).map (fun o => -o) = ν₁ := by
    rw [← hsnd]
    exact Measure.map_map (μ := π) (by fun_prop : Measurable fun o : ℝ => -o) measurable_snd
  have e₂ : (sizeBiasedLaw (gaussianAscendingLadderLaw X μ 0)).map (fun h => -h) = ν₂ := by
    rw [← hsum]
    exact Measure.map_map (μ := π) (by fun_prop : Measurable fun h : ℝ => -h)
      (by fun_prop : Measurable fun p : ℝ × ℝ => p.1 + p.2)
  have hθ' : ENNReal.ofReal (1 - entranceSelectionProb) =
      1 - ENNReal.ofReal entranceSelectionProb := by
    rw [ENNReal.ofReal_sub _ hθ0, ENNReal.ofReal_one]
  have hθle : ENNReal.ofReal entranceSelectionProb ≤ 1 := ENNReal.ofReal_le_one.mpr hθ1
  have hρ : entranceLaw X μ = ENNReal.ofReal entranceSelectionProb • ν₁ +
      (1 - ENNReal.ofReal entranceSelectionProb) • ν₂ := by
    rw [entranceLaw, e₁, e₂, hθ']
  have : IsProbabilityMeasure ν₁ := Measure.isProbabilityMeasure_map hm₁.aemeasurable
  have : IsProbabilityMeasure ν₂ := Measure.isProbabilityMeasure_map hm₂.aemeasurable
  have ha₁ := integrable_abs_map_pair hm₁ h₂.neg
  have ha₂ := integrable_abs_map_pair hm₂ (h₁.add h₂).neg
  have : IsProbabilityMeasure (slopeStationaryLaw X μ ν₁) := slopeStationaryLaw_isProbability hX _
  have : IsProbabilityMeasure (slopeStationaryLaw X μ ν₂) := slopeStationaryLaw_isProbability hX _
  have hS : ∀ ν : Measure ℝ, slopeStationaryLaw X μ ν (Ioi 0)ᶜ = 0 := fun ν => by
    rw [compl_Ioi]; exact slopeStationaryLaw_Iic_zero hX hi hG ν
  rw [hρ, slopeStationaryLaw_mixture, swingSlopeChainKernel_zero_eq hX, e₁]
  exact slopeTestLE_mixture (hS ν₁) (slopeStationaryLaw_first_moment_integrable hX hi hG ha₁)
    (hS ν₂) (slopeStationaryLaw_first_moment_integrable hX hi hG ha₂) hθle
    (SlopeTestLE.refl _) (slopeTestLE_slopeStationaryLaw_pair hX hi hG hπ h₁ h₂)

/-- **The entrance slope law lies above the boundary row**: `T(0, ·) ≤ α₂ = ρ𝖠` against every
Lipschitz slope test monotone on `(0, ∞)`. -/
theorem slopeTestLE_zero_entranceLaw [SFinite μ]
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    SlopeTestLE (swingSlopeChainKernel X μ 0) (slopeStationaryLaw X μ (entranceLaw X μ)) := by
  set ν₀ := gaussianAscendingLadderLaw X μ 0 with hν₀
  have := gaussianZeroLadder_pair_isProbabilityMeasure hX hi hG
  have : IsProbabilityMeasure ν₀ := gaussianAscendingLadderLaw_isProbabilityMeasure hX hi 0
  have hmean := ladderMeanENN_gaussianAscendingLadderLaw_zero_pos hX hi hG
  have hfst : (equilibriumPairLaw ν₀).map Prod.fst = equilibriumOvershootLaw ν₀ :=
    equilibriumPairLaw_map_fst ν₀ (gaussianAscendingLadderLaw_nonneg_ae hX 0) hmean.1.ne'
      hmean.2.ne
  have hsnd := gaussianZeroLadder_pair_map_snd hX hi hG
  have hO := equilibriumOvershootLaw_zero_integrable_id hX hi hG
  have hOnn : ∀ᵐ o ∂equilibriumOvershootLaw ν₀, 0 ≤ o := by
    rw [ae_iff]
    convert equilibriumOvershootLaw_Iio_zero ν₀ using 2
    ext o
    simp [not_le]
  have h₁ : Integrable (fun p : ℝ × ℝ => p.1) (equilibriumPairLaw ν₀) := by
    rw [← hfst] at hO
    exact (integrable_map_measure aestronglyMeasurable_id measurable_fst.aemeasurable).mp hO
  have h₂ : Integrable (fun p : ℝ × ℝ => p.2) (equilibriumPairLaw ν₀) := by
    rw [← hsnd] at hO
    exact (integrable_map_measure aestronglyMeasurable_id measurable_snd.aemeasurable).mp hO
  have hπ : ∀ᵐ p ∂equilibriumPairLaw ν₀, 0 ≤ p.1 := by
    rw [← hfst] at hOnn
    exact ae_of_ae_map measurable_fst.aemeasurable hOnn
  exact slopeTestLE_zero_entranceLaw_of_pair hX hi hG hπ h₁ h₂ hsnd
    (gaussianZeroLadder_pair_map_add X μ) entranceSelectionProb_nonneg entranceSelectionProb_le_one

end SwingRepair
