import PLAStochastic.Swing.Gaussian.ZeroLadder.WaldIdentity
import PLAStochastic.Swing.Gaussian.ZeroLadder.EpochLimits
import PLAStochastic.ForMathlib.Probability.RandomWalk.Fluctuation.SymmetricLadderMeanCesaro
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
/-- The actual Gaussian ladder mean is forced by the finite path decomposition: V(0)=1/sqrt 2. -/
theorem gaussianRenewalPotential_zero_value
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    gaussianRenewalPotential X μ 0 = 1 / Real.sqrt 2 := by
  let q : ℕ → ℝ := gaussianLadderSurvivalProbability X μ
  let e : ℕ → ℝ := gaussianLadderSurvivingFirstMoment X μ
  let d : ℕ → ℝ := gaussianLadderExitedSecondMoment X μ
  let a : ℕ → ℝ := gaussianLadderSurvivingSecondMoment X μ
  have hq0 : ∀ n, (∑ k ∈ Finset.range (n+1), q k*q (n-k)) = 1 := by
    intro n
    exact gaussian_ladder_survival_convolution hX hi hG n
  have ha : ∀ k, a k = (∑ j ∈ Finset.range k, q j)-d k := by
    intro k
    exact gaussianLadderSurvivingSecondMoment_eq hX hi hG k
  have hid0 : ∀ n : ℕ, (n : ℝ) =
      2 * (∑ k ∈ Finset.range (n+1), a k*q (n-k)) -
      2 * (∑ k ∈ Finset.range (n+1), e k*e (n-k)) := by
    intro n
    simpa [a, e, q] using gaussian_ladder_square_wald_identity hX hi hG n
  have hid : ∀ n : ℕ, 2*((∑ k ∈ Finset.range (n+1), e k*e (n-k)) +
      (∑ k ∈ Finset.range (n+1), d k*q (n-k))) = (n : ℝ) := by
    intro n
    have hh := ladder_convolution_identity_of_wald hq0 ha hid0
    simpa [a, e, q, d] using hh n
  have heM : ∀ n, |e n| ≤ gaussianExcessExpMomentBound 2 := by
    intro n
    exact gaussianLadderSurvivingFirstMoment_abs_le hX hi hG n
  have he : Tendsto e atTop (𝓝 (gaussianRenewalPotential X μ 0)) := by
    simpa [e] using gaussianLadderSurvivingFirstMoment_tendsto hX hi hG
  have hdC : ∀ n, |d n| ≤ gaussianExcessExpMomentBound 2 := by
    intro n
    exact gaussianLadderExitedSecondMoment_abs_le hX hi hG n
  have hq : Tendsto q atTop (𝓝 0) := by
    simpa [q] using gaussianLadderSurvivalProbability_tendsto_zero hX hi hG
  have he' : Tendsto e atTop (𝓝 (∫ u : ℝ, u ∂gaussianZeroLadderLaw X μ)) := by
    rw [← gaussianRenewalPotential_zero_eq_ladder_mean hX]
    exact he
  have hm : 0 ≤ (∫ u : ℝ, u ∂gaussianZeroLadderLaw X μ) := by
    apply integral_nonneg_of_ae
    filter_upwards [gaussianZeroLadderLaw_positive_ae hX hi hG] with u hu
    exact hu.le
  rw [gaussianRenewalPotential_zero_eq_ladder_mean hX]
  exact ladder_mean_eq_inv_sqrt_two_of_convolution_identity heM he' hdC hq hid hm
end SwingRepair
