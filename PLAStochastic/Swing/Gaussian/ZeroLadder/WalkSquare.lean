import PLAStochastic.Swing.Gaussian.ZeroLadder.PieceConvolution
import PLAStochastic.Swing.Restart.MaximalPrefix.ThreePointBlocks
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}
/-- A finite standard Gaussian sum has its exact quadratic moment, for the actual iid path. -/
theorem gaussianZeroWalk_square_integral (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    (∫ ω, (cumulativeSamples X n ω)^2 ∂μ) = (n : ℝ) := by
  let := hi.isProbabilityMeasure
  have hL := gaussian_weighted_sum_hasLaw hX hi hG (Finset.range n) (fun _ => 1)
  have heq : (fun ω => ∑ k ∈ Finset.range n, (1 : ℝ) * X k ω) = cumulativeSamples X n := by
    funext ω
    simp [cumulativeSamples]
  have hL' : HasLaw (cumulativeSamples X n)
      (gaussianReal 0 (Real.toNNReal (∑ k ∈ Finset.range n, (1 : ℝ)^2))) μ := by
    simpa only [heq] using hL
  have hmean : (∫ ω, cumulativeSamples X n ω ∂μ) = 0 := by
    rw [hL'.integral_eq]
    simp
  have hvar := hL'.variance_eq
  have hv : variance (cumulativeSamples X n) μ = (n : NNReal) := by
    simpa [Finset.sum_const, Nat.cast_ofNat] using hvar
  have hcum : Measurable (cumulativeSamples X n) :=
    cumulativeSamples_measurable_prefix (fun j _ => hX j)
  have hsq := variance_of_integral_eq_zero hcum.aemeasurable hmean
  calc
    (∫ ω, (cumulativeSamples X n ω)^2 ∂μ) = variance (cumulativeSamples X n) μ := hsq.symm
    _ = (n : ℝ) := by simpa using hv
end SwingRepair
