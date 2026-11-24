import PLAStochastic.Swing.FrozenCarry.Interior.UniformCoefficient
import PLAStochastic.ForMathlib.NumberTheory.Harmonic.ScaledRangeSum

/-! # The interior range contributes the logarithmic factor

Applying the range-sum estimate to the uniform interior tail coefficient turns
the sum of survival probabilities over the interior indices into
`4V(w) * E * log(b/a)` with an error controlled by `E` times the uniformity
parameter and an absolute constant. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozen_interior_range_sum
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {δ : ℝ} (hδ : 0 < δ) {K : Set ℝ} (hK : IsCompact K) (hK0 : K ⊆ Ici 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ E : ℝ in atTop, ∀ w ∈ K, ∀ a b : ℕ, 1 ≤ a → a ≤ b →
      (∀ n ∈ Finset.Ico a b, frozenInteriorWindow δ E n) →
      |(∑ n ∈ Finset.Ico a b,
          μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω})-
        4*gaussianRenewalPotential X μ w*E*(Real.log b-Real.log a)| ≤
      E*(ε*(|Real.log b-Real.log a|+1)+|4*gaussianRenewalPotential X μ w|) := by
  filter_upwards [frozenScaledTail_interior_uniform hX hi hG hδ hK hK0 hε,
    eventually_gt_atTop (0 : ℝ)] with E hEu hEpos
  intro w hw a b ha hab hwin
  refine sum_of_scaled_range hEpos hε.le ha hab (fun n hn => ?_)
  exact (hEu n (hwin n hn) w hw).le

end SwingRepair
