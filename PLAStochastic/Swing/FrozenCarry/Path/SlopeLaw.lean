import PLAStochastic.Swing.FrozenCarry.Path.SlopeEnvelope
import PLAStochastic.Swing.Gaussian.HalfLine.PrefixStability

/-! # The actual frozen slope magnitude under the original Gaussian probability law -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The original strong law yields the carried upper-slope limit with the exact n+1 denominator. -/
theorem frozenUpperSlope_tendsto_zero_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0) := by
  filter_upwards [gaussianDriftWalk_strongLaw hX hi hG w 0] with ω hω
  have hn : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using! (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun n : ℕ => (n : ℝ)/((n : ℝ)+1)) atTop (𝓝 1) := by
    have hh : Tendsto (fun n : ℕ => 1-1/((n : ℝ)+1)) atTop (𝓝 ((1 : ℝ)-0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hn)
    simp only [sub_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun n => by dsimp only; field_simp; ring)
  have hh := hω.mul hr
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  dsimp [frozenUpperSlope, gaussianDriftWalk]
  field_simp
  ring

/-- Downward crossing is proved for the actual walk, including every fixed negative initial state. -/
theorem frozen_negative_observation_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) :
    ∀ᵐ ω ∂μ, ∃ n : ℕ, w+cumulativeSamples X n ω < 0 := by
  by_cases hw : 0 ≤ w
  · filter_upwards [gaussianHalfLineExit_zero_finite_ae hX hi hG hw] with ω hω
    have hp := gaussianHalfLineExitPosition_neg hω
    refine ⟨(gaussianHalfLineExit X w 0 ω).untopD 0, ?_⟩
    simpa only [gaussianHalfLineExitPosition, gaussianDriftWalk, zero_mul, add_zero] using hp
  · exact Eventually.of_forall (fun _ => ⟨0, by simpa only [cumulativeSamples_zero, add_zero] using lt_of_not_ge hw⟩)

/-- Both actual hypotheses for the deterministic frozen-state limit hold on one full-measure set. -/
theorem frozenSlopeMagnitude_positive_ae
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (w : ℝ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => frozenUpperSlope X w n ω) atTop (𝓝 0) ∧
      0 < frozenSlopeMagnitude X w ω := by
  filter_upwards [frozenUpperSlope_tendsto_zero_ae hX hi hG w,
    frozen_negative_observation_ae hX hi hG w] with ω hv hn
  exact ⟨hv, frozenSlopeMagnitude_pos_of_negative hv hn⟩

end SwingRepair
