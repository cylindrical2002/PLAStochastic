import PLAStochastic.Swing.Gaussian.HalfLine.SmallDriftOvershootMean
import Mathlib.Probability.Independence.InfinitePi

/-! # The actual strict ladder law at zero

This module identifies the actual first strict descending overshoot with a
probability law independent of the realization of the Gaussian increments.
Reflection gives the same ascending ladder law. The zero-state renewal
potential is its first moment; no value for that moment is postulated here. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The probability law of the actual first strict descending ladder height. -/
def gaussianZeroLadderLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) : Measure ℝ :=
  μ.map (gaussianHalfLineOvershoot X 0 0)

theorem gaussianZeroLadderLaw_isProbabilityMeasure (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) : IsProbabilityMeasure (gaussianZeroLadderLaw X μ) := by
  let := hi.isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map (gaussianHalfLineOvershoot_measurable hX 0 0).aemeasurable

omit [MeasurableSpace Ω] in
theorem gaussianHalfLineExit_zero_pos (ω : Ω) :
    (0 : WithTop ℕ) < gaussianHalfLineExit X 0 0 ω := by
  apply (lt_gaussianHalfLineExit_iff X 0 0 0 ω).mpr
  intro j hj
  have hj0 : j = 0 := by omega
  simp [hj0, gaussianDriftWalk]

/-- The strict and weak noninitial crossing conventions agree outside the
single null event containing every noninitial zero position. -/
theorem gaussianHalfLineExit_zero_eq_weak_ae (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    gaussianHalfLineExit X 0 0 =ᵐ[μ] hittingAfter (gaussianDriftWalk X 0 0) (Iic 0) 1 := by
  filter_upwards [gaussianDriftWalk_nonzero_ae hX hi hG 0 0] with ω hω
  have he (j : ℕ) : (0 ≤ j ∧ gaussianDriftWalk X 0 0 j ω ∈ Iio 0) ↔
      (1 ≤ j ∧ gaussianDriftWalk X 0 0 j ω ∈ Iic 0) := by
    by_cases hj : j = 0
    · simp [hj, gaussianDriftWalk]
    · have hp : 0 < j := Nat.pos_of_ne_zero hj
      have hz := hω j hp
      simp only [mem_Iio, mem_Iic]
      constructor
      · intro h
        exact ⟨hp, h.2.le⟩
      · intro h
        exact ⟨Nat.zero_le _, lt_of_le_of_ne h.2 hz⟩
  simp only [gaussianHalfLineExit, hittingAfter, he]

theorem gaussianHalfLineOvershoot_zero_pos_ae (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ ω ∂μ, 0 < gaussianHalfLineOvershoot X 0 0 ω := by
  filter_upwards [gaussianHalfLineExit_zero_finite_ae hX hi hG (le_refl (0 : ℝ))] with ω hω
  rw [gaussianHalfLineOvershoot, if_neg hω]
  exact neg_pos.mpr (gaussianHalfLineExitPosition_neg hω)

theorem gaussianZeroLadderLaw_positive_ae (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    ∀ᵐ u ∂gaussianZeroLadderLaw X μ, 0 < u := by
  rw [gaussianZeroLadderLaw, ae_map_iff (gaussianHalfLineOvershoot_measurable hX 0 0).aemeasurable
    measurableSet_Ioi]
  exact gaussianHalfLineOvershoot_zero_pos_ae hX hi hG

/-- Canonical realization by the original infinite product of standard Gaussian
increments, not by a proposed ladder-height distribution. -/
theorem gaussianZeroLadderLaw_eq_canonical (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    gaussianZeroLadderLaw X μ = gaussianZeroLadderLaw (fun n (w : ℕ → ℝ) => w n)
      (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) := by
  have hp : μ.map (fun ω n => X n ω) =
      Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1) := by
    rw [hi.map_fun_eq_infinitePi_map hX]
    simp_rw [hG]
  have ho := gaussianHalfLineOvershoot_measurable (fun n => measurable_pi_apply n) 0 0
  unfold gaussianZeroLadderLaw
  rw [← hp, Measure.map_map ho (measurable_pi_lambda _ hX)]
  rfl

theorem gaussianIncrement_reflected_law (hX : ∀ n, Measurable (X n))
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (n : ℕ) :
    μ.map (fun ω => -X n ω) = gaussianReal 0 1 := by
  rw [show (fun ω => -X n ω) = Neg.neg ∘ X n from rfl,
    ← Measure.map_map measurable_neg (hX n), hG, gaussianReal_map_neg, neg_zero]

/-- Reflection leaves the actual strict ladder-height law unchanged. -/
theorem gaussianZeroLadderLaw_reflection (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    gaussianZeroLadderLaw (fun n ω => -X n ω) μ = gaussianZeroLadderLaw X μ := by
  have hh := gaussianZeroLadderLaw_eq_canonical (X := fun n ω => -X n ω)
    (fun n => (hX n).neg) (hi.comp (fun _ x => -x) (fun _ => measurable_neg))
    (gaussianIncrement_reflected_law hX hG)
  exact hh.trans (gaussianZeroLadderLaw_eq_canonical hX hi hG).symm

omit [MeasurableSpace Ω] in
theorem gaussianDriftWalk_zero_reflection (n : ℕ) (ω : Ω) :
    gaussianDriftWalk (fun n ω => -X n ω) 0 0 n ω = -gaussianDriftWalk X 0 0 n ω := by
  simp [gaussianDriftWalk, cumulativeSamples, Finset.sum_neg_distrib]

omit [MeasurableSpace Ω] in
/-- The reflected descending exit is exactly the first strict ascending exit of
the original zero-drift walk. -/
theorem gaussianHalfLineExit_reflection (ω : Ω) :
    gaussianHalfLineExit (fun n ω => -X n ω) 0 0 ω =
      hittingAfter (gaussianDriftWalk X 0 0) (Ioi 0) 0 ω := by
  simp only [gaussianHalfLineExit, hittingAfter, gaussianDriftWalk_zero_reflection,
    mem_Iio, neg_lt_zero, mem_Ioi]

theorem gaussianZeroLadderLaw_integrable (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (fun u : ℝ => u) (gaussianZeroLadderLaw X μ) := by
  apply (integrable_map_measure aestronglyMeasurable_id
    (gaussianHalfLineOvershoot_measurable hX 0 0).aemeasurable).mpr
  exact (gaussianHalfLineOvershoot_uniform_moments hX hi hG (le_refl (0 : ℝ)) le_rfl).1.1

theorem gaussianZeroLadderLaw_second_moment (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Integrable (fun u : ℝ => u^2) (gaussianZeroLadderLaw X μ) := by
  apply (integrable_map_measure (by fun_prop)
    (gaussianHalfLineOvershoot_measurable hX 0 0).aemeasurable).mpr
  exact (gaussianHalfLineOvershoot_uniform_moments hX hi hG (le_refl (0 : ℝ)) le_rfl).2.1

theorem gaussianZeroLadderLaw_exponential_moment (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    Integrable (fun u : ℝ => Real.exp (θ*u)) (gaussianZeroLadderLaw X μ) := by
  apply (integrable_map_measure (by fun_prop)
    (gaussianHalfLineOvershoot_measurable hX 0 0).aemeasurable).mpr
  exact gaussianHalfLineOvershoot_integrable_exp hX hi hG (le_refl (0 : ℝ)) le_rfl hθ

/-- The paper's zero-state potential is the first moment of this actual ladder
law. Identifying that moment numerically still requires the ladder factorization. -/
theorem gaussianRenewalPotential_zero_eq_ladder_mean (hX : ∀ n, Measurable (X n)) :
    gaussianRenewalPotential X μ 0 = ∫ u : ℝ, u ∂gaussianZeroLadderLaw X μ := by
  rw [gaussianRenewalPotential, zero_add, gaussianZeroLadderLaw,
    integral_map (f := fun u : ℝ => u) (gaussianHalfLineOvershoot_measurable hX 0 0).aemeasurable
      (by fun_prop)]

end SwingRepair
