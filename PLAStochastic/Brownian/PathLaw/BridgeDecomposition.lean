import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Tactic

/-!
# Brownian bridge and its independent Gaussian endpoint

The bridge is constructed from the original Brownian motion. Joint Gaussianity
and zero cross-covariance prove independence of the entire bridge process from
the endpoint, not merely independence at each individual time.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace BrownianAffine

noncomputable section

abbrev BridgeTime := Set.Icc (0 : ℝ≥0) 1

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

def unitBrownianBridge (B : ℝ≥0 → Ω → ℝ) (t : BridgeTime) (ω : Ω) : ℝ :=
  B t ω - ((t : ℝ≥0) : ℝ) * B 1 ω

omit [MeasurableSpace Ω] in
theorem brownian_bridge_endpoint_decomposition (B : ℝ≥0 → Ω → ℝ)
    (t : BridgeTime) (ω : Ω) :
    B t ω = unitBrownianBridge B t ω + ((t : ℝ≥0) : ℝ) * B 1 ω := by
  simp only [unitBrownianBridge, sub_add_cancel]

theorem bridge_endpoint_jointly_gaussian (hB : IsPreBrownianReal B μ) :
    IsGaussianProcess (Sum.elim (unitBrownianBridge B) (fun _ : Unit => B 1)) μ := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro i
  cases i with
  | inl t =>
    refine ⟨{(t : ℝ≥0), 1},
      { toFun := fun x => x ⟨t, by simp⟩ - ((t : ℝ≥0) : ℝ) * x ⟨1, by simp⟩
        map_add' := by intro x y; simp only [Pi.add_apply]; ring
        map_smul' := by intro c x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }, ?_⟩
    intro ω
    rfl
  | inr u =>
    refine ⟨{1},
      { toFun := fun x => x ⟨1, by simp⟩
        map_add' := by intro x y; rfl
        map_smul' := by intro c x; rfl }, ?_⟩
    intro ω
    rfl

theorem unitBrownianBridge_isGaussianProcess (hB : IsPreBrownianReal B μ) :
    IsGaussianProcess (unitBrownianBridge B) μ :=
  (bridge_endpoint_jointly_gaussian hB).comp_right Sum.inl

theorem unitBrownianBridge_covariance_endpoint (hB : IsPreBrownianReal B μ) (t : BridgeTime) :
    covariance (unitBrownianBridge B t) (B 1) μ = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval (t : ℝ≥0)).memLp_two
  have h₁ := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  unfold unitBrownianBridge
  rw [covariance_fun_sub_left ht (h₁.const_mul _) h₁,
    covariance_const_mul_left, hB.covariance_eval, hB.covariance_eval]
  simp only [min_eq_left t.property.2, min_self, NNReal.coe_one, mul_one, sub_self]

/-- Independence is between the full bridge random function and the scalar endpoint. -/
theorem unitBrownianBridge_indep_endpoint (hB : IsPreBrownianReal B μ) :
    IndepFun (fun ω t => unitBrownianBridge B t ω) (B 1) μ := by
  have hind := (bridge_endpoint_jointly_gaussian hB).indepFun_of_covariance_eq_zero
    (fun t => (unitBrownianBridge_isGaussianProcess hB).aemeasurable t)
    (fun _ => hB.aemeasurable 1) (fun t _ => unitBrownianBridge_covariance_endpoint hB t)
  have heval : Measurable (fun f : Unit → ℝ => f ()) := measurable_pi_apply ()
  simpa only [Function.comp_def, id_eq] using hind.comp measurable_id heval

theorem brownian_endpoint_standard_normal (hB : IsPreBrownianReal B μ) :
    HasLaw (B 1) (gaussianReal 0 1) μ := hB.hasLaw_eval 1

theorem unitBrownianBridge_continuous_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, Continuous (fun t : BridgeTime => unitBrownianBridge B t ω) := by
  filter_upwards [hB.cont] with ω hω
  have ht : Continuous (fun t : BridgeTime => ((t : ℝ≥0) : ℝ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  exact (hω.comp (continuous_subtype_val : Continuous (fun t : BridgeTime => (t : ℝ≥0)))).sub
    (ht.mul_const _)

/-- The constructed bridge is centered. -/
theorem unitBrownianBridge_integral (hB : IsPreBrownianReal B μ) (t : BridgeTime) :
    (∫ ω, unitBrownianBridge B t ω ∂μ) = 0 := by
  unfold unitBrownianBridge
  rw [integral_sub (hB.integrable_eval t) ((hB.integrable_eval 1).const_mul _),
    integral_const_mul, hB.integral_eval, hB.integral_eval]
  ring

/-- The actual bridge has the standard unit-interval covariance kernel. -/
theorem unitBrownianBridge_covariance (hB : IsPreBrownianReal B μ) (s t : BridgeTime) :
    covariance (unitBrownianBridge B s) (unitBrownianBridge B t) μ =
      min ((s : ℝ≥0) : ℝ) ((t : ℝ≥0) : ℝ) - ((s : ℝ≥0) : ℝ) * ((t : ℝ≥0) : ℝ) := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval (s : ℝ≥0)).memLp_two
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval (t : ℝ≥0)).memLp_two
  have h₁ := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
  unfold unitBrownianBridge
  rw [covariance_fun_sub_fun_sub hs (h₁.const_mul _) ht (h₁.const_mul _)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval,
    min_eq_left s.property.2, min_eq_right t.property.2, min_self, NNReal.coe_one,
    NNReal.coe_min, mul_one]
  ring

omit [MeasurableSpace Ω] in
theorem unitBrownianBridge_one (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    unitBrownianBridge B ⟨1, by simp⟩ ω = 0 := by
  simp [unitBrownianBridge]

theorem unitBrownianBridge_zero_ae (hB : IsPreBrownianReal B μ) :
    ∀ᵐ ω ∂μ, unitBrownianBridge B ⟨0, by simp⟩ ω = 0 := by
  simpa only [unitBrownianBridge, NNReal.coe_zero, zero_mul, sub_zero] using
    hB.eval_zero_ae_eq_zero

end

end BrownianAffine
