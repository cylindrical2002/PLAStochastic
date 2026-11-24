import PLAStochastic.Swing.Gaussian.Stopping.CappedExitPosition
import PLAStochastic.Swing.Gaussian.Stopping.StoppedLinearDrift

/-! # Exit-time estimates obtained from actual selected-overshoot moments -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Assembly lemma: bounded stopping is used before finiteness of the actual exit.
The overshoot hypotheses refer to the selected first-exit overshoot itself. -/
theorem gaussianStrip_capped_mean_le_of_overshoot
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x : ℝ) {a R M : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a*R ≤ 1/2)
    (hO : Integrable (gaussianStripOvershoot X x a R) μ)
    (hO₂ : Integrable (fun ω => (gaussianStripOvershoot X x a R ω)^2) μ)
    (hM₁ : (∫ ω, gaussianStripOvershoot X x a R ω ∂μ) ≤ M)
    (hM₂ : (∫ ω, (gaussianStripOvershoot X x a R ω)^2 ∂μ) ≤ M) (m : ℕ) :
    (∫ ω, (capDiscreteTime (gaussianStripExit X x a R ω) m : ℝ) ∂μ) ≤
      2 * stripPotential R x + 2*M*(R+1) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hτ : Measurable[mΩ] (gaussianStripExit X x a R) :=
    (gaussianStripExit_isStoppingTime hX x a R).measurable'
  have hP := capDiscreteTime_potential_integrable hτ
    (gaussianDriftWalk_potential_integrable hX hG x a R) m
  have hlo := integral_mono ((hO.const_mul (-R)).sub hO₂) hP
    (fun ω => gaussianStrip_capped_potential_lower (X := X) (x := x) (a := a) (R := R) m ω)
  simp only [Pi.sub_apply] at hlo
  rw [integral_sub (hO.const_mul (-R)) hO₂, integral_const_mul] at hlo
  have hup := gaussianStrip_capped_potential_le hX hi hG x ha haR m
  nlinarith [mul_le_mul_of_nonneg_left hM₁ hR]

/-- Uniform capped bounds imply actual almost-sure finiteness and the true mean estimate. -/
theorem gaussianStrip_exit_mean_le_of_overshoot
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (x : ℝ) {a R M : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) (haR : a*R ≤ 1/2)
    (hO : Integrable (gaussianStripOvershoot X x a R) μ)
    (hO₂ : Integrable (fun ω => (gaussianStripOvershoot X x a R ω)^2) μ)
    (hM₁ : (∫ ω, gaussianStripOvershoot X x a R ω ∂μ) ≤ M)
    (hM₂ : (∫ ω, (gaussianStripOvershoot X x a R ω)^2 ∂μ) ≤ M) :
    (∀ᵐ ω ∂μ, gaussianStripExit X x a R ω ≠ ⊤) ∧
      Integrable (fun ω => (((gaussianStripExit X x a R ω).untopD 0 : ℕ) : ℝ)) μ ∧
      (∫ ω, (((gaussianStripExit X x a R ω).untopD 0 : ℕ) : ℝ) ∂μ) ≤
        2 * stripPotential R x + 2*M*(R+1) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  exact discreteTime_ae_finite_integrable_mean_le_of_cap_bound
    (gaussianStripExit_isStoppingTime hX x a R).measurable'
    (gaussianStrip_capped_mean_le_of_overshoot hX hi hG x hR ha haR hO hO₂ hM₁ hM₂)

/-- The exact potential expression has the paper's uniform R(x+1) form. -/
theorem stripPotential_mean_bound {x R M : ℝ} (hx : 0 ≤ x) (hR : 1 ≤ R) (hM : 0 ≤ M) :
    2 * stripPotential R x + 2*M*(R+1) ≤ (2+4*M)*R*(x+1) := by
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hφ : stripPotential R x ≤ R*x := by unfold stripPotential; nlinarith [sq_nonneg x]
  have hr : 2*M*(R+1) ≤ 4*M*R := by nlinarith [mul_nonneg hM (sub_nonneg.mpr hR)]
  nlinarith [mul_nonneg (mul_nonneg hM hR0) hx]

end SwingRepair
