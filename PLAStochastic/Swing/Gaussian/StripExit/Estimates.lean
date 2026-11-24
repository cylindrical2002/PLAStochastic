import PLAStochastic.Swing.Gaussian.Stopping.ExitMeanFromOvershoot
import PLAStochastic.Swing.Gaussian.Stopping.ExitWald
import PLAStochastic.Swing.Gaussian.StripExit.OvershootMoments

/-! # Uniform actual Gaussian strip-exit estimates, with no overshoot hypotheses -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def gaussianExitMeanConstant : ℝ := 2+4*gaussianExcessExpMomentBound 2

def gaussianUpperExitConstant : ℝ := 1+gaussianExitMeanConstant/2+gaussianExcessExpMomentBound 2

theorem gaussianExitMeanConstant_pos : 0 < gaussianExitMeanConstant := by
  have h := gaussianExcessExpMomentBound_pos 2
  dsimp [gaussianExitMeanConstant]
  positivity

theorem gaussianUpperExitConstant_pos : 0 < gaussianUpperExitConstant := by
  have h := gaussianExcessExpMomentBound_pos 2
  have h' := gaussianExitMeanConstant_pos
  dsimp [gaussianUpperExitConstant]
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Uniform capped mean under exactly the original Gaussian, strip and drift assumptions. -/
theorem gaussianStrip_capped_mean_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (haR : a*R ≤ 1/2) (m : ℕ) :
    (∫ ω, (capDiscreteTime (gaussianStripExit X x a R ω) m : ℝ) ∂μ) ≤
      gaussianExitMeanConstant * R * (x+1) := by
  obtain ⟨h₁, h₂⟩ := gaussianStripOvershoot_uniform_moments hX hi hG hx ha ha'
  exact (gaussianStrip_capped_mean_le_of_overshoot hX hi hG x (by linarith) ha haR
    h₁.1 h₂.1 h₁.2 h₂.2 m).trans
      (stripPotential_mean_bound hx.1 hR (gaussianExcessExpMomentBound_pos 2).le)

/-- The true first exit is almost surely finite and its mean has the paper's R(x+1) bound. -/
theorem gaussianStrip_exit_mean_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (haR : a*R ≤ 1/2) :
    (∀ᵐ ω ∂μ, gaussianStripExit X x a R ω ≠ ⊤) ∧
      Integrable (fun ω => (((gaussianStripExit X x a R ω).untopD 0 : ℕ) : ℝ)) μ ∧
      (∫ ω, (((gaussianStripExit X x a R ω).untopD 0 : ℕ) : ℝ) ∂μ) ≤
        gaussianExitMeanConstant * R * (x+1) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  exact discreteTime_ae_finite_integrable_mean_le_of_cap_bound
    (gaussianStripExit_isStoppingTime hX x a R).measurable'
    (gaussianStrip_capped_mean_le hX hi hG hx hR ha ha' haR)

/-- Upper exit probability from true Wald stopping and the true selected overshoot bound. -/
theorem gaussianStrip_upperExit_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (haR : a*R ≤ 1/2) :
    μ.real (gaussianStripUpperExit X x a R) ≤ gaussianUpperExitConstant * (x+1) / R := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hR0 : 0 ≤ R := by linarith
  obtain ⟨hf, ht, hm⟩ := gaussianStrip_exit_mean_le hX hi hG hx hR ha ha' haR
  obtain ⟨h₁, _⟩ := gaussianStripOvershoot_uniform_moments hX hi hG hx ha ha'
  have hu := gaussianStrip_upperExit_mul_le hX hR0 hf h₁.1
  rw [gaussianStrip_exitPosition_integral_eq hX hi hG hR0 hf ht h₁.1] at hu
  have haM := mul_le_mul_of_nonneg_left hm ha
  have hax : a * (gaussianExitMeanConstant*R*(x+1)) ≤ gaussianExitMeanConstant/2*(x+1) := by
    have hh := mul_le_mul_of_nonneg_right haR
      (mul_nonneg gaussianExitMeanConstant_pos.le (by linarith [hx.1] : 0 ≤ x+1))
    nlinarith
  apply (le_div_iff₀ (by linarith : 0 < R)).mpr
  have hxM := mul_nonneg (gaussianExcessExpMomentBound_pos 2).le hx.1
  dsimp only [gaussianUpperExitConstant]
  nlinarith [h₁.2]

end SwingRepair
