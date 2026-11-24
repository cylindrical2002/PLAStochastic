import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LargeDeviation
import Mathlib.Probability.Moments.Tilted

/-!
# Esscher step laws

The normalized tilt is defined using Mathlib's `Measure.tilted`. A root
`E exp (β Y) = exp q` identifies its density as `exp (β Y - q)`.
The mean changes under this operation; the envelope result therefore uses a
drifted step class rather than claiming that the tilt is centred.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM.WienerHopf

/-- The normalized real Esscher tilt of a step law. -/
def esscherLaw (ρ : Measure ℝ) (β : ℝ) : Measure ℝ :=
  ρ.tilted (fun y => β * y)

theorem isProbabilityMeasure_esscherLaw {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    {β : ℝ} (hβ : Integrable (fun y => Real.exp (β * y)) ρ) :
    IsProbabilityMeasure (esscherLaw ρ β) :=
  isProbabilityMeasure_tilted hβ

/-- At a real root, the normalization is the prescribed discount. -/
theorem esscherLaw_eq_withDensity {ρ : Measure ℝ} {β q : ℝ}
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    esscherLaw ρ β = ρ.withDensity (fun y => ENNReal.ofReal (Real.exp (β * y - q))) := by
  simp only [esscherLaw, Measure.tilted, hroot, Real.exp_sub]

theorem integral_esscherLaw {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ρ : Measure ℝ} {β q : ℝ}
    (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) (f : ℝ → E) :
    (∫ y, f y ∂esscherLaw ρ β) = ∫ y, Real.exp (β * y - q) • f y ∂ρ := by
  rw [esscherLaw, integral_tilted, hroot]
  simp only [Real.exp_sub]

theorem esscherLaw_density {ρ : Measure ℝ} {f : ℝ → ℝ} {β q : ℝ}
    (hρ : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y)))
    (hf : Measurable f) (hroot : (∫ y, Real.exp (β * y) ∂ρ) = Real.exp q) :
    esscherLaw ρ β = volume.withDensity
      (fun y => ENNReal.ofReal (Real.exp (β * y - q) * f y)) := by
  rw [esscherLaw_eq_withDensity hroot, hρ, ← withDensity_mul]
  · congr 1
    funext y
    simp only [Pi.mul_apply, ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact mul_comm _ _
  · exact hf.ennreal_ofReal
  · fun_prop

/-- The drifted version of the centred step class. The second moment is raw. -/
structure IsDriftedStepLaw (ρ : Measure ℝ) (f : ℝ → ℝ) (D θ μ v : ℝ) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure ρ
  eq_withDensity : ρ = volume.withDensity (fun y => ENNReal.ofReal (f y))
  measurable : Measurable f
  nonneg : ∀ y, 0 ≤ f y
  le_exp : ∀ y, f y ≤ D * Real.exp (-θ * |y|)
  integrable_sq : Integrable (fun y => y ^ 2) ρ
  integral_id : (∫ y, y ∂ρ) = μ
  integral_sq_le : (∫ y, y ^ 2 ∂ρ) ≤ v

/-- The tilted mean is the derivative of the real cumulant generating function. -/
theorem esscherLaw_mean {ρ : Measure ℝ} {β : ℝ}
    (hβ : β ∈ interior (integrableExpSet id ρ)) :
    (∫ y, y ∂esscherLaw ρ β) = deriv (cgf id ρ) β :=
  integral_tilted_mul_self hβ

end PGM.WienerHopf
