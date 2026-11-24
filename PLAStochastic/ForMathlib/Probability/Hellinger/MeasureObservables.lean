import PLAStochastic.ForMathlib.Probability.Hellinger.MeasureMetric
import PLAStochastic.ForMathlib.Probability.Hellinger.Variational

/-!
# Observable and event bounds for actual probability measures

The common finite dominating measure pays the density representation. The
observable may be unbounded, with its actual second moments on both sides.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

theorem measureHellinger_observable (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {phi : α → ℝ} (hphi : Measurable phi)
    (hP : Integrable (fun x => phi x ^ 2) P) (hQ : Integrable (fun x => phi x ^ 2) Q) :
    |(∫ x, phi x ∂P) - ∫ x, phi x ∂Q| ≤ measureHellinger P Q *
      Real.sqrt (2 * ((∫ x, phi x ^ 2 ∂P) + ∫ x, phi x ^ 2 ∂Q)) := by
  let p := HellingerDensity.ofProbability P (P + Q)
    (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
  let q := HellingerDensity.ofProbability Q (P + Q)
    (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hp : p.toMeasure = P := HellingerDensity.ofProbability_toMeasure _ _ _
  have hq : q.toMeasure = Q := HellingerDensity.ofProbability_toMeasure _ _ _
  have hpi : Integrable (fun x => phi x ^ 2 * p.density x) (P + Q) := by
    simpa only [mul_comm] using
      (p.integrable_toMeasure_iff (fun x => phi x ^ 2)).mp (hp.symm ▸ hP)
  have hqi : Integrable (fun x => phi x ^ 2 * q.density x) (P + Q) := by
    simpa only [mul_comm] using
      (q.integrable_toMeasure_iff (fun x => phi x ^ 2)).mp (hq.symm ▸ hQ)
  have h := p.abs_integral_observable_sub_le q hphi hpi hqi
  have hmetric : measureHellinger P Q = p.hellinger q := by
    simpa only [hp, hq] using measureHellinger_eq_density_of_finite p q
  have hcomm (r : HellingerDensity (P + Q)) (F : α → ℝ) :
      (∫ x, F x * r.density x ∂(P + Q)) = ∫ x, F x ∂r.toMeasure := by
    rw [r.integral_toMeasure]
    simp only [mul_comm]
  simpa only [hcomm, hp, hq, ← hmetric] using h

theorem measureHellinger_sqrt_event (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {s : Set α} (hs : MeasurableSet s) :
    |Real.sqrt (P.real s) - Real.sqrt (Q.real s)| ≤ measureHellinger P Q := by
  let p := HellingerDensity.ofProbability P (P + Q)
    (Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl))
  let q := HellingerDensity.ofProbability Q (P + Q)
    (Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl))
  have hp : p.toMeasure = P := HellingerDensity.ofProbability_toMeasure _ _ _
  have hq : q.toMeasure = Q := HellingerDensity.ofProbability_toMeasure _ _ _
  have h := p.abs_sqrt_mass_sub_le q s hs
  have hmetric : measureHellinger P Q = p.hellinger q := by
    simpa only [hp, hq] using measureHellinger_eq_density_of_finite p q
  simpa only [HellingerDensity.mass_eq_measureReal _ hs, hp, hq, ← hmetric] using h

end

end ProbabilityTheory
