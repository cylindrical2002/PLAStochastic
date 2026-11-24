import PLAStochastic.ForMathlib.Probability.Hellinger.RadonNikodym

/-!
# Metric identities for the actual measure-level Hellinger distance

Finite common dominating measures give exact density representations. Taking
the sum of three probability measures proves the triangle inequality without
absolute continuity restrictions. Measurable invertible maps preserve distance.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem measureHellinger_eq_density_of_finite {μ : Measure α} [IsFiniteMeasure μ]
    (p q : HellingerDensity μ) :
    measureHellinger p.toMeasure q.toMeasure = p.hellinger q := by
  apply le_antisymm (measureHellinger_le_density p q)
  apply HellingerDensity.hellinger_le_of_map
    (HellingerDensity.leftDensity p.toMeasure q.toMeasure)
    (HellingerDensity.rightDensity p.toMeasure q.toMeasure) p q measurable_id
  · simp only [Measure.map_id, HellingerDensity.leftDensity_toMeasure]
  · simp only [Measure.map_id, HellingerDensity.rightDensity_toMeasure]

theorem measureHellinger_triangle (P Q R : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    measureHellinger P R ≤ measureHellinger P Q + measureHellinger Q R := by
  let μ := P + Q + R
  have hPQ : P + Q ≤ μ := Measure.le_add_right le_rfl
  have hP : P ≪ μ := Measure.absolutelyContinuous_of_le
    ((Measure.le_add_right (show P ≤ P from le_rfl)).trans hPQ)
  have hQ : Q ≪ μ := Measure.absolutelyContinuous_of_le
    ((Measure.le_add_left (show Q ≤ Q from le_rfl)).trans hPQ)
  have hR : R ≪ μ := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  let p := HellingerDensity.ofProbability P μ hP
  let q := HellingerDensity.ofProbability Q μ hQ
  let r := HellingerDensity.ofProbability R μ hR
  have hp : p.toMeasure = P := HellingerDensity.ofProbability_toMeasure P μ hP
  have hq : q.toMeasure = Q := HellingerDensity.ofProbability_toMeasure Q μ hQ
  have hr : r.toMeasure = R := HellingerDensity.ofProbability_toMeasure R μ hR
  have hePR : measureHellinger P R = p.hellinger r := by
    simpa only [hp, hr] using measureHellinger_eq_density_of_finite p r
  have hePQ : measureHellinger P Q = p.hellinger q := by
    simpa only [hp, hq] using measureHellinger_eq_density_of_finite p q
  have heQR : measureHellinger Q R = q.hellinger r := by
    simpa only [hq, hr] using measureHellinger_eq_density_of_finite q r
  rw [hePR, hePQ, heQR]
  exact p.hellinger_triangle q r

theorem measureHellinger_comm (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    measureHellinger P Q = measureHellinger Q P := by
  let μ := P + Q
  let p := HellingerDensity.leftDensity P Q
  let q := HellingerDensity.rightDensity P Q
  have hp : p.toMeasure = P := HellingerDensity.leftDensity_toMeasure P Q
  have hq : q.toMeasure = Q := HellingerDensity.rightDensity_toMeasure P Q
  have hePQ : measureHellinger P Q = p.hellinger q := by
    simpa only [hp, hq] using measureHellinger_eq_density_of_finite p q
  have heQP : measureHellinger Q P = q.hellinger p := by
    simpa only [hp, hq] using measureHellinger_eq_density_of_finite q p
  rw [hePQ, heQP]
  exact p.hellinger_comm q

theorem measureHellinger_map_eq_of_leftInverse (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {F : α → β} {G : β → α} (hF : Measurable F) (hG : Measurable G)
    (hGF : Function.LeftInverse G F) :
    let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    let : IsProbabilityMeasure (Q.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
    measureHellinger (P.map F) (Q.map F) = measureHellinger P Q := by
  let : IsProbabilityMeasure (P.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  let : IsProbabilityMeasure (Q.map F) := Measure.isProbabilityMeasure_map hF.aemeasurable
  have he : G ∘ F = id := funext hGF
  apply le_antisymm (measureHellinger_map P Q hF)
  have hb := measureHellinger_map (P.map F) (Q.map F) hG
  simpa only [Measure.map_map hG hF, he, Measure.map_id] using hb

end

end ProbabilityTheory
