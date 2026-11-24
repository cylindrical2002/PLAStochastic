import PLAStochastic.ForMathlib.Probability.Hellinger.Variational

/-!
# Hellinger contraction under arbitrary measurable outputs

The output densities represent the actual pushforward measures. A finite
dominating output measure is sufficient, and will always be available by taking
the sum of the two output probability measures. The input reference measure
need not be finite. This includes deterministic outputs without output densities
relative to Lebesgue measure, such as a whole finite leading tree.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

theorem integral_density_comp (p : HellingerDensity μ) (r : HellingerDensity ν)
    {F : α → β} (hF : Measurable F) (hmap : p.toMeasure.map F = r.toMeasure)
    {φ : β → ℝ} (hφ : Measurable φ) :
    (∫ x, p.density x * φ (F x) ∂μ) = ∫ y, r.density y * φ y ∂ν := by
  rw [← p.integral_toMeasure,
    ← integral_map hF.aemeasurable hφ.aestronglyMeasurable, hmap, r.integral_toMeasure]

theorem integrable_density_comp_iff (p : HellingerDensity μ) (r : HellingerDensity ν)
    {F : α → β} (hF : Measurable F) (hmap : p.toMeasure.map F = r.toMeasure)
    {φ : β → ℝ} (hφ : Measurable φ) :
    Integrable (fun x => p.density x * φ (F x)) μ ↔
      Integrable (fun y => r.density y * φ y) ν := by
  rw [← p.integrable_toMeasure_iff, ← r.integrable_toMeasure_iff]
  change Integrable (φ ∘ F) p.toMeasure ↔ Integrable φ r.toMeasure
  rw [← integrable_map_measure hφ.aestronglyMeasurable hF.aemeasurable, hmap]

theorem affinity_le_of_map [IsFiniteMeasure ν]
    (p q : HellingerDensity μ) (r s : HellingerDensity ν)
    {F : α → β} (hF : Measurable F)
    (hp : p.toMeasure.map F = r.toMeasure) (hq : q.toMeasure.map F = s.toMeasure) :
    p.affinity q ≤ r.affinity s := by
  have hb : 0 ≤ (∫ y, Real.sqrt (r.density y) ∂ν) +
      ∫ y, Real.sqrt (s.density y) ∂ν :=
    add_nonneg (integral_nonneg fun _ => Real.sqrt_nonneg _)
      (integral_nonneg fun _ => Real.sqrt_nonneg _)
  have hmain : 2 * p.affinity q ≤ 2 * r.affinity s := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let b := (∫ y, Real.sqrt (r.density y) ∂ν) +
      ∫ y, Real.sqrt (s.density y) ∂ν
    let δ := ε / (b + 1)
    have hδ : 0 < δ := div_pos hε (by dsimp [b]; linarith)
    have hφ := r.rootRatio_measurable s δ
    have hir := r.density_mul_rootRatio_integrable s hδ
    have his : Integrable (fun y => s.density y * (r.rootRatio s δ y)⁻¹) ν := by
      simpa only [rootRatio_reciprocal] using s.density_mul_rootRatio_integrable r hδ
    have hip := (integrable_density_comp_iff p r hF hp hφ).2 hir
    have hiq := (integrable_density_comp_iff q s hF hq hφ.inv).2 his
    have hy := affinity_le_test p q (fun x => r.rootRatio_pos s hδ (F x)) hip
      (by simpa only [div_eq_mul_inv, Pi.inv_apply] using hiq)
    rw [integral_density_comp p r hF hp hφ] at hy
    have heq := integral_density_comp q s hF hq hφ.inv
    change (∫ x, q.density x / r.rootRatio s δ (F x) ∂μ) =
      ∫ y, s.density y / r.rootRatio s δ y ∂ν at heq
    rw [heq] at hy
    have hreg := integral_rootRatio_test_le r s hδ
    have hδε : δ * b ≤ ε := by
      dsimp [δ]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by change 0 < b + 1; dsimp [b]; linarith)]
      nlinarith
    change _ ≤ 2 * r.affinity s + δ * b at hreg
    linarith
  linarith

theorem hellinger_le_of_map [IsFiniteMeasure ν]
    (p q : HellingerDensity μ) (r s : HellingerDensity ν)
    {F : α → β} (hF : Measurable F)
    (hp : p.toMeasure.map F = r.toMeasure) (hq : q.toMeasure.map F = s.toMeasure) :
    r.hellinger s ≤ p.hellinger q := by
  have h := affinity_le_of_map p q r s hF hp hq
  have h₁ := p.hellinger_sq_eq_affinity q
  have h₂ := r.hellinger_sq_eq_affinity s
  nlinarith [p.hellinger_nonneg q, r.hellinger_nonneg s]

end

end ProbabilityTheory.HellingerDensity
