import PLAStochastic.ForMathlib.Probability.Hellinger.Measure
import PLAStochastic.ForMathlib.Probability.Hellinger.Affinity

/-!
# Variational bounds for affinity

Young's inequality bounds affinity by a positive test and its reciprocal.
Regularised square-root ratios approach the optimum. The output reference
measure may be any finite measure; no positive lower bound on a density is used.
-/

set_option autoImplicit false

namespace ProbabilityTheory.HellingerDensity

noncomputable section

open MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

theorem integrable_toMeasure_iff (p : HellingerDensity μ) (φ : α → ℝ) :
    Integrable φ p.toMeasure ↔ Integrable (fun x => p.density x * φ x) μ := by
  rw [toMeasure, integrable_withDensity_iff_integrable_smul'
    p.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (p.nonneg _), smul_eq_mul]

theorem sqrt_mul_le_test {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 < t) :
    2 * (Real.sqrt a * Real.sqrt b) ≤ a * t + b / t := by
  have hs := sq_nonneg (Real.sqrt a * t - Real.sqrt b)
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  apply (mul_le_mul_iff_left₀ ht).mp
  have he : (a * t + b / t) * t = a * t ^ 2 + b := by
    field_simp
  rw [he]
  nlinarith [congrArg (fun z : ℝ => z * t ^ 2) hsa]

theorem affinity_le_test (p q : HellingerDensity μ) {φ : α → ℝ}
    (hφ : ∀ x, 0 < φ x)
    (hp : Integrable (fun x => p.density x * φ x) μ)
    (hq : Integrable (fun x => q.density x / φ x) μ) :
    2 * p.affinity q ≤
      (∫ x, p.density x * φ x ∂μ) + ∫ x, q.density x / φ x ∂μ := by
  rw [affinity, ← integral_const_mul, ← integral_add hp hq]
  exact integral_mono ((p.affinity_integrable q).const_mul 2) (hp.add hq)
    fun x => sqrt_mul_le_test (p.nonneg x) (q.nonneg x) (hφ x)

def rootRatio (p q : HellingerDensity μ) (δ : ℝ) (x : α) : ℝ :=
  (Real.sqrt (q.density x) + δ) / (Real.sqrt (p.density x) + δ)

theorem rootRatio_measurable (p q : HellingerDensity μ) (δ : ℝ) :
    Measurable (p.rootRatio q δ) :=
  (q.measurable.sqrt.add_const δ).div (p.measurable.sqrt.add_const δ)

theorem rootRatio_pos (p q : HellingerDensity μ) {δ : ℝ} (hδ : 0 < δ) (x : α) :
    0 < p.rootRatio q δ x :=
  div_pos (by linarith [Real.sqrt_nonneg (q.density x)])
    (by linarith [Real.sqrt_nonneg (p.density x)])

theorem rootRatio_reciprocal (p q : HellingerDensity μ) (δ : ℝ) (x : α) :
    (p.rootRatio q δ x)⁻¹ = q.rootRatio p δ x := by
  simp only [rootRatio, inv_div]

theorem density_mul_rootRatio_le (p q : HellingerDensity μ) {δ : ℝ}
    (hδ : 0 < δ) (x : α) :
    p.density x * p.rootRatio q δ x ≤
      Real.sqrt (p.density x) * Real.sqrt (q.density x) +
        δ * Real.sqrt (p.density x) := by
  have hden : 0 < Real.sqrt (p.density x) + δ := by
    linarith [Real.sqrt_nonneg (p.density x)]
  have hfrac : p.density x / (Real.sqrt (p.density x) + δ) ≤
      Real.sqrt (p.density x) := by
    rw [div_le_iff₀ hden]
    nlinarith [Real.mul_self_sqrt (p.nonneg x),
      mul_nonneg (Real.sqrt_nonneg (p.density x)) hδ.le]
  calc
    p.density x * p.rootRatio q δ x =
        (p.density x / (Real.sqrt (p.density x) + δ)) *
          (Real.sqrt (q.density x) + δ) := by unfold rootRatio; ring
    _ ≤ Real.sqrt (p.density x) * (Real.sqrt (q.density x) + δ) :=
      mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = _ := by ring

theorem density_mul_rootRatio_integrable [IsFiniteMeasure μ]
    (p q : HellingerDensity μ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => p.density x * p.rootRatio q δ x) μ := by
  refine ((p.affinity_integrable q).add
    ((p.sqrt_memLp.integrable (by norm_num)).const_mul δ)).mono'
      (p.measurable.mul (p.rootRatio_measurable q δ)).aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (p.nonneg x) (p.rootRatio_pos q hδ x).le)]
    exact density_mul_rootRatio_le p q hδ x

theorem integral_rootRatio_test_le [IsFiniteMeasure μ]
    (p q : HellingerDensity μ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x, p.density x * p.rootRatio q δ x ∂μ) +
        (∫ x, q.density x / p.rootRatio q δ x ∂μ) ≤
      2 * p.affinity q + δ *
        ((∫ x, Real.sqrt (p.density x) ∂μ) + ∫ x, Real.sqrt (q.density x) ∂μ) := by
  have hp := p.density_mul_rootRatio_integrable q hδ
  have hq := q.density_mul_rootRatio_integrable p hδ
  have hb₁ := (p.affinity_integrable q).add
    ((p.sqrt_memLp.integrable (by norm_num)).const_mul δ)
  have hb₂ := (q.affinity_integrable p).add
    ((q.sqrt_memLp.integrable (by norm_num)).const_mul δ)
  have h₁ := integral_mono hp hb₁ (density_mul_rootRatio_le p q hδ)
  have h₂ := integral_mono hq hb₂ (density_mul_rootRatio_le q p hδ)
  change (∫ x, p.density x * p.rootRatio q δ x ∂μ) ≤
    ∫ x, Real.sqrt (p.density x) * Real.sqrt (q.density x) +
      δ * Real.sqrt (p.density x) ∂μ at h₁
  change (∫ x, q.density x * q.rootRatio p δ x ∂μ) ≤
    ∫ x, Real.sqrt (q.density x) * Real.sqrt (p.density x) +
      δ * Real.sqrt (q.density x) ∂μ at h₂
  rw [integral_add (p.affinity_integrable q)
    ((p.sqrt_memLp.integrable (by norm_num)).const_mul δ), integral_const_mul] at h₁
  rw [integral_add (q.affinity_integrable p)
    ((q.sqrt_memLp.integrable (by norm_num)).const_mul δ), integral_const_mul] at h₂
  have he : (fun x => q.density x / p.rootRatio q δ x) =
      fun x => q.density x * q.rootRatio p δ x := by
    funext x
    rw [div_eq_mul_inv, rootRatio_reciprocal]
  rw [he]
  change (∫ x, p.density x * p.rootRatio q δ x ∂μ) ≤
    p.affinity q + δ * ∫ x, Real.sqrt (p.density x) ∂μ at h₁
  change (∫ x, q.density x * q.rootRatio p δ x ∂μ) ≤
    q.affinity p + δ * ∫ x, Real.sqrt (q.density x) ∂μ at h₂
  have heaff : q.affinity p = p.affinity q := by
    unfold affinity
    congr 1
    funext x
    exact mul_comm _ _
  rw [heaff] at h₂
  linarith

end

end ProbabilityTheory.HellingerDensity
