import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# A three-factor Hölder inequality with an indicator

`∫⁻ 1_A a b ≤ (∫⁻ a⁴)^{1/4} μ(A)^{1/4} (∫⁻ b²)^{1/2}` for nonnegative extended functions
(`lintegral_indicator_mul_le`), by two applications of Cauchy–Schwarz. This is the Hölder
step with exponents `(4, 4, 2)` used for a negative moment, a stopping event and a centred
sum (`research/2026-09-29-ceps-full-expansion/output-closure.md` (O11)).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PGM

variable {α : Type*} [MeasurableSpace α]

/-- **Three-factor Hölder inequality** with exponents `(4, 4, 2)`. -/
theorem lintegral_indicator_mul_le (μ : Measure α) {A : Set α} (hA : MeasurableSet A)
    {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) :
    ∫⁻ x, A.indicator a x * b x ∂μ ≤
      (∫⁻ x, a x ^ (4 : ℝ) ∂μ) ^ (1 / 4 : ℝ) * μ A ^ (1 / 4 : ℝ) *
        (∫⁻ x, b x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
  have hAa : AEMeasurable (A.indicator a) μ := ha.indicator hA
  have h1 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hAa hb
  have hsq : ∀ x, A.indicator a x ^ (2 : ℝ) = (a x ^ (2 : ℝ)) * A.indicator (fun _ => 1) x := by
    intro x
    by_cases hx : x ∈ A
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  have h2 := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => a x ^ (2 : ℝ)) (g := A.indicator fun _ => 1) (ha.pow_const _)
    ((aemeasurable_const).indicator hA)
  have h4 : ∀ x, (a x ^ (2 : ℝ)) ^ (2 : ℝ) = a x ^ (4 : ℝ) := by
    intro x; rw [← ENNReal.rpow_mul]; norm_num
  have hind : ∀ x, (A.indicator (fun _ => (1 : ℝ≥0∞)) x) ^ (2 : ℝ) =
      A.indicator (fun _ => 1) x := by
    intro x
    by_cases hx : x ∈ A
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]
  simp only [h4, hind] at h2
  rw [lintegral_indicator_const hA, one_mul] at h2
  simp only [Pi.mul_apply] at h1 h2
  simp_rw [hsq] at h1
  calc ∫⁻ x, A.indicator a x * b x ∂μ
      ≤ (∫⁻ x, a x ^ (2 : ℝ) * A.indicator (fun _ => 1) x ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ x, b x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := h1
    _ ≤ ((∫⁻ x, a x ^ (4 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ A ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∫⁻ x, b x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = (∫⁻ x, a x ^ (4 : ℝ) ∂μ) ^ (1 / 4 : ℝ) * μ A ^ (1 / 4 : ℝ) *
          (∫⁻ x, b x ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

end PGM
