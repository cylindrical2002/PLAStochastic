import PLAStochastic.Index.GEP.StrongApprox.Quantile.AffineQuantile
import PLAStochastic.Index.GEP.StrongApprox.Quantile.RateEnvelopeTail

/-! # WP5: affine normalization of actual densities and their CDF tails -/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set

theorem sa_integral_affine (f : ℝ → ℝ) (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    (∫ x : ℝ, σ * f (c + σ * x)) = ∫ x : ℝ, f x := by
  rw [integral_const_mul]
  have ht := Measure.integral_comp_mul_left (fun x => f (c + x)) σ
  rw [integral_add_left_eq_self f c, abs_of_pos (inv_pos.mpr hσ), smul_eq_mul] at ht
  rw [ht, ← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul]

/-- The normalized affine density, with its mass and integrability proved. -/
theorem SADensity.affine {p : ℝ → ℝ} (hp : SADensity p) (c : ℝ) {σ : ℝ} (hσ : 0 < σ) :
    SADensity (fun x => σ * p (c + σ * x)) := by
  have hpcont := hp.continuous
  refine ⟨by fun_prop, fun x => mul_pos hσ (hp.pos _), ?_, ?_, ?_⟩
  · exact ((hp.integrable.comp_add_left c).comp_mul_left' hσ.ne').const_mul σ
  · rw [sa_integral_affine _ _ hσ, hp.mass]
  · obtain ⟨C, hC⟩ := hp.bounded
    exact ⟨σ * C, fun x => mul_le_mul_of_nonneg_left (hC _) hσ.le⟩

/-- The affine CDF belongs to the actual normalized density, at every real point. -/
theorem SADensity.cdf_affine {p : ℝ → ℝ} (hp : SADensity p) (c : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (x : ℝ) :
    cdf ((hp.affine c hσ).law : Measure ℝ) x = cdf (hp.law : Measure ℝ) (c + σ * x) := by
  rw [(hp.affine c hσ).cdf_eq_integral, hp.cdf_eq_integral,
    ← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have he : (Iic x).indicator (fun y => σ * p (c + σ * y)) =
      fun y => σ * ((Iic (c + σ * x)).indicator p) (c + σ * y) := by
    funext y
    have hy : c + σ * y ≤ c + σ * x ↔ y ≤ x := by constructor <;> intro h <;> nlinarith
    by_cases h : y ≤ x
    · simp only [mem_Iic, h, hy.mpr h, indicator_of_mem]
    · simp only [mem_Iic, h, not_false_eq_true, indicator_of_notMem, hy.not.mpr h, mul_zero]
  rw [he, sa_integral_affine _ _ hσ]

/-- A density envelope after centering and scaling controls the two actual CDF
tails before normalization. -/
theorem SADensity.affine_tails_le_rateEnvelope {p : ℝ → ℝ} (hp : SADensity p)
    (m : ℝ) {σ A c R Y : ℝ} (hσ : 0 < σ) (hA : 0 ≤ A)
    (hc : 0 < c) (hR : 0 < R) (hY : 0 < Y)
    (hb : ∀ x, Y ≤ |x| → σ * p (m + σ * x) ≤
      A * Real.exp (-c * min (x ^ 2) (R * |x|))) :
    cdf (hp.law : Measure ℝ) (m - σ * Y) ≤
        A * Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) ∧
      1 - cdf (hp.law : Measure ℝ) (m + σ * Y) ≤
        A * Real.exp (-c * min (Y ^ 2) (R * Y)) / (c * min Y R) := by
  have ht := (hp.affine m hσ).tails_le_rateEnvelope hA hc hR hY hb
  rw [hp.cdf_affine m hσ (-Y), hp.cdf_affine m hσ Y] at ht
  simpa only [mul_neg, ← sub_eq_add_neg] using ht.symm

end

end PGM
