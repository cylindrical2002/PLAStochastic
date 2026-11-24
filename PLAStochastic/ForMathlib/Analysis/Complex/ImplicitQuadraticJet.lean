import PLAStochastic.ForMathlib.Analysis.Complex.TaylorSeriesCongr
import Mathlib.Analysis.Calculus.DSlope

/-! # Finite-jet stability of a nondegenerate implicit quadratic root

The hypotheses describe genuine analytic root germs and the continuous moving
spatial divided difference of the quadratic unit, including diagonal points.
-/

noncomputable section
open Complex Set Metric Filter Topology PowerSeries
namespace PGM

theorem implicitQuadraticRoot_difference_budget {H H' f g : ℂ → ℂ} {lam : ℂ}
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0) (hH : ContinuousAt H 0)
    (hS : ContinuousAt (fun b : ℂ => dslope H (b * g b) (b * f b)) 0)
    (hzero : f 0 = g 0) (hgap : lam + 2 * f 0 * H 0 ≠ 0)
    (he : ∀ᶠ b : ℂ in 𝓝 0,
      f b ^ 2 * H (b * f b) + lam * f b = g b ^ 2 * H' (b * g b) + lam * g b)
    (N : ℕ) {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hunit : ∀ s ∈ ball (0 : ℂ) R, ‖H' s - H s‖ ≤ K * ‖s‖ ^ (N + 1)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ b : ℂ, ‖b‖ < B →
      ‖f b - g b‖ ≤ C * ‖b‖ ^ (N + 1) := by
  let E : ℂ → ℂ := fun b => lam + (f b + g b) * H (b * f b) +
    b * g b ^ 2 * dslope H (b * g b) (b * f b)
  let U : ℝ := ‖g 0‖ + 1
  let L : ℝ := ‖lam + 2 * f 0 * H 0‖ / 2
  have hU : 0 < U := by dsimp [U]; positivity
  have hL : 0 < L := half_pos (norm_pos_iff.mpr hgap)
  have hcomp : ContinuousAt (fun b : ℂ => H (b * f b)) 0 :=
    hH.comp_of_eq (continuousAt_id.mul hf) (by simp)
  have hcE : ContinuousAt E 0 :=
    (continuousAt_const.add ((hf.add hg).mul hcomp)).add
      ((continuousAt_id.mul (hg.pow 2)).mul hS)
  have hE0 : E 0 = lam + 2 * f 0 * H 0 := by
    simp only [E, zero_mul, add_zero]
    rw [← hzero]
    ring
  have hlow : ∀ᶠ b : ℂ in 𝓝 0, L < ‖E b‖ :=
    hcE.norm.eventually (isOpen_Ioi.mem_nhds (by
      change L < ‖E 0‖
      rw [hE0]
      dsimp [L]
      linarith [norm_pos_iff.mpr hgap]))
  have hgb : ∀ᶠ b : ℂ in 𝓝 0, ‖g b‖ < U :=
    hg.norm.eventually (isOpen_Iio.mem_nhds (show ‖g 0‖ < U by dsimp [U]; linarith))
  have hc0 : Tendsto (fun b : ℂ => b * g b) (𝓝 0) (𝓝 0) := by
    simpa using! (continuousAt_id.mul hg).tendsto
  have hmap := hc0.eventually (ball_mem_nhds (0 : ℂ) hR)
  obtain ⟨B, hB, hball⟩ := Metric.mem_nhds_iff.mp (he.and (hlow.and (hgb.and hmap)))
  refine ⟨K * U ^ (N + 3) / L, B, by positivity, hB, ?_⟩
  intro b hb
  obtain ⟨heq, hl, hu, hm⟩ := hball (mem_ball_zero_iff.mpr hb)
  have hslope := sub_smul_dslope H (b * g b) (b * f b)
  simp only [smul_eq_mul] at hslope
  have hid : (f b - g b) * E b = g b ^ 2 * (H' (b * g b) - H (b * g b)) := by
    dsimp only [E]
    linear_combination heq + g b ^ 2 * hslope
  have hprod : ‖f b - g b‖ * L ≤ K * U ^ (N + 3) * ‖b‖ ^ (N + 1) := by
    calc
      _ ≤ ‖f b - g b‖ * ‖E b‖ := mul_le_mul_of_nonneg_left hl.le (norm_nonneg _)
      _ = ‖g b‖ ^ 2 * ‖H' (b * g b) - H (b * g b)‖ := by
        rw [← norm_mul, hid, norm_mul, norm_pow]
      _ ≤ U ^ 2 * (K * (‖b‖ * U) ^ (N + 1)) := by
        apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hu.le 2) ?_ (norm_nonneg _) (by positivity)
        apply (hunit _ hm).trans
        rw [norm_mul]
        gcongr
      _ = _ := by rw [mul_pow, show N + 3 = 2 + (N + 1) by omega, pow_add]; ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hL]
  exact hprod

end PGM
