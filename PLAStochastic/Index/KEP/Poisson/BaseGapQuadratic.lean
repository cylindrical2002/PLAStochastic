import PLAStochastic.Index.KEP.Poisson.BaseGapCoordinates

/-!
# Quadratic displacement of the actual base-gap transformation

The error between physical normalization and cumulative-intensity time is an
integral of the original intensity variation. Its Lipschitz bound is uniform
over anchors and has the required inverse-intensity rate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepPoissonNormalizedGap_sub_bound {f : ℝ → ℝ} {flo fhi L n t : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (ht : 0 ≤ t) (x : ℝ) :
    |kepPoissonNormalizedGap hf n x t - t| ≤ (L / flo ^ 2) * t ^ 2 / n := by
  let y := kepPoissonArrival hf n x t
  have hy : x ≤ y := kepPoissonArrival_ge hf hn ht x
  have hgap : 0 ≤ y - x := sub_nonneg.mpr hy
  have hL := hf.lip_nonneg
  have hlo := hf.pos
  have he : kepPoissonNormalizedGap hf n x t - t = n * ∫ v in x..y, f x - f v := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hf.intervalIntegrable x y),
      intervalIntegral.integral_const, smul_eq_mul, ← kepIntensityPrimitive_sub hf]
    dsimp [y]
    rw [kepPoissonArrival_intensity]
    unfold kepPoissonNormalizedGap
    field_simp [hn.ne']
    ring
  have hi : |∫ v in x..y, f x - f v| ≤ L * (y - x) ^ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := x) (b := y) (f := fun v => f x - f v) (C := L * (y - x)) (fun v hv => by
        rw [uIoc_of_le hy] at hv
        rw [Real.norm_eq_abs]
        apply (hf.lip x v).trans
        rw [abs_sub_comm, abs_of_nonneg (by linarith only [hv.1] : 0 ≤ v - x)]
        exact mul_le_mul_of_nonneg_left (by linarith only [hv.2]) hL)
    rw [Real.norm_eq_abs, abs_of_nonneg hgap] at h
    nlinarith only [h]
  rw [he, abs_mul, abs_of_pos hn]
  calc
    _ ≤ n * (L * (y - x) ^ 2) := mul_le_mul_of_nonneg_left hi hn.le
    _ ≤ n * (L * (t / (n * flo)) ^ 2) := by
      gcongr
      exact (kepPoissonArrival_gap_bracket hf hn ht x).2
    _ = _ := by field_simp [hn.ne', hlo.ne']

end

end PGM
