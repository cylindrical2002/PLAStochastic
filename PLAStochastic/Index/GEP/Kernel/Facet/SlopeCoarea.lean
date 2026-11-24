import PLAStochastic.ForMathlib.MeasureTheory.Measure.Lebesgue.WeightedAffineDensity
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Slope coarea for an actual two-block linear facet root

The first coordinate parametrizes the physical first-block length and the
second is eliminated by the actual affine root density. Changing the first
length to slope gives exactly the coefficient `q/a^2`. All path weights may
depend jointly on both coordinates; no independence of an active selector is
assumed and no input density is differentiated.
-/

namespace PGM
noncomputable section
open MeasureTheory Set
open scoped ENNReal

theorem kernel_reciprocal_image {p : ℝ} (hp : 0 < p) (c : ℝ) :
    (fun a : ℝ => p / a - c) '' Ioi 0 = Ioi (-c) := by
  ext u
  constructor
  · rintro ⟨a, ha, rfl⟩
    have h := div_pos hp ha
    change -c < p / a - c
    linarith
  · intro hu
    have hu' : 0 < u + c := by change -c < u at hu; linarith
    refine ⟨p / (u + c), div_pos hp hu', ?_⟩
    field_simp
    ring

/-- Exact positive-slope substitution, including its full reciprocal Jacobian. -/
theorem kernel_lintegral_reciprocal {p : ℝ} (hp : 0 < p) (c : ℝ)
    (G : ℝ → ℝ≥0∞) :
    (∫⁻ u in Ioi (-c), G u) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (p / a ^ 2) * G (p / a - c) := by
  have hd (a : ℝ) (ha : a ∈ Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun a : ℝ => p / a - c) (-p / a ^ 2) (Ioi 0) a := by
    have hder : HasDerivAt (fun z : ℝ => p / z - c) ((0 * a - p * 1) / a ^ 2) a :=
      ((hasDerivAt_const a p).div (hasDerivAt_id a) (ne_of_gt ha)).sub_const c
    simpa only [zero_mul, mul_one, zero_sub] using hder.hasDerivWithinAt (s := Ioi 0)
  have hinj : InjOn (fun a : ℝ => p / a - c) (Ioi 0) := by
    intro a ha b hb hab
    have hh : p / a = p / b := sub_left_inj.mp hab
    have hh' := (div_eq_div_iff (ne_of_gt ha) (ne_of_gt hb)).mp hh
    exact (mul_left_cancel₀ (ne_of_gt hp) hh').symm
  have h := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi hd hinj G
  rw [kernel_reciprocal_image hp c] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro a _
  dsimp only
  have hn : 0 ≤ p / a ^ 2 := div_nonneg hp.le (sq_nonneg _)
  rw [show -p / a ^ 2 = -(p / a ^ 2) by ring, abs_neg, abs_of_nonneg hn]

/-- Eliminate the second block in the linear facet root, then change the first
physical length to slope. The displayed coefficient is exact for arbitrary
joint nonnegative weights, including infinite mass. -/
theorem kernel_facet_slope_lintegral {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (x c d : ℝ) (W : ℝ × ℝ → ℝ≥0∞) :
    ENNReal.ofReal (q / p) *
        (∫⁻ u in Ioi (-(x + c)), W (u, (q / p) * (x + u + c) - d)) =
      ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
        W (p / a - x - c, q / a - d) := by
  rw [kernel_lintegral_reciprocal hp (x + c)]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro a ha
  dsimp only
  have h₁ : p / a - (x + c) = p / a - x - c := by ring
  have h₂ : q / p * (x + (p / a - (x + c)) + c) - d = q / a - d := by
    field_simp
    ring
  rw [h₂, h₁, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hq.le hp.le)]
  congr 2
  field_simp

/-- Measure-level coarea for the actual linear facet root. Positivity is only
the physical second-block constraint. The path weight remains fully joint. -/
theorem kernel_linear_facet_map_slope_density {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (c d : ℝ) {W : ℝ × ℝ → ℝ≥0∞} (hW : Measurable W)
    (hpos : ∀ u v, v + d ≤ 0 → W (u, v) = 0) :
    ((volume.prod volume).withDensity W).map
        (fun z : ℝ × ℝ => (p / q) * (z.2 + d) - z.1 - c) =
      volume.withDensity (fun x => ∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (q / a ^ 2) *
        W (p / a - x - c, q / a - d)) := by
  have hpq : p / q ≠ 0 := div_ne_zero hp.ne' hq.ne'
  have he : (fun z : ℝ × ℝ => (p / q) * (z.2 + d) - z.1 - c) =
      fun z => ((p / q) * d - z.1 - c) + (p / q) * z.2 := by funext z; ring
  rw [he, kernel_weighted_affine_map_density volume hpq
    (b := fun u : ℝ => p / q * d - u - c) (by fun_prop) hW]
  congr 1
  funext x
  unfold kernelLinearDensity
  have hc : |(p / q)⁻¹| = q / p := by
    rw [inv_div, abs_of_pos (div_pos hq hp)]
  have hv (u : ℝ) : (x - (p / q * d - u - c)) / (p / q) =
      q / p * (x + u + c) - d := by field_simp; ring
  simp_rw [hc, hv]
  have hs : (∫⁻ u, W (u, q / p * (x + u + c) - d)) =
      ∫⁻ u in Ioi (-(x + c)), W (u, q / p * (x + u + c) - d) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ Ioi (-(x + c))
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu]
      apply hpos
      have hn : x + u + c ≤ 0 := by
        change ¬ -(x + c) < u at hu
        linarith
      have hnon := mul_nonpos_of_nonneg_of_nonpos (div_pos hq hp).le hn
      linarith
  rw [hs]
  exact kernel_facet_slope_lintegral hp hq x c d W

end
end PGM
