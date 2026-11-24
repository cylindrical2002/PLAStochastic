import PLAStochastic.ForMathlib.MeasureTheory.Measure.Lebesgue.WeightedAffineDensity
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.Tactic

/-!
# A designated one-gap bridge after integration in the slope

At a fixed slope the endpoint `1 - a*x` is deterministic. This module changes
variables in the slope measure itself. The other pin's explicit factor `1/a`
cancels the slope Jacobian `1/x`, producing `1/(1-y)` on `y < 1`.

All weights are arbitrary nonnegative measurable functions; infinite total
mass and infinite pointwise weights are permitted. The displayed density is a
chosen measurable representative, including its specified boundary values.
-/

namespace PGM
noncomputable section
open MeasureTheory Set
open scoped ENNReal

/-- The positive-slope weight, retaining the other random pin's `1/a` factor. -/
def kernelDiracSlopeWeight (F : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  (Ioi (0 : ℝ)).indicator (fun a => F a / ENNReal.ofReal a)

/-- An explicit representative of the endpoint density after slope integration. -/
def kernelDiracShortDensity (x : ℝ) (F : ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  (Iio (1 : ℝ)).indicator (fun y => F ((1 - y) / x) / ENNReal.ofReal (1 - y))

/-- The designated gap is still a Dirac endpoint at each fixed slope. -/
theorem kernel_dirac_designated_endpoint (a x : ℝ) :
    (Measure.dirac x).map (fun t : ℝ => 1 - a * t) = Measure.dirac (1 - a * x) :=
  Measure.map_dirac' (by fun_prop) x

theorem measurable_kernelDiracSlopeWeight {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (kernelDiracSlopeWeight F) := by
  unfold kernelDiracSlopeWeight
  apply Measurable.indicator _ measurableSet_Ioi
  fun_prop

theorem measurable_kernelDiracShortDensity (x : ℝ) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (kernelDiracShortDensity x F) := by
  unfold kernelDiracShortDensity
  apply Measurable.indicator _ measurableSet_Iio
  fun_prop

/-- Pointwise cancellation inside the explicit affine density formula. The
coefficient is finite, so this also covers `F((1-y)/x) = ∞`. -/
theorem kernel_dirac_short_jacobian {x : ℝ} (hx : 0 < x) (F : ℝ → ℝ≥0∞) (y : ℝ) :
    ENNReal.ofReal |(-x)⁻¹| * kernelDiracSlopeWeight F ((y - 1) / (-x)) =
      kernelDiracShortDensity x F y := by
  have hi : (y - 1) / (-x) = (1 - y) / x := by field_simp; ring
  have hc : |(-x)⁻¹| = x⁻¹ := by
    rw [inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hx)]
  rw [hi, hc]
  by_cases hy : y < 1
  · have ht : 0 < (1 - y) / x := div_pos (sub_pos.mpr hy) hx
    have htI : (1 - y) / x ∈ Ioi (0 : ℝ) := ht
    have hyI : y ∈ Iio (1 : ℝ) := hy
    simp only [kernelDiracSlopeWeight, kernelDiracShortDensity,
      indicator_of_mem htI, indicator_of_mem hyI]
    rw [div_eq_mul_inv (F ((1 - y) / x)) (ENNReal.ofReal ((1 - y) / x)),
      div_eq_mul_inv (F ((1 - y) / x)) (ENNReal.ofReal (1 - y)), ← ENNReal.ofReal_inv_of_pos ht,
      ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hy)]
    calc ENNReal.ofReal x⁻¹ * (F ((1 - y) / x) * ENNReal.ofReal ((1 - y) / x)⁻¹) =
          F ((1 - y) / x) * (ENNReal.ofReal x⁻¹ * ENNReal.ofReal ((1 - y) / x)⁻¹) := by ac_rfl
         _ = F ((1 - y) / x) * ENNReal.ofReal (x⁻¹ * ((1 - y) / x)⁻¹) := by
           rw [ENNReal.ofReal_mul (inv_nonneg.mpr hx.le)]
         _ = F ((1 - y) / x) * ENNReal.ofReal (1 - y)⁻¹ := by
           congr 2
           field_simp
  · have ht : ¬ 0 < (1 - y) / x := by
      have hnonpos : (1 - y) / x ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hx.le
      exact not_lt_of_ge hnonpos
    have htI : (1 - y) / x ∉ Ioi (0 : ℝ) := ht
    have hyI : y ∉ Iio (1 : ℝ) := hy
    simp only [kernelDiracSlopeWeight, kernelDiracShortDensity,
      indicator_of_notMem htI, indicator_of_notMem hyI, mul_zero]

/-- Actual measure-level change of variables for the deterministic endpoint,
after integrating over all positive slopes with the retained `1/a` weight. -/
theorem kernel_dirac_short_map_density {x : ℝ} (hx : 0 < x) {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    ((volume : Measure ℝ).withDensity (kernelDiracSlopeWeight F)).map (fun a => 1 - a * x) =
      volume.withDensity (kernelDiracShortDensity x F) := by
  have hmap : Measurable (fun a : ℝ => 1 - a * x) := by fun_prop
  have hW := measurable_kernelDiracSlopeWeight hF
  have hD := measurable_kernelDiracShortDensity x hF
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  have hφmap : Measurable (fun a : ℝ => φ (1 - a * x)) := hφ.comp hmap
  rw [lintegral_map hφ hmap, lintegral_withDensity_eq_lintegral_mul _ hW hφmap,
    lintegral_withDensity_eq_lintegral_mul _ hD hφ]
  simp only [Pi.mul_apply]
  have hm : Measurable (fun a : ℝ => kernelDiracSlopeWeight F a * φ (1 - a * x)) := hW.mul hφmap
  rw [kernel_lintegral_affine_inverse (neg_ne_zero.mpr (ne_of_gt hx)) 1 hm]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  have he : 1 - ((y - 1) / (-x)) * x = y := by field_simp; ring
  rw [he, ← mul_assoc, kernel_dirac_short_jacobian hx F y]

/-- Equivalent half-axis formulation: source slopes are positive and target
endpoints are strictly below one. -/
theorem kernel_dirac_short_map_restrict {x : ℝ} (hx : 0 < x) {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (((volume : Measure ℝ).restrict (Ioi 0)).withDensity
      (fun a => F a / ENNReal.ofReal a)).map (fun a => 1 - a * x) =
      (volume.restrict (Iio 1)).withDensity
        (fun y => F ((1 - y) / x) / ENNReal.ofReal (1 - y)) := by
  simpa only [kernelDiracSlopeWeight, kernelDiracShortDensity, withDensity_indicator
    measurableSet_Ioi, withDensity_indicator measurableSet_Iio] using
      kernel_dirac_short_map_density hx hF

/-- Mixing the actual designated-gap Dirac endpoints over positive slopes
produces the explicit density. No density for a fixed-slope Dirac is asserted. -/
theorem kernel_dirac_short_mixture {x : ℝ} (hx : 0 < x) {F : ℝ → ℝ≥0∞}
    (hF : Measurable F) :
    (((volume : Measure ℝ).restrict (Ioi 0)).withDensity (fun a => F a / ENNReal.ofReal a)).bind
      (fun a => (Measure.dirac x).map (fun t : ℝ => 1 - a * t)) =
        volume.withDensity (kernelDiracShortDensity x F) := by
  simp_rw [kernel_dirac_designated_endpoint]
  rw [Measure.bind_dirac_eq_map _ (by fun_prop), ← withDensity_indicator measurableSet_Ioi]
  exact kernel_dirac_short_map_density hx hF

/-- The same change of variables against any nonnegative measurable endpoint
test, with no finite-mass hypothesis. -/
theorem kernel_dirac_short_lintegral {x : ℝ} (hx : 0 < x) {F φ : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hφ : Measurable φ) :
    (∫⁻ a in Ioi (0 : ℝ), (F a / ENNReal.ofReal a) * φ (1 - a * x)) =
      ∫⁻ y in Iio (1 : ℝ), (F ((1 - y) / x) / ENNReal.ofReal (1 - y)) * φ y := by
  have h := congrArg (fun μ : Measure ℝ => ∫⁻ y, φ y ∂μ) (kernel_dirac_short_map_restrict hx hF)
  have hmap : Measurable (fun a : ℝ => 1 - a * x) := by fun_prop
  have hφmap : Measurable (fun a : ℝ => φ (1 - a * x)) := hφ.comp hmap
  have hW : Measurable (fun a : ℝ => F a / ENNReal.ofReal a) := by fun_prop
  have hD : Measurable (fun y : ℝ => F ((1 - y) / x) / ENNReal.ofReal (1 - y)) := by fun_prop
  rw [lintegral_map hφ hmap, lintegral_withDensity_eq_lintegral_mul _ hW hφmap,
    lintegral_withDensity_eq_lintegral_mul _ hD hφ] at h
  exact h

theorem kernel_dirac_short_density_of_lt {x y : ℝ} {F : ℝ → ℝ≥0∞} (hy : y < 1) :
    kernelDiracShortDensity x F y = F ((1 - y) / x) / ENNReal.ofReal (1 - y) :=
  indicator_of_mem (s := Iio 1) hy _

theorem kernel_dirac_short_density_of_ge {x y : ℝ} {F : ℝ → ℝ≥0∞} (hy : 1 ≤ y) :
    kernelDiracShortDensity x F y = 0 := indicator_of_notMem (s := Iio 1) (not_lt.mpr hy) _

/-- The canonical lower-endpoint value has `1/(w+1)`, with no exposed `1/x`
singularity. Dependence on `x` remains inside the original slope weight `F`. -/
theorem kernel_dirac_short_density_at_lower {x w : ℝ} (hw : 0 < w) (F : ℝ → ℝ≥0∞) :
    kernelDiracShortDensity x F (-w) = F ((w + 1) / x) / ENNReal.ofReal (w + 1) := by
  rw [kernel_dirac_short_density_of_lt (by linarith : -w < 1)]
  congr 2 <;> ring

/-- A bounded remaining slope weight gives a lower-endpoint bound uniform in
the designated gap `x > 0`. -/
theorem kernel_dirac_short_density_at_lower_le {x w : ℝ} (hx : 0 < x) (hw : 0 < w)
    {F : ℝ → ℝ≥0∞} {B : ℝ≥0∞} (hF : ∀ a > 0, F a ≤ B) :
    kernelDiracShortDensity x F (-w) ≤ B / ENNReal.ofReal (w + 1) := by
  rw [kernel_dirac_short_density_at_lower hw F]
  gcongr
  exact hF _ (div_pos (by linarith) hx)

/-- The short downward bridge is absent from any slope range below its exact
root. In particular, `A = 2` gives the near-critical support separation. -/
theorem kernel_dirac_short_density_at_lower_eq_zero {x w A : ℝ} (hx : 0 < x) (hw : 0 < w)
    (hsep : A * x < w + 1) {F : ℝ → ℝ≥0∞} (hF : ∀ a, A < a → F a = 0) :
    kernelDiracShortDensity x F (-w) = 0 := by
  rw [kernel_dirac_short_density_at_lower hw F, hF _ ((lt_div_iff₀ hx).mpr hsep), ENNReal.zero_div]

/-- At zero designated gap the endpoint stays at one, so its actual pushforward
has no mass below one. The positive-gap density formula is not used at `x=0`. -/
theorem kernel_dirac_zero_gap_below_one (μ : Measure ℝ) :
    (μ.map (fun a : ℝ => 1 - a * (0 : ℝ))).restrict (Iio 1) = 0 := by
  apply Measure.restrict_eq_zero.mpr
  rw [Measure.map_apply (by fun_prop) measurableSet_Iio]
  simp

end
end PGM
