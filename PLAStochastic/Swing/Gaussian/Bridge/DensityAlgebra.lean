import PLAStochastic.Swing.Gaussian.Bridge.EndpointIndependence

/-! Density algebra and nonnegative integral changes of variables for a Gaussian bridge. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem gaussianPi_lintegral_translate {n : ℕ} (a : ℝ) {f : (Fin n → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ z, f (fun i => z i+a) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
    ∫⁻ z, ENNReal.ofReal (Real.exp (a*(∑ i, z i)-(n : ℝ)*a^2/2))*f z
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hl : HasLaw (fun z : Fin n → ℝ => fun i => z i+a)
      (Measure.pi (fun _ : Fin n => gaussianReal a 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    ⟨(measurable_pi_lambda _ (fun i => (measurable_pi_apply i).add_const a)).aemeasurable,
      gaussianPi_map_add a n⟩
  rw [hl.lintegral_comp hf.aemeasurable, ← gaussianPi_withDensity_tilt,
    lintegral_withDensity_eq_lintegral_mul _ (by unfold gaussianTiltWeight; fun_prop) hf]
  simp only [Pi.mul_apply, gaussianTiltWeight_prod]

theorem gaussianReal_lintegral_translate {v : ℝ≥0} (hv : v ≠ 0) (s : ℝ)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ r, f (s+r) ∂gaussianReal 0 v) = ∫⁻ y, gaussianPDF 0 v (y-s)*f y := by
  rw [gaussianReal_of_var_ne_zero 0 hv,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) (by fun_prop)]
  rw [← lintegral_add_right_eq_self (fun y => gaussianPDF 0 v (y-s)*f y) s]
  simp only [Pi.mul_apply, add_sub_cancel_right]
  congr 1
  funext r
  rw [add_comm r s]

theorem gaussianPDFReal_zero_mean_factor (v : ℝ≥0) (y : ℝ) :
    gaussianPDFReal 0 v y = gaussianPDFReal 0 v 0 * Real.exp (-y^2/(2*v)) := by
  simp only [gaussianPDFReal, sub_zero, zero_pow (by norm_num : 2 ≠ 0), neg_zero,
    zero_div, Real.exp_zero, mul_one]

/-- Completing the actual Gaussian densities separates endpoint and bridge prefix. -/
theorem gaussianBridge_density_factor (m : ℕ) {r : ℝ≥0} (hr : 0 < r) (s y : ℝ) :
    Real.exp ((-y/((m : ℝ)+r))*s-(m : ℝ)*(-y/((m : ℝ)+r))^2/2)*
      gaussianPDFReal 0 r (y-(s+(m : ℝ)*y/((m : ℝ)+r))) =
    gaussianPDFReal 0 ((m : ℝ≥0)+r) y *
      (gaussianPDFReal 0 r (-s)/gaussianPDFReal 0 ((m : ℝ≥0)+r) 0) := by
  have hrR : (0 : ℝ) < r := hr
  have ht : (0 : ℝ) < (m : ℝ)+r := by positivity
  have hp : gaussianPDFReal 0 ((m : ℝ≥0)+r) 0 ≠ 0 :=
    (gaussianPDFReal_pos 0 ((m : ℝ≥0)+r) 0 (by positivity)).ne'
  rw [gaussianPDFReal_zero_mean_factor r (y-(s+(m : ℝ)*y/((m : ℝ)+r))),
    gaussianPDFReal_zero_mean_factor ((m : ℝ≥0)+r) y,
    gaussianPDFReal_zero_mean_factor r (-s)]
  simp only [NNReal.coe_add, NNReal.coe_natCast]
  have he : (-y/((m : ℝ)+r))*s-(m : ℝ)*(-y/((m : ℝ)+r))^2/2 +
      (-(y-(s+(m : ℝ)*y/((m : ℝ)+r)))^2/(2*r)) =
      -y^2/(2*((m : ℝ)+r)) + (-(-s)^2/(2*r)) := by
    field_simp
    ring
  calc
    _ = gaussianPDFReal 0 r 0 * Real.exp
        ((-y/((m : ℝ)+r))*s-(m : ℝ)*(-y/((m : ℝ)+r))^2/2 +
          (-(y-(s+(m : ℝ)*y/((m : ℝ)+r)))^2/(2*r))) := by
      rw [Real.exp_add]
      ring
    _ = gaussianPDFReal 0 r 0 *
        (Real.exp (-y^2/(2*((m : ℝ)+r)))*Real.exp (-(-s)^2/(2*r))) := by
      rw [he, Real.exp_add]
    _ = _ := by field_simp

end SwingRepair
