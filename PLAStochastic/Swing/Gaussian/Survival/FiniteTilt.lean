import PLAStochastic.Swing.Gaussian.HalfLine.ExponentialStopping
import Mathlib.MeasureTheory.Integral.Pi

/-! Exact finite Gaussian changes of drift from their actual densities. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

def gaussianTiltWeight (a z : ℝ) : ℝ := Real.exp (a*z-a^2/2)

theorem gaussianTiltWeight_measurable (a : ℝ) : Measurable (gaussianTiltWeight a) := by
  unfold gaussianTiltWeight
  fun_prop

theorem gaussianTiltWeight_integrable (a : ℝ) : Integrable (gaussianTiltWeight a) (gaussianReal 0 1) := by
  have hi := (integrable_exp_mul_gaussianReal (μ := 0) (v := 1) a).const_mul (Real.exp (-a^2/2))
  apply hi.congr
  exact ae_of_all _ (fun z => by dsimp [gaussianTiltWeight]; rw [← Real.exp_add]; congr 1; ring)

theorem gaussianPDFReal_tilt (a z : ℝ) :
    gaussianPDFReal a 1 z = gaussianPDFReal 0 1 z * gaussianTiltWeight a z := by
  simp only [gaussianPDFReal, gaussianTiltWeight, NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- A one-dimensional Gaussian drift change, without an assumed likelihood identity. -/
theorem gaussianReal_withDensity_tilt (a : ℝ) :
    (gaussianReal 0 1).withDensity (fun z => ENNReal.ofReal (gaussianTiltWeight a z)) = gaussianReal a 1 := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero), gaussianReal_of_var_ne_zero a (one_ne_zero),
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (gaussianTiltWeight_measurable a).ennreal_ofReal]
  congr 1
  funext z
  simp only [Pi.mul_apply, gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  exact congrArg ENNReal.ofReal (gaussianPDFReal_tilt a z).symm

theorem gaussianPi_withDensity_tilt (a : ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).withDensity
      (fun z => ENNReal.ofReal (∏ i : Fin n, gaussianTiltWeight a (z i))) =
      Measure.pi (fun _ : Fin n => gaussianReal a 1) := by
  apply (Measure.pi_eq _).symm
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hi : Integrable (fun z : Fin n → ℝ => ∏ i, gaussianTiltWeight a (z i))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    Integrable.fintype_prod (fun _ => gaussianTiltWeight_integrable a)
  rw [← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (ae_of_all _ (fun z => Finset.prod_nonneg (fun _ _ => (Real.exp_pos _).le))),
    Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  have hpos (i : Fin n) : 0 ≤ ∫ z in s i, gaussianTiltWeight a z ∂gaussianReal 0 1 :=
    integral_nonneg (fun z => (Real.exp_pos _).le)
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hpos i)]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofReal_integral_eq_lintegral_ofReal (gaussianTiltWeight_integrable a).integrableOn
    (ae_of_all _ (fun _ => (Real.exp_pos _).le))]
  rw [← withDensity_apply _ (hs i), gaussianReal_withDensity_tilt]


theorem gaussianTiltWeight_prod (a : ℝ) {n : ℕ} (z : Fin n → ℝ) :
    (∏ i, gaussianTiltWeight a (z i)) = Real.exp (a*(∑ i, z i)-(n : ℝ)*a^2/2) := by
  simp only [gaussianTiltWeight, ← Real.exp_sum]
  congr 1
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem gaussianPi_map_add (a : ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin n => gaussianReal 0 1)).map (fun z i => z i+a) =
      Measure.pi (fun _ : Fin n => gaussianReal a 1) := by
  have (i : Fin n) : IsProbabilityMeasure ((gaussianReal 0 1).map (fun z => z+a)) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [Measure.pi_map_pi (f := fun _ : Fin n => fun z : ℝ => z+a)
    (fun _ => (measurable_id.add_const a).aemeasurable)]
  simp only [gaussianReal_map_add_const, zero_add]

/-- Finite-coordinate likelihood identity for every measurable test function. -/
theorem gaussianPi_integral_translate {n : ℕ} (a : ℝ) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) :
    (∫ z, f (fun i => z i+a) ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) =
    ∫ z, Real.exp (a*(∑ i, z i)-(n : ℝ)*a^2/2)*f z
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hl : HasLaw (fun z : Fin n → ℝ => fun i => z i+a)
      (Measure.pi (fun _ : Fin n => gaussianReal a 1))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) :=
    ⟨(measurable_pi_lambda _ (fun i => (measurable_pi_apply i).add_const a)).aemeasurable,
      gaussianPi_map_add a n⟩
  have he := hl.integral_comp hf.aestronglyMeasurable
  dsimp only [Function.comp_def] at he
  rw [he, ← gaussianPi_withDensity_tilt]
  rw [integral_withDensity_eq_integral_toReal_smul
    (by unfold gaussianTiltWeight; fun_prop) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [gaussianTiltWeight_prod, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul])

end SwingRepair
